open Utils
open Containers

type clause_t = int list
type cnf_t = clause_t list
type value_t = TRUE | FALSE | UNDEF
type variable_t = { value : value_t; antecender : clause_t option }
type assignment_t = variable_t CCPersistentArray.t
type answer_t = UNSAT of cnf_t | SAT of bool list

let verify_cnf clauses =
  let vars = List.flatten clauses |> List.map abs |> Intset.of_list in
  let expected = 1 -- Intset.max_elt vars in
  List.equal ( = ) (Intset.to_list vars) expected
  && not (Intset.exists (fun x -> x = 0) vars)

let rec opt_unit_acc assignment clause acc =
  match clause with
  | [] -> acc
  | v :: t -> (
      let id = abs v in
      let variable = CCPersistentArray.get assignment id in
      let literal =
        match variable.value with
        | TRUE -> if v < 0 then FALSE else TRUE
        | UNDEF -> UNDEF
        | FALSE -> if v < 0 then TRUE else FALSE
      in
      match literal with
      | TRUE -> (0, 0)
      | FALSE -> opt_unit_acc assignment t acc
      | UNDEF ->
          let count, _ = acc in
          opt_unit_acc assignment t (count + 1, v))

let opt_unit assignment clause =
  let opt_id = opt_unit_acc assignment clause (0, 0) in
  match opt_id with 0, _ -> None | 1, l -> Some (l, clause) | _, _ -> None

let resolve_unit_clause_if_any clauses assignment =
  let unit_clause = List.find_map (opt_unit assignment) clauses in
  match unit_clause with
  | None -> None
  | Some (l, clause) ->
      let new_literal =
        { value = (if l > 0 then TRUE else FALSE); antecender = Some clause }
      in
      Some (CCPersistentArray.set assignment (abs l) new_literal)

let rec is_conflict assignment clause =
  match clause with
  | [] -> true
  | v :: t -> (
      let id = abs v in
      let variable = CCPersistentArray.get assignment id in
      let literal =
        match variable.value with
        | TRUE -> if v < 0 then FALSE else TRUE
        | UNDEF -> UNDEF
        | FALSE -> if v < 0 then TRUE else FALSE
      in
      match literal with
      | FALSE -> is_conflict assignment t
      | TRUE -> false
      | UNDEF -> false)

let rec unit_propagation clauses assignment =
  let conflict_clause = List.find_opt (is_conflict assignment) clauses in
  match conflict_clause with
  | Some conflict -> (assignment, Some conflict)
  | None -> (
      let new_assignment = resolve_unit_clause_if_any clauses assignment in
      match new_assignment with
      | None -> (assignment, None)
      | Some a -> unit_propagation clauses a)

let init_assignment clauses =
  let vars = List.flatten clauses |> List.map (fun x -> abs x) in
  let vars_cnt = 1 + List.fold_left max 0 vars in
  CCPersistentArray.make vars_cnt { value = UNDEF; antecender = None }

let conflict_analyzist conflict assignment =
  let antecendant_clauses =
    List.map
      (fun lit ->
        let variable = CCPersistentArray.get assignment (abs lit) in
        variable.antecender)
      conflict
  in
  let literals =
    List.filter_map Fun.id antecendant_clauses |> List.flatten |> Intset.of_list
  in
  List.fold_left
    (fun clause lit -> Intset.remove lit clause |> Intset.remove (-lit))
    literals conflict
  |> Intset.to_list

let not_always_true clause =
  let vars = List.map abs clause |> List.sort_uniq ~cmp:compare in
  List.length clause = List.length vars

let preprocess clauses =
  clauses
  |> List.map (fun c -> List.sort_uniq ~cmp:compare c)
  |> List.filter not_always_true
  |> List.sort_uniq ~cmp:Stdlib.compare

let rec get_undef_var_rec assignment i n =
  if i = n then None
  else
    let var = CCPersistentArray.get assignment i in
    match var.value with
    | UNDEF -> Some i
    | _ -> get_undef_var_rec assignment (i + 1) n

let get_undef_var assignment =
  let n = CCPersistentArray.length assignment in
  get_undef_var_rec assignment 1 n

let assignment_to_bool_list assignment =
  let omit0 = CCPersistentArray.to_list assignment |> List.tail_opt in
  match omit0 with
  | None -> raise (Failure "could not convert to bool lists")
  | Some t ->
      List.map
        (fun v ->
          match v.value with
          | TRUE -> true
          | FALSE -> false
          | UNDEF -> raise (Failure "could not convert to bool lists"))
        t

let is_unsatisfiable assignment clause =
  List.for_all
    (fun l ->
      match (CCPersistentArray.get assignment (abs l)).value with
      | FALSE -> if l > 0 then true else false
      | TRUE -> if l < 0 then true else false
      | UNDEF -> false)
    clause

let exists_unsat clauses assignment =
  List.exists (is_unsatisfiable assignment) clauses

let rec cdcl_bf clauses assignment =
  if exists_unsat clauses assignment then UNSAT clauses
  else
    let propagated, conflict = unit_propagation clauses assignment in
    match conflict with
    | Some c ->
        let new_clause = conflict_analyzist c propagated in
        if List.is_empty new_clause then UNSAT clauses
        else UNSAT (new_clause :: clauses)
    | None -> (
        let undef_var_opt = get_undef_var propagated in
        match undef_var_opt with
        | None -> SAT (assignment_to_bool_list assignment)
        | Some undef_var -> (
            let assume_true =
              CCPersistentArray.set propagated undef_var
                { value = TRUE; antecender = None }
            in
            match cdcl_bf clauses assume_true with
            | SAT a -> SAT a
            | UNSAT cnf ->
                let assume_false =
                  CCPersistentArray.set propagated undef_var
                    { value = FALSE; antecender = None }
                in
                cdcl_bf cnf assume_false))

let cdcl clauses =
  if not (verify_cnf clauses) then raise (Failure "this is not cnf");
  let simplified_clauses = preprocess clauses in
  let init_assignment = init_assignment simplified_clauses in
  cdcl_bf simplified_clauses init_assignment

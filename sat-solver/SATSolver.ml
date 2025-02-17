open Utils
open Containers
module Assign = CCPersistentArray

type clause_t = int list
type cnf_t = clause_t list
type value_t = TRUE | FALSE | UNDEF
type variable_t = { value : value_t; antecender : clause_t option }
type assignment_t = variable_t Assign.t
type answer_t = UNSAT of int * cnf_t | SAT of bool list

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
      let variable = Assign.get assignment id in
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

let rec is_conflict assignment clause =
  match clause with
  | [] -> true
  | v :: t -> (
      let id = abs v in
      let variable = Assign.get assignment id in
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

let rec unit_propagation possible_clauses clause_by_var assignment =
  (* let _ =
    print_string "ok";
    print_int (Seq.length possible_clauses);
    print_endline ""
  in *)
  match possible_clauses () with
  | Seq.Nil -> (assignment, None)
  | Seq.Cons (cur_clause, t) -> (
      if is_conflict assignment cur_clause then (assignment, Some cur_clause)
      else
        let unit_opt = opt_unit assignment cur_clause in
        match unit_opt with
        | None -> unit_propagation t clause_by_var assignment
        | Some (l, clause) ->
            let new_literal =
              {
                value = (if l > 0 then TRUE else FALSE);
                antecender = Some clause;
              }
            in
            let id = abs l in
            let new_assignment = Assign.set assignment id new_literal in
            let new_possible = clause_by_var.(id) in
            unit_propagation
              (Seq.append new_possible possible_clauses)
              clause_by_var new_assignment)

let init_assignment clauses =
  let vars = List.flatten clauses |> List.map (fun x -> abs x) in
  let vars_cnt = 1 + List.fold_left max 0 vars in
  Assign.make vars_cnt { value = UNDEF; antecender = None }

let conflict_analyzist conflict assignment =
  let antecendant_clauses =
    List.map
      (fun lit ->
        let variable = Assign.get assignment (abs lit) in
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
    let var = Assign.get assignment i in
    match var.value with
    | UNDEF -> Some i
    | _ -> get_undef_var_rec assignment (i + 1) n

let get_undef_var assignment =
  let n = Assign.length assignment in
  get_undef_var_rec assignment 1 n

let assignment_to_bool_list assignment =
  (* let _ =
    CCPersistentArray.length assignment |> print_int;
    print_endline ""
  in *)
  let omit0 = Assign.to_list assignment |> List.tail_opt in
  match omit0 with
  | None -> raise (Failure "could not convert to bool lists")
  | Some t ->
      List.map
        (fun v ->
          match v.value with TRUE -> true | FALSE -> false | UNDEF -> false)
        t

let is_unsatisfiable assignment clause =
  List.for_all
    (fun l ->
      match (Assign.get assignment (abs l)).value with
      | FALSE -> if l > 0 then true else false
      | TRUE -> if l < 0 then true else false
      | UNDEF -> false)
    clause

let is_satisfiable assignment clause =
  List.for_all
    (fun l ->
      match (Assign.get assignment (abs l)).value with
      | FALSE -> if l < 0 then true else false
      | TRUE -> if l > 0 then true else false
      | UNDEF -> false)
    clause

let get_clause_by_var assignment clauses =
  let max_var = List.flatten clauses |> List.map abs |> List.fold_left max 0 in
  let arr = Array.make (max_var + 1) Seq.empty in
  List.iter
    (fun clause ->
      if is_satisfiable assignment clause then print_endline "found sat"
      else
        List.iter
          (fun l ->
            let id = abs l in
            arr.(id) <- Seq.cons clause arr.(id))
          clause)
    clauses;
  arr

let counter = ref 0
let max_clause_cnt = int_of_float 1e6
let max_clause_sz = 10

let add_clause_to_clause_by_var clause clause_by_var =
  List.iter
    (fun l ->
      let id = abs l in
      clause_by_var.(id) <- Seq.cons clause clause_by_var.(id))
    clause

let add_clause (clauses_added, extra_clauses) clause_by_var clause =
  if List.is_empty clause then (clauses_added, extra_clauses)
  else if clauses_added > max_clause_cnt || greater_than clause max_clause_sz
  then
    ( (*maybe some heuristic to remove old*)
      clauses_added,
      extra_clauses )
  else (
    add_clause_to_clause_by_var clause clause_by_var;
    (clauses_added, clause :: extra_clauses))

let get_undef_clauses clauses assignment =
  List.filter (fun clause -> not (is_satisfiable assignment clause)) clauses

let rec cdcl_bf extra_clauses assignment possible_unit clause_by_var =
  (* if exists_unsat clauses assignment then UNSAT clauses
  else *)
  (* let stat = Gc.quick_stat () in
  let ab = stat.minor_words +. stat.major_words -. stat.promoted_words in *)
  counter := !counter + 1;
  if !counter mod 1000 = 0 then (
    print_int !counter;
    print_endline " unit propagation finished, undef vars: ";
    print_int
      (Assign.fold_left
         (fun acc e -> match e.value with UNDEF -> acc + 1 | _ -> acc)
         0 assignment);
    print_endline "");

  let propagated, conflict =
    unit_propagation possible_unit clause_by_var assignment
  in
  match conflict with
  | Some c ->
      let new_clause = conflict_analyzist c propagated in
      let cnt, clauses = add_clause extra_clauses clause_by_var new_clause in
      UNSAT (cnt, clauses)
  | None -> (
      let undef_var_opt = get_undef_var propagated in
      match undef_var_opt with
      | None -> SAT (assignment_to_bool_list propagated)
      | Some undef_var -> (
          let curc, _ = extra_clauses in
          let a_true =
            Assign.set propagated undef_var { value = TRUE; antecender = None }
          in

          match
            cdcl_bf extra_clauses a_true clause_by_var.(undef_var) clause_by_var
          with
          | SAT a -> SAT a
          | UNSAT (clause_added, clauses) ->
              let a_false =
                Assign.set propagated undef_var
                  { value = FALSE; antecender = None }
              in
              let new_possible =
                Seq.append
                  (List.take (clause_added - curc) clauses |> List.to_seq)
                  clause_by_var.(undef_var)
              in

              cdcl_bf (clause_added, clauses) a_false new_possible clause_by_var
          ))

let cdcl clauses =
  let _ = print_endline "start verifying " in
  if not (verify_cnf clauses) then raise (Failure "this is not cnf");
  print_endline "start solving ";
  let simplified_clauses = preprocess clauses in
  print_endline "preprocess finished";
  let init_assignment = init_assignment simplified_clauses in
  print_endline "got init assignment";
  let clause_by_var = get_clause_by_var init_assignment simplified_clauses in
  print_endline "get claues by var";
  let propagated, conflict =
    unit_propagation
      (List.to_seq simplified_clauses)
      clause_by_var init_assignment
  in
  match conflict with
  | Some _ -> UNSAT (0, [])
  | None ->
      let undef_clauses = get_undef_clauses simplified_clauses propagated in
      let clause_by_var_upd = get_clause_by_var propagated simplified_clauses in
      print_endline "get clauses by var updated";
      print_int (List.length undef_clauses);
      print_newline ();
      print_endline "start brootforce";
      cdcl_bf (0, []) propagated (List.to_seq []) clause_by_var_upd

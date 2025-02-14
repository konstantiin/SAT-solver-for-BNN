open Utils

let scalar_mul v1 v2 =
  List.combine v1 v2 |> List.fold_left (fun acc (e1, e2) -> acc + (e1 * e2)) 0

let linear weights x = List.map (scalar_mul x) weights
let sign x = List.map (fun el -> if el >= 0 then 1 else -1) x

type component_t = Linear of int * int
type config_t = { weights : int list; extra_vars : int list }
type train_data_t = int list * int

let rec alloc_extra cfg n =
  if n = 0 then cfg
  else
    let n_var =
      1
      +
      match cfg.extra_vars with
      | [] -> ( match cfg.weights with [] -> 0 | hw :: _ -> hw)
      | he :: _ -> ( match cfg.weights with [] -> he | hw :: _ -> max hw he)
    in
    alloc_extra
      { weights = cfg.weights; extra_vars = n_var :: cfg.extra_vars }
      (n - 1)

let alloc_weights cfg n =
  match cfg.extra_vars with
  | [] ->
      let last = match cfg.weights with [] -> 0 | h :: _ -> h in
      {
        weights = cfg.weights @ (last + 1 -- (last + n));
        extra_vars = cfg.extra_vars;
      }
  | _ -> raise (Failure "weights should be assigned before extra variables")

let alloc_extra_one cfg =
  let cfg = alloc_extra cfg 1 in
  (List.hd cfg.extra_vars, cfg)

(* let rec unit_propagation cnf =
  (* let _ =
    print_endline "_";
    print_int (List.length cnf);
    print_endline ""
  in *)
  let units = find_arr_of_1 cnf in
  if units = [] then cnf
  else
    (* let i = ref 0 in *)
    let resolved =
      List.filter_map
        (fun clause ->
          (* let _ =
                print_int !i
                print_endline " clause resolving";
                i := !i + 1
              in *)
          let is_true = is_intersecting clause units in
          if is_true then None
          else Some (remove_intersection clause (List.map (fun x -> -x) units)))
        cnf
    in
    unit_propagation resolved *)

let get_next (cfg, a, cnf) x =
  let b0, cfg = alloc_extra_one cfg in
  let b1, cfg = alloc_extra_one cfg in
  let b = b0 :: x :: [ b1 ] in
  let m1 = List.length a - 2 in
  let m2 = List.length b - 2 in
  let m = m1 + m2 in
  let cfg = alloc_extra cfg (m + 2) in
  let r = List.take (m + 2) cfg.extra_vars in
  let range_0_m1 = 0 -- m1 in
  let range_0_m2 = 0 -- m2 in
  let cnf =
    [ b0 ] :: [ List.hd r ] :: [ -b1 ] :: [ -List.nth r (m + 1) ] :: cnf
  in
  let a_arr = Array.of_list a in
  let b_arr = Array.of_list b in
  let r_arr = Array.of_list r in
  let new_cnf =
    List.fold_left
      (fun cnf_a i ->
        List.fold_left
          (fun cnf_b j ->
            let k = i + j in
            if k > m then cnf_b
            else
              [ -a_arr.(i); -b_arr.(j); r_arr.(k) ]
              :: [ a_arr.(i + 1); b_arr.(j + 1); -r_arr.(k + 1) ]
              :: cnf_b)
          cnf_a range_0_m2)
      cnf range_0_m1
  in
  (cfg, r, new_cnf)

let at_least_k input_var k cnf cfg =
  let init0, cfg = alloc_extra_one cfg in
  let init1, cfg = alloc_extra_one cfg in
  let init = init0 :: List.hd input_var :: [ init1 ] in
  let cnf = [ init0 ] :: [ -init1 ] :: cnf in
  let result_cfg, last_vec, result_cnf =
    List.fold_left get_next (cfg, init, cnf) (List.tl input_var)
  in
  ((result_cnf, result_cfg), List.nth last_vec k)

let mul_to_cnf (cnf, cfg) (v1, v2) =
  let e, cfg = alloc_extra_one cfg in
  let add_is_neg =
    [ v1; -v2; -e ] :: [ -v1; v2; -e ] :: [ v1; v2; e ] :: [ -v1; -v2; e ]
    :: cnf
  in
  ((add_is_neg, cfg), e)

let scalar_mul_to_cnf (cnf, cfg) (vec1, vec2) =
  (* let _ =
    print_int (List.length vec1);
    print_endline "";
    print_int (List.length vec2);
    print_endline ""
  in *)
  let (cnf, cfg), res_vars =
    List.fold_left_map mul_to_cnf (cnf, cfg) (List.combine vec1 vec2)
  in
  let k_for_pos = (1 + List.length res_vars) / 2 in
  at_least_k res_vars k_for_pos cnf cfg

let linear_to_cnf (cnf, cfg, input) weights =
  let (cnf, cfg), res_vars =
    List.fold_left_map
      (fun acc line ->
        (* print_endline "line finished"; *)
        scalar_mul_to_cnf acc (input, line))
      (cnf, cfg) weights
  in
  (* print_endline "layer finished"; *)
  (cnf, cfg, res_vars)

let input_to_vars cnf cfg pixels =
  let (cnf, cfg), res =
    List.fold_left_map
      (fun (cnf, cfg) pix ->
        let var, cfg = alloc_extra_one cfg in
        (([ var * pix ] :: cnf, cfg), var))
      (cnf, cfg) pixels
  in
  (cnf, cfg, res)

let cnf_from_sample weights (cnf, cfg) sample =
  let input_p, output = sample in
  let cnf, cfg, input = input_to_vars cnf cfg input_p in
  let cnf = cnf in
  (* let _ = print_endline "linear to cnf started" in *)
  let cnf, cfg, last = List.fold_left linear_to_cnf (cnf, cfg, input) weights in
  let cnf =
    List.fold_left2
      (fun cnf label i ->
        if i = output then [ label ] :: cnf else [ -label ] :: cnf)
      cnf last
      (0 -- (List.length last - 1))
  in
  (cnf, cfg)

module type S = sig
  val s : component_t list
end

module Sequantial (Sequence : S) = struct
  let predictor_of_cnf_solution solution =
    let _, sequence =
      List.fold_left_map
        (fun solution_cur component ->
          match component with
          | Linear (n, m) ->
              let w_cnt = n * m in
              let weights =
                List.take w_cnt solution_cur
                |> List.map (fun b -> if b then 1 else -1)
                |> unflatten n m
              in
              (List.drop w_cnt solution, Fun.compose (linear weights) sign))
        solution Sequence.s
    in
    List.fold_left Fun.compose Fun.id sequence

  let get_cnf (train_batch : train_data_t list) =
    let cnf = [] in
    let cfg = { weights = []; extra_vars = [] } in
    let cfg, weights =
      List.fold_left_map
        (fun cfg layer ->
          match layer with
          | Linear (n, m) ->
              let w_cnt = n * m in
              let cfg = alloc_weights cfg w_cnt in
              let cur_weights =
                cfg.weights |> List.take w_cnt |> unflatten m n
              in
              (cfg, cur_weights))
        cfg Sequence.s
    in
    let _ = print_endline "weights allocated" in
    let bsz = List.length train_batch in
    let _, (cnf, _) =
      List.fold_left
        (fun (i, acc) s ->
          let _ =
            print_int i;
            print_string " out of ";
            print_int bsz;
            print_endline ""
          in
          (i + 1, cnf_from_sample weights acc s))
        (0, (cnf, cfg))
        train_batch
    in
    cnf
end

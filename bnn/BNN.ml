open Utils

let scalar_mul v1 v2 =
  (* let _ =
    print_int (List.length v1);
    print_string " ";
    print_int (List.length v2);
    print_endline ""
  in *)
  List.combine v1 v2 |> List.fold_left (fun acc (e1, e2) -> acc + (e1 * e2)) 0

let linear weights x = List.map (scalar_mul x) weights
let sign x = List.map (fun el -> if el >= 0 then 1 else -1) x

type component_t = Linear of int * int

type config_t = {
  weights : int list;
  extra_vars : int list;
  g_true : int;
  g_false : int;
}

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
      {
        weights = cfg.weights;
        extra_vars = n_var :: cfg.extra_vars;
        g_true = cfg.g_true;
        g_false = cfg.g_false;
      }
      (n - 1)

let alloc_weights cfg n =
  match cfg.extra_vars with
  | [ 2; 1 ] ->
      let last = match cfg.weights with [] -> 2 | h :: _ -> h in
      (* let _ =
        print_int last;
        print_endline ""
      in *)
      {
        weights =
          List.fold_left
            (fun acc w -> w :: acc)
            cfg.weights
            (last + 1 -- (last + n));
        extra_vars = cfg.extra_vars;
        g_true = cfg.g_true;
        g_false = cfg.g_false;
      }
  | _ ->
      raise
        (Failure
           "weights should be assigned before extra variables but after g_true \
            and g_false")

let alloc_extra_one cfg =
  let cfg = alloc_extra cfg 1 in
  (List.hd cfg.extra_vars, cfg)

let add_clauses cnf cfg clauses =
  List.fold_left
    (fun cnf clause ->
      let is_sat =
        List.exists (fun l -> l = cfg.g_true || -l = cfg.g_false) clause
      in
      if is_sat then cnf
      else Utils.remove_intersection clause [ -cfg.g_true; cfg.g_false ] :: cnf)
    cnf clauses

let get_next (cfg, a, cnf) x =
  (* let b0, cfg = alloc_extra_one cfg in *)
  (* let b1, cfg = alloc_extra_one cfg in *)
  let b = cfg.g_true :: x :: [ cfg.g_false ] in
  let m1 = List.length a - 2 in
  let m2 = List.length b - 2 in
  let m = m1 + m2 in
  let cfg = alloc_extra cfg m in
  let r = (cfg.g_true :: List.take m cfg.extra_vars) @ [ cfg.g_false ] in
  let range_0_m1 = 0 -- m1 in
  let range_0_m2 = 0 -- m2 in
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
              add_clauses cnf_b cfg
                [
                  [ -a_arr.(i); -b_arr.(j); r_arr.(k) ];
                  [ a_arr.(i + 1); b_arr.(j + 1); -r_arr.(k + 1) ];
                ])
          cnf_a range_0_m2)
      cnf range_0_m1
  in
  (cfg, r, new_cnf)

let at_least_k input_var k cnf cfg =
  let init = cfg.g_true :: List.hd input_var :: [ cfg.g_false ] in
  let result_cfg, last_vec, result_cnf =
    List.fold_left get_next (cfg, init, cnf) (List.tl input_var)
  in
  ((result_cnf, result_cfg), List.nth last_vec k)

let mul_to_cnf (cnf, cfg) (v1, v2) =
  let e, cfg = alloc_extra_one cfg in
  let add_is_neg =
    add_clauses cnf cfg
      [ [ v1; -v2; -e ]; [ -v1; v2; -e ]; [ v1; v2; e ]; [ -v1; -v2; e ] ]
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
        print_endline "line weights";
        print_endline (string_of_int_list line);
        print_endline "__________________|";
        scalar_mul_to_cnf acc (input, line))
      (cnf, cfg) weights
  in
  (cnf, cfg, res_vars)

let input_to_vars cfg features =
  List.map
    (fun f ->
      if f = 1 then cfg.g_true
      else if f = -1 then cfg.g_false
      else raise (Failure "social credit -100500"))
    features

let cnf_from_sample weights (cnf, cfg) sample =
  let input_p, output = sample in
  let input = input_to_vars cfg input_p in
  let _ =
    print_endline "input:";
    print_endline (string_of_int_list input);
    print_endline "_"
  in
  let cnf, cfg, last = List.fold_left linear_to_cnf (cnf, cfg, input) weights in
  let _ =
    print_endline (string_of_int_list last);
    print_endline "_^_"
  in
  let cnf =
    if List.length last <> 1 then raise (Failure "social credit -100500");
    add_clauses cnf cfg
      (if output = 1 then [ [ List.hd last ] ] else [ [ -List.hd last ] ])
  in
  (* let cnf =
    List.fold_left2
      (fun cnf label i ->
        add_clauses cnf cfg
          (if i = output then [ [ label ] ] else [ [ -label ] ]))
      cnf last
      (0 -- (List.length last - 1))
  in *)
  (cnf, cfg)

module type S = sig
  val s : component_t list
end

module Sequantial (Sequence : S) = struct
  let weights_cnt =
    List.fold_left
      (fun acc -> function Linear (n, m) -> acc + (n * m))
      0 Sequence.s

  let predictor_of_cnf_solution solution_r =
    (* let _ =
      print_int (List.length solution);
      print_endline
    in *)
    let solution = List.drop 2 solution_r in
    let _, sequence =
      List.fold_left_map
        (fun solution_cur component ->
          match component with
          | Linear (n, m) ->
              let w_cnt = n * m in
              let weights =
                List.take w_cnt solution_cur
                |> List.map (fun b -> if b then 1 else -1)
                |> unflatten m n
              in
              let _ =
                print_endline "weights";
                print_endline (string_of_int_list_list weights)
              in
              ( List.drop w_cnt solution_cur,
                fun x -> x |> linear weights |> sign ))
          (* (List.drop w_cnt solution, Fun.compose (linear weights) sign)) *)
        solution Sequence.s
    in
    List.fold_left Fun.compose Fun.id (List.rev sequence)

  let get_cnf (train_batch : train_data_t list) =
    let cnf = [ [ 1 ]; [ -2 ] ] in
    let cfg =
      { weights = []; extra_vars = [ 2; 1 ]; g_true = 1; g_false = 2 }
    in
    let cfg, weights =
      List.fold_left_map
        (fun cfg layer ->
          match layer with
          | Linear (n, m) ->
              let w_cnt = n * m in
              let cfg = alloc_weights cfg w_cnt in
              let cur_weights =
                cfg.weights |> List.take w_cnt |> List.rev |> unflatten m n
              in
              (cfg, cur_weights))
        cfg Sequence.s
    in
    (* let _ =
      print_endline "weights allocated";
      print_endline (string_of_int_list_list (List.flatten weights))
    in *)
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

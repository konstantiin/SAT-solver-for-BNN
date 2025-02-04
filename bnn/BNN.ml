open Utils

let scalar_mul v1 v2 =
  List.combine v1 v2 |> List.fold_left (fun acc (e1, e2) -> acc + (e1 * e2)) 0

let linear weights x = List.map (scalar_mul x) weights
let sign x = List.map (fun el -> if el >= 0 then 1 else -1) x

type component_t = Linear of int * int
type config_t = { weights : int list; extra_vars : int list }

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

let alloc_extra_one cfg = (1 + List.hd cfg.extra_vars, alloc_extra cfg 1)

let get_next (cfg, a, cnf) x =
  let cfg = alloc_extra cfg 2 in
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
    [ b0 ] :: [ List.hd r ] :: [ -b1 ] :: [ List.nth r (m + 1) ] :: cnf
  in
  let new_cnf =
    List.fold_left
      (fun cnf_a i ->
        List.fold_left
          (fun cnf_b j ->
            let k = i + j in
            if k > m then cnf_b
            else
              [ -List.nth a i; -List.nth b j; List.nth r k ]
              :: [ List.nth a (i + 1); List.nth b (j + 1); -List.nth r (k + 1) ]
              :: cnf_b)
          cnf_a range_0_m2)
      cnf range_0_m1
  in
  (cfg, r, new_cnf)

let at_least_k input_var k cnf cfg =
  let cfg = alloc_extra cfg 2 in
  let b0 = List.hd cfg.extra_vars in
  let b1 = List.nth cfg.extra_vars 1 in
  let init = b0 :: List.hd input_var :: [ b1 ] in
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
  let (cnf, cfg), res_vars =
    List.fold_left_map mul_to_cnf (cnf, cfg) (List.combine vec1 vec2)
  in
  let k_for_pos = (1 + List.length res_vars) / 2 in
  at_least_k res_vars k_for_pos cnf cfg

let linear_to_cnf cnf cfg input weights =
  List.fold_left_map
    (fun acc line -> scalar_mul_to_cnf acc (input, line))
    (cnf, cfg) weights

module type S = sig
  val components : component_t list
end

module Sequantial (Sequence : S) = struct
  (* let predictor_of_cnf_solution solution =
    let _, sequence =
      List.fold_left_map
        (fun solution_cur component ->
          match component with
          | Linear (inp, out) ->
              let w_cnt = inp * out in
              let weights =
                List.take w_cnt solution_cur
                |> List.map (fun b -> if b then 1 else -1)
              in
              (List.drop w_cnt solution, Fun.compose (linear weights) sign))
        solution Sequence.components
    in
    List.fold_left Fun.compose Fun.id sequence *)
  let cnf =
    let input_features =
      match List.hd Sequence.components with
      | Linear (input, _) -> List.rev (1 -- input)
    in
    let pure_weights_cnt =
      1
      + List.fold_left
          (fun cnt -> function Linear (i, o) -> cnt + (i * o))
          0 Sequence.components
    in
    let _, res, _, _ =
      List.fold_left linear_to_cnf
        (input_features, [], 1, pure_weights_cnt)
        Sequence.components
    in
    res

  let apply_train_data train_data = smth
end

(* open Utils *)
open BNN

let train_data = Csv.load "fashion-mnist/fashion-mnist_train.csv"
let threshold = 200

(* let images data =
  List.tl data
  |> List.map (fun img ->
         img |> List.tl
         |> List.map (fun p -> if int_of_string p > threshold then 255 else 0)
         |> unflatten 28 28 |> List.map Array.of_list |> Array.of_list)

let print_sample img =
  let _ =
    Graphics.open_graph "";
    print_endline "showing image";
    let cimg = Graphics.make_image img |> Graphic_image.image_of in
    let resized = Images.Rgb24 (Rgb24.resize None cimg 400 400) in
    (resized |> Graphic_image.of_image |> Graphics.draw_image) 100 100;
    Graphics.close_graph
  in
  ()

let _ = print_sample (List.hd (images train_data)) *)

let all =
  List.map
    (fun image ->
      let label = int_of_string (List.hd image) in
      let pixels = List.map int_of_string (List.tl image) in
      (pixels, label))
    (List.tl train_data)

let train = List.sort_uniq (fun (_, l1) (_, l2) -> compare l1 l2) all
(* List.take train_sz all
  |> List.map (fun (img, l) ->
         (List.map (fun x -> if x > threshold then 1 else -1) img, l)) *)

let _ =
  List.iter
    (fun (_, l) ->
      print_int l;
      print_string " ")
    train

let test =
  List.drop 100 all
  |> List.map (fun (img, l) ->
         (List.map (fun x -> if x > threshold then 1 else -1) img, l))

module LinearNet = Sequantial (struct
  let s = [ Linear (28 * 28, 4); Linear (4, 10) ]
end)

let _ = print_endline "creating predictor..."

let save_weights weights =
  let meaningfull = List.take (LinearNet.weights_cnt + 2) weights in
  let row = meaningfull |> List.map (fun w -> string_of_bool w) in
  Csv.save "weights/model" [ row ]

let predictor =
  let cnf_to_opt = LinearNet.get_cnf train in
  let _ =
    print_endline "got cnf";
    print_int (List.length cnf_to_opt);
    print_endline " ";
    print_int
      (List.fold_left
         (fun acc c -> if List.length c = 1 then acc + 1 else acc)
         0 cnf_to_opt);
    print_endline ""
  in
  let solution = SATSolver.cdcl cnf_to_opt in
  let _ = print_endline "found some solution" in
  match solution with
  | UNSAT _ -> raise (Failure "unsat cnf")
  | SAT s ->
      save_weights s;
      LinearNet.predictor_of_cnf_solution s

let _ = print_endline "got predictor"

let res =
  List.map
    (fun (img, l) ->
      let p = List.find_index (fun x -> x = 1) (predictor img) in
      match p with None -> l = 0 | Some v -> v = l)
    test

let _ = print_endline "got res"

let _ =
  let tc =
    List.fold_left (fun acc x -> if x then acc + 1 else acc) 0 res
    |> float_of_int
  in
  tc /. float_of_int (List.length res) |> print_float
(*49239822*)

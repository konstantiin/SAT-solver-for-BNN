open BNN

type feature = Num of float | Str of string

let categorize (features : feature list) =
  let uniq =
    let vals =
      List.sort_uniq
        (fun f1 f2 ->
          match f1 with
          | Num n1 -> (
              match f2 with
              | Str _ -> raise (Failure "social credit -100500")
              | Num n2 -> Float.compare n1 n2)
          | Str s1 -> (
              match f2 with
              | Str s2 -> String.compare s1 s2
              | Num _ -> raise (Failure "social credit -100500")))
        features
    in
    Utils.enumerate vals (List.length vals)
  in
  let features_cnt = List.length uniq in
  List.map
    (fun f ->
      let id = List.assoc f uniq in
      Utils.int_to_vec id features_cnt)
    features

let header, train_data_raw =
  let df = Csv.load "titanic/train.csv" in
  Utils.uncons df

let train_data =
  List.filter_map
    (fun r ->
      let l = [ List.nth r 2; List.nth r 4; List.nth r 6; List.nth r 7 ] in
      if List.exists (fun s -> s = "") l then None else Some l)
    train_data_raw

let categorized_data =
  train_data |> Utils.transpose
  |> List.map (fun f -> List.map (fun x -> Str x) f)
  |> List.map (fun feature -> categorize feature)
  |> Utils.transpose

let _ = Num 0.1

let _ =
  print_string "available columns: ";
  String.concat " " header |> print_endline

let flat_data =
  List.map
    (fun sample ->
      List.flatten sample
      |> List.map (fun x ->
             if x = 1 then 1
             else if x = 0 then -1
             else raise (Failure "social credit -100500")))
    categorized_data

let all =
  List.combine flat_data
    (List.map
       (fun sample ->
         let b = int_of_string (List.nth sample 1) in
         if b = 1 then b
         else if b = 0 then -1
         else raise (Failure "social credit -100500"))
       train_data_raw)

let train = List.take 10 all
let test = List.drop 10 all

let _ =
  List.iter (fun (_, o) -> print_int o) train;
  print_endline ""

module LinearNet = Sequantial (struct
  let s = [ Linear (19, 10); Linear (10, 1) ]
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
    print_int (List.length cnf_to_opt)
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
      let p = List.hd (predictor img) in
      let _ =
        print_int l;
        print_newline ();
        print_int p;
        print_newline ()
      in

      p = l)
    test

let _ = print_endline "got res"

let _ =
  let tc =
    List.fold_left (fun acc x -> if x then acc + 1 else acc) 0 res
    |> float_of_int
  in
  tc /. float_of_int (List.length res) |> print_float

(*
1 -1 -1 -1 1 -1 -1 -1 -1 -1 -1  1 -1 -1 -1 -1 -1 -1 1
1 -1 -1 -1 1 -1 -1 -1  1  1  1  1  1  1  1  1  1  1 1
1 1 1 1 1 1 1 1 -1 -1 -1 1 -1 -1 -1 -1 -1 -1 1 

*)

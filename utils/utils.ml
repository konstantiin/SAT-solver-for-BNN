module Intset = Set.Make (Int)

let ( -- ) i j =
  let rec range acc i = if i > j then acc else range (i :: acc) (i + 1) in
  range [] i |> List.rev

let string_of_int_list lst = List.map string_of_int lst |> String.concat " "
let string_of_bool_list lst = List.map string_of_bool lst |> String.concat " "

let string_of_int_list_list lst =
  List.map string_of_int_list lst |> String.concat "\n"

let rec enumerate_acc lst sz acc i =
  if sz = 0 then acc
  else
    match lst with
    | [] -> raise (Failure "list size less then expected")
    | h :: t -> enumerate_acc t (sz - 1) ((h, i) :: acc) (i + 1)

let enumerate lst sz = List.rev (enumerate_acc lst sz [] 0)

let unflatten lst n m =
  let res =
    List.fold_left
      (fun ans (li, i) ->
        if i mod m = 0 then [ li ] :: ans
        else
          match ans with
          | [] -> raise (Failure "impossible branch")
          | h :: t -> (li :: h) :: t)
      []
      (enumerate lst (n * m))
  in
  List.map (fun l -> List.rev l) res |> List.rev

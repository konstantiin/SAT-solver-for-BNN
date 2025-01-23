module Intset = Set.Make (Int)

let ( -- ) i j =
  let rec range acc i = if i > j then acc else range (i :: acc) (i + 1) in
  range [] i |> List.rev

let string_of_int_list lst = List.map string_of_int lst |> String.concat " "
let string_of_bool_list lst = List.map string_of_bool lst |> String.concat " "

let string_of_int_list_list lst =
  List.map string_of_int_list lst |> String.concat "\n"

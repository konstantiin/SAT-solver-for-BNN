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

let unflatten n m lst =
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

let find_arr_of_1 arr =
  List.find_all
    (fun a -> match a with [] -> false | _ :: [] -> true | _ -> false)
    arr
  |> List.flatten

let rec remove_if_any_acc acc lst x =
  match lst with
  | [] -> acc
  | h :: t ->
      if h = x then remove_if_any_acc acc t x
      else remove_if_any_acc (h :: acc) t x

let remove_if_any lst x = remove_if_any_acc [] lst x

(*lst1 \ lst2*)
let remove_intersection lst1 lst2 =
  List.filter
    (fun x ->
      match List.find_opt (fun y -> y = x) lst2 with
      | None -> true
      | Some _ -> false)
    lst1

let is_intersecting lst1 lst2 =
  List.fold_left
    (fun acc x ->
      if acc then acc
      else
        let fopt = List.find_opt (fun y -> x = y) lst2 in
        match fopt with None -> acc | Some _ -> true)
    false lst1

let rec greater_than lst sz =
  if lst = [] then false
  else if sz = 0 then true
  else greater_than (List.tl lst) (sz - 1)

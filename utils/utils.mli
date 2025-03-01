val ( -- ) : int -> int -> int list

module Intset : Set.S with type elt = int

val string_of_int_list_list : int list list -> string
val string_of_int_list : int list -> string
val string_of_bool_list : bool list -> string
val enumerate : 'a list -> int -> ('a * int) list
val unflatten : int -> int -> 'a list -> 'a list list
val find_arr_of_1 : 'a list list -> 'a list
val remove_if_any : 'a list -> 'a -> 'a list
val remove_intersection : 'a list -> 'a list -> 'a list
val is_intersecting : 'a list -> 'a list -> bool
val greater_than : 'a list -> int -> bool
val uncons : 'a list -> 'a * 'a list
val int_to_vec : int -> int -> int list
val transpose : 'a list list -> 'a list list

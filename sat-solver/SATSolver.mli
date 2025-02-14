type clause_t = int list
type cnf_t = clause_t list
type value_t = TRUE | FALSE | UNDEF
type variable_t = { value : value_t; antecender : clause_t option }
type assignment_t = variable_t CCPersistentArray.t
type answer_t = UNSAT of cnf_t | SAT of bool list

val verify_cnf : cnf_t -> bool
val opt_unit_acc : assignment_t -> clause_t -> int * int -> int * int
val opt_unit : assignment_t -> clause_t -> (int * clause_t) option
val is_conflict : assignment_t -> clause_t -> bool

val unit_propagation :
  clause_t list ->
  clause_t list array ->
  assignment_t ->
  assignment_t * clause_t option

val init_assignment : cnf_t -> assignment_t
val conflict_analyzist : clause_t -> assignment_t -> clause_t
val not_always_true : clause_t -> bool
val preprocess : cnf_t -> cnf_t
val get_undef_var_rec : assignment_t -> int -> int -> int option
val get_undef_var : assignment_t -> int option
val assignment_to_bool_list : assignment_t -> bool list
val is_unsatisfiable : assignment_t -> clause_t -> bool
val exists_unsat : cnf_t -> assignment_t -> bool
val get_clause_by_var : cnf_t -> clause_t list array

val cdcl_bf :
  cnf_t -> assignment_t -> clause_t list -> clause_t list array -> answer_t

val cdcl : cnf_t -> answer_t

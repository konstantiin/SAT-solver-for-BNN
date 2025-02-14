open SATSolver

type config_t = { weights : int list; extra_vars : int list }
type component_t = Linear of int * int
type train_data_t = int list * int

val at_least_k :
  int list -> int -> cnf_t -> config_t -> (cnf_t * config_t) * int

module type S = sig
  val s : component_t list
end

module Sequantial : (_ : S) -> sig
  val predictor_of_cnf_solution : bool list -> int list -> int list
  val get_cnf : train_data_t list -> cnf_t
end

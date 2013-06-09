module Id : Id.S
module S : Solver_intf.S

val constrain : Id.c Logic.A.t Formula.t -> unit

val solve : unit -> Terminology.result

val fresh_int_var : unit -> (Id.c, int) Logic.M.t

val fresh_bool_var : unit -> Id.c Logic.A.t Formula.t

val ideref : (Id.c, int) Logic.M.t -> Core.Std.Int63.t option

val bderef : Id.c Logic.A.t Formula.t -> bool option

val toi : int -> (Id.c, int) Logic.M.t

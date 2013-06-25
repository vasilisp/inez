module S : Solver_intf.S

type c

val constrain : c Logic.A.t Formula.t -> unit

val solve : unit -> Terminology.result

val fresh_int_var : unit -> (c, int) Logic.M.t

val fresh_bool_var : unit -> c Logic.A.t Formula.t

val ideref : (c, int) Logic.M.t -> Core.Std.Int63.t option

val bderef : c Logic.A.t Formula.t -> bool option

val toi : int -> (c, int) Logic.M.t

val gen_id : 's Type.t -> (c, 's) Id.t

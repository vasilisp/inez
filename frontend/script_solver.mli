include Script_solver_intf.S
with type ('c, 's) term_plug := ('c, 's) Logic.M.t
and type 's atom_plug := 's Logic.A.t

val add_objective : (c, int) Logic.M.t -> unit

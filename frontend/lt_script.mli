include Script_intf.S
with type ('c, 's) term_plug := ('c, 's) Logic.M.t
and type 's atom_plug := 's Logic.A.t

val assert_axiom : c Axiom.t -> [ `Ok | `Unsupported ]

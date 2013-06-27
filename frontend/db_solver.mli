module Make :

  functor (Imt : Imt_intf.S_with_dp) ->
    functor (I : Id.S) ->

sig

  include Ctx_intf.S_unit_creatable

  val existential :
    bool -> I.c Db_logic.A.t Formula.t -> bool

  val assert_formula :
    ctx -> I.c Db_logic.A.t Formula.t -> [> `Ok | `Out_of_fragment ]

  val solve :
    ctx -> Terminology.result

  val deref_int :
    ctx -> (I.c, int) Id.t -> Core.Std.Int63.t option

  val deref_bool :
    ctx -> (I.c, bool) Id.t -> bool option

  val write_bg_ctx : ctx -> string -> unit

  val add_objective :
    ctx -> (I.c, int) Db_logic.M.t ->
    [> `Duplicate | `Ok | `Out_of_fragment]


end

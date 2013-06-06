module Make :

  functor (Imt : Imt_intf.S_with_dp) ->
    functor (I : Lang_ids.S) ->

sig

  include Ctx_intf.S_unit_creatable

  val existential :
    bool -> I.c Db_lang_abstract.A.t Formula.t -> bool

  val assert_formula :
    ctx -> I.c Db_lang_abstract.A.t Formula.t -> [ `Fail | `Ok ]

  val solve :
    ctx -> Terminology.result

  val deref_int :
    ctx -> (I.c, int) Lang_ids.t -> Core.Std.Int63.t option

  val deref_bool :
    ctx -> (I.c, bool) Lang_ids.t -> bool option

end

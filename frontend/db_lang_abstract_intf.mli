module type Row = sig

  type (_, _) m

  type ('i, _) t =
  | U_Base : ('i, 's) m -> ('i, 's) t
  | U_Pair : ('i, 'r) t * ('i, 's) t -> ('i, 'r * 's) t

end

module type Db = sig

  type _ a

  type (_, _) r

  type ('i, _) t =
  | D_T      :  ('i, 'r ) r list -> ('i, 'r) t
  | D_Cross  :  ('i, 'r) t * ('i, 's) t -> ('i, 'r * 's) t
  | D_Sel    :  ('i, 'r) t * (('i, 'r) r -> 'i a Formula.t) ->
    ('i, 'r) t

end

module type Atom = sig

  type (_, _) d
  type (_, _) m

  type 'i t =
  | A_Empty  :   ('i, 'r) d -> 'i t
  | A_Bool   of  ('i, bool) m
  | A_Le     of  ('i, int) m
  | A_Eq     of  ('i, int) m

end

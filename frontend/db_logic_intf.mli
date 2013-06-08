module type Schema = sig

  type _ t =
  | S_Int   :  int t
  | S_Bool  :  bool t
  | S_Pair  :  'a t * 'b t -> ('a * 'b) t

end

module type Row = sig

  type (_, _) m

  type ('i, _) t =
  | R_Int   :  ('i, int) m ->
    ('i, int) t
  | R_Bool  :  ('i, bool) m ->
    ('i, bool) t
  | R_Pair  :  ('i, 'r) t * ('i, 's) t ->
    ('i, 'r * 's) t

end

module type Row_with_ops = sig

  include Row

  type _ a

  type _ s

  val of_list :
    'u s ->
    (('i, int) m, 'i a Formula.t) Terminology.ibeither list ->
    ('i, 'u) t option

  val to_list :
    ('i, 's) t ->
    (('i, int) m, 'i a Formula.t) Terminology.ibeither list

end

module type Db = sig

  type _ a

  type _ s

  type (_, _) r

  type ('i, _) t =
  | D_Input  :  'r s * ('i, 'r) r list ->
    ('i, 'r) t
  | D_Cross  :  ('i, 'r) t * ('i, 's) t ->
    ('i, 'r * 's) t
  | D_Sel    :  ('i, 'r) t * (('i, 'r) r -> 'i a Formula.t) ->
    ('i, 'r) t

end

module type Db_with_ops = sig

  include Db

  val sel :
    ('i, 's) t -> (('i, 's) r -> 'i a Formula.t) -> ('i, 's) t

  val cross :
    ('i, 'r) t -> ('i, 's) t -> ('i, 'r * 's) t

  val schema_of_t : (_, 'r) t -> 'r s

end

module type Atom = sig

  type (_, _) d
  type (_, _) m

  type 'i t =
  | A_Exists  :   ('i, 'r) d -> 'i t
  | A_Bool    of  ('i, bool) m
  | A_Le      of  ('i, int) m
  | A_Eq      of  ('i, int) m

end

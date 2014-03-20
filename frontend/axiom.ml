open Terminology
open Core.Std

type 'i quantified = ('i, int) Id.t

type 'i hypothesis =
  (('i, int) Flat.t * ('i, int) Flat.t option) offset

type 'i cut =
  ('i, int) Flat.t iexpr

type 'i t =
  'i quantified list * 'i hypothesis list * 'i cut

let iter_subterms (_, h, (l, _) : 'i t) ~f =
  (let f ((a, b), _) = f a; Option.iter b ~f in
   List.iter h ~f);
  (let f = Fn.compose f Tuple.T2.get2 in
   List.iter l ~f)


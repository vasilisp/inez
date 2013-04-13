open Core.Std
open Terminology

type 'a formula =
  F_True
| F_Atom  of  'a
| F_Not   of  'a formula
| F_And   of  'a formula * 'a formula
| F_Ite   of  'a formula * 'a formula * 'a formula

(* constant formulas *)

let true' = F_True

let false' = F_Not F_True

(* formula operators *)

let not g = F_Not g

let (&&) g h = F_And (g, h)

let (||) g h = not (not g && not h)

let (=>) g h = not g || h

let ite c g h = F_Ite (c, g, h)

(* quantifiers over lists *)

let forall l ~f =
  let f acc = Fn.compose ((&&) acc) f
  and init = true' in
  List.fold_left l ~init ~f

let exists l ~f =
  let f acc = Fn.compose ((&&) acc) (Fn.compose not f)
  and init = false' in
  not (List.fold_left l ~init ~f)

let rec map g ~f =
  match g with
  | F_True ->
    F_True
  | F_Atom a ->
    F_Atom (f a)
  | F_Not g ->
    F_Not (map g ~f)
  | F_And (g, h) ->
    F_And (map g ~f, map h ~f)
  | F_Ite (q, g, h) ->
    F_Ite (map q ~f, map g ~f, map h ~f)

open Core.Std
open Terminology

type 'a formula =
  F_True
| F_Ground  of  'a
| F_Not     of  'a formula
| F_And     of  'a formula * 'a formula
| F_Ite     of  'a formula * 'a formula * 'a formula

(* constant formulas *)

let true' = F_True

let false' = F_Not F_True

(* formula operators *)

let not g = F_Not g

let (&&) g h = F_And (g, h)

let (||) g h = not (not g && not h)

let (=>) g h = not g || h

let ite c g h = F_Ite (c, g, h)


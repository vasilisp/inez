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

let not = function
  | F_Not g ->
    g
  | g ->
    F_Not g

let (&&) g h =
  match g, h with
  | F_True, g | g, F_True ->
    g
  | F_Not F_True, _ | _, F_Not F_True ->
    F_Not F_True
  | _ ->
    F_And (g, h)

let (||) g h = not (not g && not h)

let (=>) g h = not g || h

let ite c g h =
  match c with
  | F_True ->
    g
  | F_Not F_True ->
    h
  | _ ->
    F_Ite (c, g, h)

let forall l ~f =
  let rec forall_aux acc = function
    | h :: t ->
      (match  acc && f h with
      | F_Not F_True as g ->
        g
      | acc ->
        forall_aux acc t)
    | [] -> 
      acc in
  forall_aux F_True l

let exists l ~f =
  not (forall l ~f:(Fn.compose (not) f))

let rec map g ~f =
  match g with
  | F_True ->
    F_True
  | F_Atom a ->
    F_Atom (f a)
  | F_Not g ->
    not (map g ~f)
  | F_And (g, h) ->
    map g ~f && map h ~f
  | F_Ite (q, g, h) ->
    ite (map q ~f) (map g ~f) (map h ~f)

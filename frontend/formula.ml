open Core.Std
open Terminology

type 'a t =
  F_True
| F_Atom  of  'a
| F_Not   of  'a t
| F_And   of  'a t * 'a t
| F_Ite   of  'a t * 'a t * 'a t

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

let forall_pairs l ~f =
  let rec forall_pairs_aux acc = function
    | a :: d ->
      (match acc && forall d ~f:(f a) with
      | F_Not F_True as g ->
        g
      | acc ->
        forall_pairs_aux acc d)
    | [] ->
      acc in
  forall_pairs_aux F_True l

let exists l ~f =
  not (forall l ~f:(Fn.compose (not) f))

let negate_polarity = function
  | `Positive -> `Negative
  | `Negative -> `Positive
  | `Both -> `Both

let rec map_non_atomic g ~f ~polarity =
  match g with
  | F_True ->
    F_True
  | F_Atom a ->
    f a ~polarity
  | F_Not g ->
    let polarity = negate_polarity polarity in
    not (map_non_atomic g ~f ~polarity)
  | F_And (g, h) ->
    map_non_atomic g ~f ~polarity && map_non_atomic h ~f ~polarity
  | F_Ite (q, g, h) ->
    ite (map_non_atomic q ~f ~polarity:`Both)
      (map_non_atomic g ~f ~polarity)
      (map_non_atomic h ~f ~polarity)

let rec map g ~f ~polarity =
  map_non_atomic g ~polarity
    ~f:(fun x ~polarity -> F_Atom (f x ~polarity))

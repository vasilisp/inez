(* utility functions; too small to get their own module *)

let foldo_right l ~f ~init =
  let rec fr_aux acc = function
    | a :: d ->
      (match f a acc with
      | Some x ->
        fr_aux x d
      | None ->
        None)
    | _ ->
      Some acc in
  fr_aux init l

let iter_pairs l ~f =
  let rec iter_pairs_aux = function
    | a :: d ->
      Core.Std.List.iter d ~f:(f a); iter_pairs_aux d
    | [] ->
      () in
  iter_pairs_aux l

exception Exn of (string * Here.t)

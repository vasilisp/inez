open Core.Std
open Logic

module Make
  
  (Imt : sig

    include Imt_intf.S_essentials

    type sol

    module Dvars : (Imt_intf.Dvars_access
                    with type ctx_plug := ctx
                    and type sol_plug := sol)

  end) =

struct

  type axiom_id = int
  with compare, sexp_of

  type occ = axiom_id * Imt.Dvars.t list * int option ref

  type hypotheses = Imt.Dvars.t list 
  with sexp_of

  type cut = Imt.ivar Terminology.iexpr
  with sexp_of

  type cuts = Imt.ivar Terminology.iexpr list
  with sexp_of

  type instantiator = axiom_id -> Imt.Dvars.t list -> cut list

  type axiom = occ Dequeue.t * instantiator

  type ctx = {
    mutable r_next_id  :  int;
    r_axioms_h         :  axiom Int.Table.t;
    mutable r_level    :  int;
  }

  let make_ctx () = {
    r_next_id  = 0;
    r_axioms_h = Int.Table.create ~size:128 ();
    r_level    = 0
  }

  module F

    (S : Imt_intf.S_cut_gen_access
     with type ivar := Imt.ivar
     and type bvar := Imt.bvar
     and type Dvars.t = Imt.Dvars.t) =

  struct

    let met_hypotheses_sol r' sol =
      let f v = Int63.(S.Dvars.ideref_sol r' sol v <= zero) in
      List.for_all ~f

    let eval_cut r' sol (l, o) = 
      let f acc (c, v) = Int63.(acc + c * S.ideref_sol r' sol v)
      and init = o in
      Int63.(List.fold_left l ~init ~f <= zero)

    let check_axiom_occ r' sol axiom_id f (_, dvars, _ : occ) =
      let cuts = f axiom_id dvars in
      let b1 = met_hypotheses_sol r' sol dvars
      and b2 = List.for_all cuts ~f:(eval_cut r' sol) in
      (*
      Printf.printf "%s => %s\n%!"
        (Sexplib.Sexp.to_string (sexp_of_hypotheses dvars))
        (Sexplib.Sexp.to_string (sexp_of_cuts cuts));
      Printf.printf "not %b => %b\n%!" b1 b2;
      *)
      not b1 || b2

    let check_axiom r' sol axiom_id (occs, f : axiom) =
      Dequeue.for_all occs ~f:(check_axiom_occ r' sol axiom_id f)

    let check {r_axioms_h} r' sol =
      let f ~key ~data = not (check_axiom r' sol key data) in
      not (Hashtbl.existsi r_axioms_h ~f)

    let backtrack ({r_axioms_h; r_level} as r) r' =
      assert (r_level >= 0);
      r.r_level <- r.r_level - 1;
      let f ~key ~data:(occs, _) =
        let f = function
          | (_, _, ({contents = Some level'} as reference)) ->
            if level' > r.r_level then reference := None
          | _ ->
            () in
        Dequeue.iter occs ~f in
      Hashtbl.iter r_axioms_h ~f

    let push_level r r' =
      r.r_level <- r.r_level + 1

    type response_generate_axiom_occ =
      R_Cutoff | R_Gen_Unsat | R_Gen_Sat
        
    let lb_cut r' (l, o) =
      let f acc (c, v) =
        let lb =
          if Int63.(c >= zero) then
            S.get_lb_local r' v
          else
            S.get_ub_local r' v in
        let lb = Option.(lb >>| Int63.( * ) c)
        and f = Int63.(+) in
        Option.map2 ~f lb acc 
      and init = Some o in
      List.fold_left l ~init ~f

    let ub_cut r' (l, o) =
      let f acc (c, v) =
        let ub =
          if Int63.(c >= zero) then
            S.get_ub_local r' v
          else
            S.get_lb_local r' v in
        let ub = Option.(ub >>| Int63.( * ) c)
        and f = Int63.(+) in
        Option.map2 ~f ub acc 
      and init = Some o in
      List.fold_left l ~init ~f

    type response_gao =
    | R_Unknown
    | R_Sat
    | R_Sat_Cut of cut list
    | R_Unsat of cut list
    | R_Cutoff

    let met_hypotheses r' = 
      let f v =
        match S.Dvars.get_ub_local r' v with
        | Some ub ->
          Int63.(ub <= zero)
        | None ->
          false in
      List.for_all ~f

    let generate_axiom_occ {r_level} r' sol axiom_id f occ =
      let cuts = f axiom_id
      and lb c = Option.value (lb_cut r' c) ~default:Int63.minus_one
      and eval = List.for_all ~f:(eval_cut r' sol) in
      match occ with
      | _, dvars, {contents = Some _} ->
        if
          not (met_hypotheses r' dvars) || not (eval (cuts dvars))
        then
          raise (Unreachable.Exn _here_)
        else
          R_Sat
      | _, dvars, _ ->
        if met_hypotheses r' dvars then
          (let l = cuts dvars in
           if
             let f c = Int63.(lb c > zero) in
             List.exists l ~f
           then
             R_Cutoff
           else if eval l then
             R_Sat
           else
             R_Unsat l)
        else
          if
            not (met_hypotheses_sol r' sol dvars) || eval (cuts dvars)
          then
            R_Sat
          else
            R_Unknown

    type response_ga = [ `Unknown | `Sat | `Unsat_Cut_Gen | `Cutoff ]

    let combine_response_ga (r1 : response_ga) (r2 : response_ga) =
      match r1, r2 with
      | `Cutoff, _ | _, `Cutoff ->
        `Cutoff
      | `Unsat_Cut_Gen, _ | _, `Unsat_Cut_Gen ->
        `Unsat_Cut_Gen
      | `Unknown, _ | _, `Unknown ->
        `Unknown
      | `Sat, `Sat ->
        `Sat

    let generate_axiom ({r_level} as r) r' sol (occs, f : axiom) =
      let response = ref `Sat in
      let f ((axiom_id, dvars, level : occ) as occ) =
        match generate_axiom_occ r r' sol axiom_id f occ with
        | R_Unknown ->
          response := combine_response_ga !response `Unknown;
          false
        | R_Sat ->
          false
        | R_Sat_Cut _ ->
          (* in theory we could add the generated cuts; SCIP doesn't
             like them *)
          false
        | R_Unsat l ->
          List.iter l ~f:(S.add_cut_local r');
          level := Some r_level;
          response := combine_response_ga !response `Unsat_Cut_Gen;
          true
        | R_Cutoff ->
          response := combine_response_ga !response `Cutoff;
          true in
      let _ = Dequeue.exists occs ~f in
      !response

    let generate ({r_axioms_h} as r) r' sol =
      let response = ref `Sat in
      let f a =
        let r = generate_axiom r r' sol a in
        response := combine_response_ga !response r;
        match r with
        | `Cutoff | `Unsat_Cut_Gen ->
          true
        | _ ->
          false in
      let _ = Hashtbl.exists r_axioms_h ~f in
      !response

  end

  let assert_axiom ({r_next_id = id; r_axioms_h} as r) f =
    r.r_next_id <- id + 1;
    Hashtbl.replace r_axioms_h id (Dequeue.create (), f);
    id

  let assert_instance {r_axioms_h} id l =
    let occs, f = Hashtbl.find_exn r_axioms_h id in
    Dequeue.enqueue_back occs (id, l, ref None)

end

open Core.Std
open Async.Std
open Async
open Ocaml_plugin.Std

(*
  module Plugin = Ocaml_dynloader.Make(struct
  type t = (module Script_intf.S)
  let t_repr = "Script_intf.S"
  let univ_constr = Script_intf.univ_constr
  let univ_constr_repr = "Script_intf.univ_constr"
  end)
*)

let () =
  let file = Sys.argv.(1) in
  don't_wait_for (
    Ocaml_plugin.Shell.set_defaults ~verbose:false ~echo:false ();
    Ocaml_compiler.create () >>= function
    | Error e ->
      Printf.eprintf "Cannot build embed loader: %s"
        (Error.to_string_hum e);
      exit 1
    | Ok (`this_needs_manual_cleaning_after ocaml_compiler) ->
      don't_wait_for
        (Ocaml_compiler.read_directory ocaml_compiler >>| function
        | Ok directory ->
          Printf.eprintf "compilation happens in %S\n%!" directory
        | Error exn ->
          Printf.eprintf "Cannot initialize loader: %s\n%!"
            (Error.to_string_hum exn));
      (* let loader = Ocaml_compiler.loader ocaml_compiler in *)
      let clean_and_shutdown () =
        Ocaml_compiler.clean ocaml_compiler >>= fun result ->
        let () = Or_error.ok_exn result in
        return (shutdown 0) in
      let rec doit () =
        Ocaml_compiler.load_ocaml_src_files [file]
          (* ?camlp4o_opt:None *)
          ~cmx_flags:["-pp \"camlp4o pa_logic.cmxs\""]
        >>= function
        | Error e ->
          Printf.eprintf "Cannot build embed loader: %s"
            (Error.to_string_hum e);
          clean_and_shutdown ()
        | Ok () ->
          Printf.printf "loaded plugin\n%!";
          clean_and_shutdown () in
      doit ())

let () = never_returns (Scheduler.go ())

open Core.Std
open Async.Std
open Ocaml_plugin.Std

let _ =
  let file = Sys.argv.(1) in
  don't_wait_for (
    Ocaml_plugin.Shell.set_defaults ~verbose:false ~echo:false ();
    Ocaml_compiler.load_ocaml_src_files [file]
      ~custom_warnings_spec:"@a-4-9-29-33" >>=
      function
      | Error e ->
        Printf.eprintf "Script error: %s\n" (Error.to_string_hum e);
        return (shutdown 0)
      | Ok () ->
        return (shutdown 0))

let _ =
  never_returns (Scheduler.go ())

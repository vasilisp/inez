(* copied from http://janestreet.github.com/installation.html *)

#use "topfind"
#thread
#require "dynlink"
#camlp4o
#require "bin_prot.syntax"
#require "sexplib.syntax"
#require "variantslib.syntax"
#require "fieldslib.syntax"
#require "comparelib.syntax"
#require "core"

#require "camlp4"
#require "camlp4.quotations"
#load "formula_dsl.cmo"
#load "formula.cmo"

open Core.Std
open Camlp4.PreCast

module Formula = (Formula: Formula_intf.S)

let _loc = Camlp4.PreCast.Loc.ghost

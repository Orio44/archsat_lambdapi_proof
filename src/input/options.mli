(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(** Global options for the prover.

    This module defines options for the prover.
    Also defines global constants such as sections,
    mainly for dependency reasons.
*)

exception Sigint
exception Out_of_time
exception Out_of_space
exception File_not_found of string
exception Stmt_not_implemented of Dolmen.Statement.t
(** Some exceptions *)

val misc_section : Section.t

type input = In.language
(* Type alias for input languages *)

type output =
  | Standard
  | SZS
(** Type for output format *)

type mode =
  | Debug
  | Regular
  | Interactive
(** Type for modes of running. *)

type status =
  | Ok
  | Errored

type input_options = {
  mode    : mode;
  format  : input option;
  dir     : string;
  file    : [ `Stdin | `File of string];
}

type output_options = {
  format  : output;
  icnf    : Format.formatter option;
  dimacs  : Format.formatter option;
  tptp    : Format.formatter option;
}

type typing_options = {
  infer : bool;
  typing : bool;
  explain : [ `No | `Yes | `Full ];
}

type profile_options = {
  enabled   : bool;
  max_depth : int option;
  sections  : Section.t list;
  raw_data  : Format.formatter option;
}

type stats_options = {
  enabled       : bool;
}

type coq_options = {
  msat        : Format.formatter option;
  script      : Format.formatter option;
  term        : Format.formatter option;
  term_big    : bool;
  norm        : Format.formatter option;
  norm_big    : bool;
}

type dot_options = {
  incr        : string option;
  res         : Format.formatter option;
  full        : Format.formatter option;
}

type dedukti_options = {
  term        : Format.formatter option;
  term_big    : bool;
  norm        : Format.formatter option;
  norm_big    : bool;
}

type lambdapi_options = {
  lp_term        : Format.formatter option;
  lp_term_big    : bool;
  lp_sig         : string option;
}

type proof_options = {
  active      : bool;
  context     : bool;
  coq         : coq_options;
  dot         : dot_options;
  dedukti     : dedukti_options;
  lambdapi    : lambdapi_options;
  unsat_core  : Format.formatter option;
}

type model_options = {
  active      : bool;
  assign      : Format.formatter option;
}

type opts = {

  (* Internal status *)
  status  : status;

  (* Input&output options *)
  input   : input_options;
  output  : output_options;

  (* Typing options *)
  typing  : typing_options;
  translate         : bool;

  (* Proof&model options *)
  proof   : proof_options;
  model   : model_options;

  (* Solving options *)
  solve   : bool;
  addons  : string list;
  plugins : string list;

  (* Time/Memory options *)
  time_limit  : float;
  size_limit  : float;
  profile     : profile_options;
  stats       : stats_options;
}
(** Common options for theorem proving. *)

val input_to_string : [ `Stdin | `File of string ] -> string
(** String representation of inut mode. *)

val log_opts : opts -> unit
(** Prints a summary of options *)

val ext_sect : string
val copts_sect : string
val proof_sect : string
val model_sect : string
(** Section names for options in cmdliner. *)

val help_secs :
  Cmdliner.Manpage.block list ->
  Cmdliner.Manpage.block list ->
  Cmdliner.Manpage.block list
(** Given documentation for addons, then extensions,
    returns a documentation for the tool. *)

val copts_t : unit -> opts Cmdliner.Term.t
(** A term to evaluate common options from the command line. *)

val error : opts -> opts
(** Change the status of the options to [Errored],
    except if in interactive mode. *)


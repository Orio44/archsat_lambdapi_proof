
let section = Util.Section.make ~parent:Dispatcher.section "stats"

(* Statistics record & manipulations *)
let max_rounds = ref 0

type t = {
  mutable cur_round : int;
  instanciations : ((int * int), CCVector.rw) CCVector.t;
}

let print_state state =
  let s = state.cur_round in
  let (i, r) = CCVector.get state.instanciations s in
  Util.debug ~section 0 "Round %d : instanciations %d (remaining : %d)" s i r

let init_round state =
  state.cur_round <- state.cur_round + 1;
  CCVector.push state.instanciations (0, 0)

(* State record *)
let state = {
  cur_round = 0;
  instanciations = CCVector.make 1 (0, 0);
  }

(* Exported functions *)
let current_round () = state.cur_round

let inst_done () =
  let s = state.cur_round in
  let (i, r) = CCVector.get state.instanciations s in
  CCVector.set state.instanciations s (i + 1, r)

let inst_remaining r =
  let s = state.cur_round in
  let (i, _) = CCVector.get state.instanciations s in
  CCVector.set state.instanciations s (i, r)

(* Print stats and prep for next round *)
let handler =
  { Dispatcher.handle =
      fun (type ret) (msg : ret Dispatcher.msg) ->
        match msg with
        | Dispatcher.If_sat _ ->
          print_state state;
          if !max_rounds >= 0 && state.cur_round >= !max_rounds then
            raise (Extension.Abort (
                "stats", Format.sprintf "Maximum number of rounds reached (%d)" !max_rounds));
          init_round state;
          (Some () : ret option)
        | _ -> (None : ret option)
          ;
  }

(* Extension registering *)
(* ************************************************************************ *)

let options =
  let docs = Options.ext_sect in
  let stop =
    let doc = "Stop at the given round" in
    Cmdliner.Arg.(value & opt int (-1) & info ["stats.stop"] ~docv:"N" ~docs ~doc)
  in
  let set_opts n =
    max_rounds := n
  in
  Cmdliner.Term.(pure set_opts $ stop)

;;
Dispatcher.Plugin.register "stats" ~prio:0 ~options
  ~descr:"Handles delayed printing of statistics for each round of solving"
  (Dispatcher.mk_ext
     ~handle:handler
     ~section ()
  )


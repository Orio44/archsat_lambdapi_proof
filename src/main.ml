
(* ArchSat *)

open Options

(* Main function *)
let () =
  (* Register all extensions *)
  Ext.register_all ();
  (* Argument parsing *)
  let man = Options.help_secs (Dispatcher.Plugin.ext_doc ()) (Semantics.Addon.ext_doc ()) in
  let info = Cmdliner.Term.(info ~sdocs:Options.copts_sect ~man ~version:"0.1" "archsat") in
  let opts = Cmdliner.Term.(
      pure (fun () () x -> x)
      $ Semantics.Addon.opts ()
      $ Dispatcher.Plugin.opts ()
      $ (Options.copts_t ())
    ) in
  let opt = match Cmdliner.Term.eval (opts, info) with
    | `Version | `Help -> exit 0
    | `Error `Parse | `Error `Term | `Error `Exn -> exit 1
    | `Ok opt -> opt
  in

  let opt', g =
    try
      Format.set_margin 100;
      (* Profiling *)
      if opt.profile.enabled then begin
        Util.enable_profiling ();
        Util.Section.set_profile_depth
          (CCOpt.get_or ~default:0 opt.profile.max_depth);
        List.iter Util.Section.profile_section opt.profile.sections
      end;
      if opt.profile.print_stats then
        Util.enable_statistics ();

      (* Syntax extensions *)
      Semantics.Addon.set_exts "+base,+arith";
      List.iter Semantics.Addon.set_ext opt.addons;

      (* Extensions options *)
      Dispatcher.Plugin.set_exts "+eq,+uf,+logic,+prop,+skolem,+inst,+stats";
      List.iter Dispatcher.Plugin.set_ext opt.plugins;

      (* Print the current options *)
      Options.log_opts opt;
      Util.log ~section:Semantics.section "active: @[<hov>%a@]"
        CCFormat.(list string) (Semantics.Addon.active ());
      Util.log ~section:Dispatcher.plugin_section "active: @[<hov>%a@]"
        CCFormat.(list string) (Dispatcher.Plugin.active ());

      Pipe.parse opt
    with e ->
      Out.print_exn opt e;
      exit 2
  in
  Pipeline.(
    run ~print_exn:Out.print_exn g opt' (
      (
        (fix (apply ~name:"expand" Pipe.expand) (
            (apply ~name:"execute" Pipe.execute)
            @>>> (f_map ~name:"typecheck" Pipe.typecheck)
            @>>> (f_map ~name:"solve" Pipe.solve)
            @>>> (iter_ ~name:"print_res" Pipe.print_res)
            @>>> (apply fst) @>>> _end)
        ) @||| (
          (iter_ ~name:"print_stats" Pipe.print_stats) @>>> _end
        )
      )
    )
  )



let section = Util.Section.make ~parent:Dispatcher.section "inst"

(* Instanciation helpers *)
(* ************************************************************************ *)

let index m = Expr.(m.meta_index)

(* Partial order, representing the inclusion on quantified formulas
 * Uses the free variables to determine inclusion. *)
let free_args = function
  | { Expr.formula = Expr.All (_, args, _) }
  | { Expr.formula = Expr.Ex (_, args, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (_, args, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (_, args, _) } }
  | { Expr.formula = Expr.AllTy (_, args, _) }
  | { Expr.formula = Expr.ExTy (_, args, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (_, args, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (_, args, _) } } -> args
  | _ -> assert false

let sub_quant p q = match p with
  | { Expr.formula = Expr.All (l, _, _) }
  | { Expr.formula = Expr.Ex (l, _, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, _, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, _) } } ->
    let _, tl = free_args q in
    List.exists (fun v -> List.exists (function
        | { Expr.term = Expr.Var v' } | { Expr.term = Expr.Meta { Expr.meta_id = v' } } ->
          Expr.Id.equal v v'
        | _ -> false) tl) l
  | { Expr.formula = Expr.AllTy (l, _, _) }
  | { Expr.formula = Expr.ExTy (l, _, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, _, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (l, _, _) } } ->
    let tyl, _ = free_args q in
    List.exists (fun v -> List.exists (function
        | { Expr.ty = Expr.TyVar v' } | { Expr.ty = Expr.TyMeta { Expr.meta_id = v' } } ->
          Expr.Id.equal v v'
        | _ -> false) tyl) l
  | _ -> assert false

let quant_compare p q =
  if Expr.Formula.equal p q then
    Some 0
  else if sub_quant p q then
    Some 1
  else if sub_quant q p then
    Some ~-1
  else
    None

let quant_comparable p q = match quant_compare p q with
  | Some _ -> true
  | None -> false

(* Splits an arbitrary unifier (Unif.t) into a list of
 * unifiers such that all formula generating the metas in
 * a unifier are comparable according to compare_quant. *)
let belong_ty m s =
  let f = Expr.Meta.ttype_def (index m) in
  let aux m' _ =
    let f' = Expr.Meta.ttype_def (index m') in
    if Expr.Formula.equal f f' then index m = index m'
    else quant_comparable f f'
  in
  Expr.Subst.exists aux Unif.(s.ty_map)

let belong_term m s =
  let f = Expr.Meta.ty_def (index m) in
  let aux m' _ =
    let f' = Expr.Meta.ty_def (index m') in
    if Expr.Formula.equal f f' then index m = index m'
    else quant_comparable f f'
  in
  Expr.Subst.exists aux Unif.(s.t_map)

let split s =
  let rec aux bind belongs acc m t = function
    | [] -> bind Unif.empty m t :: acc
    | s :: r ->
      if belongs m s then
        (bind s m t) :: (List.rev_append acc r)
      else
        aux bind belongs (s :: acc) m t r
  in
  Expr.Subst.fold (aux Unif.bind_term belong_term []) Unif.(s.t_map)
    (Expr.Subst.fold (aux Unif.bind_ty belong_ty []) Unif.(s.ty_map) [])

(* Given an arbitrary substitution (Unif.t),
 * Returns a pair (formula * Unif.t) to instanciate
 * the outermost metas in the given unifier. *)
let partition s =
  let aux bind m t = function
    | None -> Some (index m, bind Unif.empty m t)
    | Some (min_index, acc) ->
      let i = index m in
      if i < min_index then
        Some (i, bind Unif.empty m t)
      else if i = min_index then
        Some (i, bind acc m t)
      else
        Some (min_index, acc)
  in
  match Expr.Subst.fold (aux Unif.bind_ty) Unif.(s.ty_map) None with
  | Some (i, u) -> Expr.Meta.ttype_def i, u
  | None ->
    match Expr.Subst.fold (aux Unif.bind_term) Unif.(s.t_map) None with
    | Some (i, u) -> Expr.Meta.ty_def i, u
    | None -> assert false

let simplify s = snd (partition s)

(* Produces a proof for the instanciation of the given formulas and unifiers *)
let mk_proof f p ty_map t_map = Dispatcher.mk_proof "inst"
    ~ty_args:(Expr.Subst.fold (fun v t l -> Expr.Ty.of_id v :: t :: l) ty_map [])
    ~term_args:(Expr.Subst.fold (fun v t l -> Expr.Term.of_id v :: t :: l) t_map [])
    ~formula_args:[f; p] "inst"

let to_var s = Expr.Subst.fold (fun {Expr.meta_id = v} t acc -> Expr.Subst.Id.bind v t acc) s Expr.Subst.empty

let soft_subst f ty_subst term_subst =
  let q = Expr.Formula.partial_inst ty_subst term_subst f in
  [ Expr.Formula.neg f; q], mk_proof f q ty_subst term_subst

(* Heap for prioritizing instanciations *)
(* ************************************************************************ *)

module Inst = struct
  type t = {
    age : int;
    score : int;
    formula : Expr.formula;
    ty_subst : Expr.Ty.subst;
    term_subst : Expr.Term.subst;
  }

  (* Age counter *)
  let age = ref 0
  let clock () = incr age

  (* Constructor *)
  let mk u k =
    let f, s = partition u in
    {
    age = !age;
    score = k;
    formula = f;
    ty_subst = to_var Unif.(s.ty_map);
    term_subst = to_var Unif.(s.t_map);
    }

  (* debug printing *)
  let debug b t =
    Printf.bprintf b "%a%a" Expr.Ty.debug_subst t.ty_subst Expr.Term.debug_subst t.term_subst

  (* Comparison for the Heap *)
  let leq t1 t2 = t1.score + t1.age <= t2.score + t2.age

  (* Hash and equality for the hashtbl. *)
  let hash t =
    Hashtbl.hash (Expr.Formula.hash t.formula,
                  Expr.Subst.hash Expr.Ty.hash t.ty_subst,
                  Expr.Subst.hash Expr.Term.hash t.term_subst)

  let equal t t' =
    Expr.Formula.equal t.formula t'.formula &&
    Expr.Subst.equal Expr.Ty.equal t.ty_subst t'.ty_subst &&
    Expr.Subst.equal Expr.Term.equal t.term_subst t'.term_subst
end

module Q = CCHeap.Make(Inst)
module H = Hashtbl.Make(Inst)

let heap = ref Q.empty
let delayed = ref []
let inst_set = H.create 4096
let inst_incr = ref 0

let add ?(delay=0) ?(score=0) u =
  let t = Inst.mk u score in
  if not (H.mem inst_set t) then begin
    H.add inst_set t false;
    Util.debug ~section 10 "New inst : %a" Inst.debug t;
    if delay <= 0 then
      heap := Q.add !heap t
    else
      delayed := (t, delay) :: !delayed;
    true
  end else begin
    Util.debug ~section 15 "Redondant inst : %a" Inst.debug t;
    false
  end

let push inst =
  Stats.inst_done ();
  assert (not (H.find inst_set inst));
  H.replace inst_set inst true;
  Util.debug ~section 5 "Pushed inst : %a" Inst.debug inst;
  let open Inst in
  let cl, p = soft_subst inst.formula inst.ty_subst inst.term_subst in
  Dispatcher.push cl p

let take f k =
  let aux f i =
    for _ = 1 to i do
      match Q.take !heap with
      | None -> ()
      | Some (new_h, min) ->
        heap := new_h;
        f min;
    done
  in
  if k > 0 then
    aux f k
  else
    aux f (Q.size !heap + k)

let rec decr_delay () =
  if !delayed = [] then
    ()
  else begin
    delayed := CCList.filter_map (fun (u, d) ->
        if d > 1 then
          Some (u, d - 1)
        else begin
          heap := Q.add !heap u;
          None
        end
      ) !delayed;
    if Q.size !heap = 0 then
      decr_delay ()
  end

let inst_sat : type ret. ret Dispatcher.msg -> ret option = function
  | Dispatcher.If_sat _ ->
    decr_delay ();
    take push !inst_incr;
    Stats.inst_remaining (Q.size !heap);
    Some (Inst.clock ())
  | _ -> None

(* Extension registering *)
(* ************************************************************************ *)

let opts =
  let docs = Options.ext_sect in
  let n_of_inst =
    let doc = "Decides how many instanciations are pushed to the solver each round.
                   If $(docv) is a strictly positive number, then at each round, the $(docv)
                   most promising instanciations are pushed. If $(docv) is negative, then all
                   but the $(docv) least promising instanciations are pushed." in
    Cmdliner.Arg.(value & opt int 0 & info ["inst.nb"] ~docv:"N" ~docs ~doc)
  in
  let set_opts nb =
    inst_incr := nb
  in
  Cmdliner.Term.(pure set_opts $ n_of_inst)

;;
Dispatcher.Plugin.register "inst" ~prio:5 ~options:opts
  ~descr:"Handles the pushing of clauses corresponding to instanciations. This plugin does not
          do anything by itself, but rather is called by other plugins when doing instanciations."
  (Dispatcher.mk_ext ~section ~handle:{Dispatcher.handle=inst_sat} ())


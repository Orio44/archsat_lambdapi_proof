
(** Random generation of terms

    This module is designed to generate random terms. Since truly random terms might
    not be that useful we instead constrain generated terms to live inside a specific
    signature of types and terms (defined in the [S] module).
*)

(* QCheck related definitions *)
(* ************************************************************************ *)

module G = QCheck.Gen
module I = QCheck.Iter
module S = QCheck.Shrink

type 'a gen = 'a QCheck.Gen.t
type 'a sized = 'a QCheck.Gen.sized
type 'a shrink = 'a QCheck.Shrink.t
type 'a arbitrary = 'a QCheck.arbitrary

let rec split size len =
  let open G in
  if len = 0 then
    return []
  else if len = 1 then
    return [size]
  else begin
    (0 -- size) >>= fun hd ->
    split (size - hd) (len - 1) >|= fun tl ->
    hd :: tl
  end

let split_int size =
  G.(split size 2 >|= function
    | [a; b] -> a, b | _ -> assert false)

let sublist l =
  G.(shuffle_l l >>= fun l ->
     (0 -- List.length l) >|= fun n ->
     CCList.take n l)

let iter_filter p seq k =
  seq (fun x -> if p x then k x)

module type S = sig
  type t
  val print : t -> string
  val small : t -> int
  val shrink : t shrink
  val sized : t sized
  val gen : t gen
  val t : t arbitrary
end

(* Small matching algorithm for types *)
(* ************************************************************************ *)

module Match = struct

  exception No_match

  let rec ty_aux subst pat ty =
    let open Expr in
    match pat, ty with
    | { ty = TyVar v }, _ ->
      begin match Expr.Subst.Id.get v subst with
        | t ->
          if Expr.Ty.equal t ty then subst else raise No_match
        | exception Not_found ->
          Expr.Subst.Id.bind v ty subst
      end
    | { ty = TyApp (id, l) }, { ty = TyApp (id', l') } ->
      if Expr.Id.equal id id' then
        List.fold_left2 ty_aux subst l l'
      else
        raise No_match
    | _ -> raise No_match

  let ty pat ty =
    try
      let res = ty_aux Expr.Subst.empty pat ty in
      Some res
    with No_match ->
      None
end


(* Identifiers used in random terms *)
(* ************************************************************************ *)


module C = struct

  (** Types *)
  let type_a_id = Expr.Id.ty_fun "a" 0
  let type_b_id = Expr.Id.ty_fun "b" 0
  let type_list_id = Expr.Id.ty_fun "list" 1
  let type_pair_id = Expr.Id.ty_fun "pair" 2

  let type_prop = Expr.Ty.prop
  let type_a = Expr.Ty.apply type_a_id []
  let type_b = Expr.Ty.apply type_b_id []
  let mk_list_type a = Expr.Ty.apply type_list_id [a]
  let mk_pair_type a b = Expr.Ty.apply type_pair_id [a; b]

  (** Constants *)
  let a_0 = Expr.Id.term_fun "a_0" [] [] type_a
  let a_1 = Expr.Id.term_fun "a_1" [] [] type_a
  let a_2 = Expr.Id.term_fun "a_2" [] [] type_a

  let f_a = Expr.Id.term_fun "f_a" [] [ type_a ] type_a
  let g_a = Expr.Id.term_fun "g_a" [] [ type_a; type_b] type_a
  let h_a = Expr.Id.term_fun "h_a" [] [ mk_list_type type_a ] type_a

  let b_0 = Expr.Id.term_fun "b_0" [] [] type_b
  let b_1 = Expr.Id.term_fun "b_1" [] [] type_b
  let b_2 = Expr.Id.term_fun "b_2" [] [] type_b

  let f_b = Expr.Id.term_fun "f_b" [] [ type_b ] type_b
  let g_b = Expr.Id.term_fun "g_b" [] [ type_b; type_a ] type_b
  let h_b = Expr.Id.term_fun "h_b" [] [ mk_pair_type type_a type_b ] type_b

  let p_0 = Expr.Id.term_fun "p_0" [] [] type_prop
  let p_1 = Expr.Id.term_fun "p_1" [] [] type_prop
  let p_2 = Expr.Id.term_fun "p_2" [] [] type_prop

  let f_p = Expr.Id.term_fun "f_p" [] [type_a; type_b] type_prop
  let g_p = Expr.Id.term_fun "g_p" [] [mk_list_type type_a] type_prop
  let h_p = Expr.Id.term_fun "h_p" [] [mk_pair_type type_b type_a] type_prop

  let pair =
    let a = Expr.Id.ttype "alpha" in
    let b = Expr.Id.ttype "beta" in
    let t_a = Expr.Ty.of_id a in
    let t_b = Expr.Ty.of_id b in
    Expr.Id.term_fun "pair" [a; b] [t_a; t_b] (mk_pair_type t_a t_b)

  let nil =
    let a = Expr.Id.ttype "alpha" in
    let t_a = Expr.Ty.of_id a in
    Expr.Id.term_fun "nil" [a] [] (mk_list_type t_a)

  let cons =
    let a = Expr.Id.ttype "alpha" in
    let t_a = Expr.Ty.of_id a in
    Expr.Id.term_fun "cons" [a] [t_a; mk_list_type t_a] (mk_list_type t_a)

end

(* Type generation *)
(* ************************************************************************ *)

module Ty = struct

  let print ty =
    Format.asprintf "%a" Expr.Ty.print ty

  let small =
    let rec aux acc = function
    | { Expr.ty = Expr.TyVar _ }
    | { Expr.ty = Expr.TyMeta _ } -> acc + 1
    | { Expr.ty = Expr.TyApp(_, l) } ->
      List.fold_left aux (acc + 1) l
    in
    aux 0

  let shrink = function
    | { Expr.ty = Expr.TyVar _ }
    | { Expr.ty = Expr.TyMeta _ } -> I.empty
    | { Expr.ty = Expr.TyApp(_, l) } -> I.of_list l

  let sized =
    let base = G.oneofl [ C.type_a; C.type_b; C.type_prop; ] in
    G.fix (fun self n ->
        if n = 0 then base
        else begin
          G.frequency [
            3, base;
            1, G.(return C.mk_list_type <*> self (n-1));
            1, G.(return C.mk_pair_type <*> self (n-1) <*> self (n-1));
          ]
        end
      )

  let gen = G.sized sized

  let t = QCheck.make ~print ~small ~shrink gen

end

(* Variable generation *)
(* ************************************************************************ *)

module Var = struct

  module H = Hashtbl.Make(Expr.Ty)

  let num = 10
  let table = H.create 42

  let get ty =
    try H.find table ty
    with Not_found ->
      let a = Array.init num (fun i ->
          Expr.Id.ty (Format.sprintf "v%d" i) ty) in
      H.add table ty a;
      a

  let gen ty =
    G.map (fun i -> (get ty).(i)) G.(0 -- (num - 1))

end

(* Term generation *)
(* ************************************************************************ *)

module Term = struct

  let consts = C.[
      a_0; a_1; a_2; b_0; b_1; b_2;
      f_a; g_a; h_a; f_b; g_b; h_b;
      p_0; p_1; p_2; f_p; g_p; h_p;
      pair; nil; cons;
    ]

  let print t =
    Format.asprintf "%a" Expr.Term.print t

  let small =
    let rec aux acc = function
      | { Expr.term = Expr.Var _ }
      | { Expr.term = Expr.Meta _ } -> acc + 1
      | { Expr.term = Expr.App(_, _, l) } ->
        List.fold_left aux (acc + 1) l
    in
    aux 0

  let rec sub = function
    | { Expr.term = Expr.Var _ }
    | { Expr.term = Expr.Meta _ } -> I.empty
    | { Expr.term = Expr.App(_, _, l) } ->
      let i = I.of_list l in
      I.(append i (i >>= sub))

  let shrink term =
    let aux t = Expr.(Ty.equal term.t_type t.t_type) in
    iter_filter aux (sub term)

  let rec typed ?(ground=true) ty size =
    (** This is used to filter constant that can produce a term
        of the required type [ty]. *)
    let aux c =
      match Match.ty Expr.(c.id_type.fun_ret) ty with
      | None -> None
      | Some subst -> Some (c, subst)
    in
    (** This is used to filter constants base on their arity. Only
        constants with arity > 0 should be considered when [size > 1]. *)
    let score (c, subst) =
      if (size <= 1) then begin
        if List.length Expr.(c.id_type.fun_args) = 0 then
          Some (1, `Cst (c, subst))
        else
          None
      end else begin
        if List.length Expr.(c.id_type.fun_args) > 0 then
          Some (1, `Cst (c, subst))
        else
          None
      end
    in
    (** Apply the above functions *)
    let l1 = CCList.filter_map aux consts in
    assert (l1 <> []);
    let l2 = CCList.filter_map score l1 in
    (** Check wether the last filter was too restrictive. For instance, if [size=0),
        and we need to generate a pair, then the only constructor will ahve arity > 0,
        and thus we need to get it back. *)
    let l3 =
      if l2 <> [] then l2
      else begin
        List.map (fun x -> (1, `Cst x)) l1
      end
    in
    (** Finally, insert the possibility to generate a variable when we want to
        generate a leaf (i.e ground is true, and size <= 1). *)
    let l4 =
      if ground || size > 1 then l3
      else (2, `Var) :: l3
    in
    assert (l4 <> [] && List.for_all (fun (n, _) -> n > 0) l4);
    (** Turn the possibility list into a generator. *)
    G.(frequencyl l4 >>= (fun x ->
        match x with
        | `Var -> Var.gen ty >|= Expr.Term.of_id
        | `Cst (c, subst) ->
          let tys = List.map (fun v -> Expr.Subst.Id.get v subst) Expr.(c.id_type.fun_vars) in
          let args = List.map (Expr.Ty.subst subst) Expr.(c.id_type.fun_args) in
          split (max 0 (size - 1)) (List.length args) >>= fun sizes ->
          sized_list ~ground args sizes >|= (Expr.Term.apply c tys)
      ))

  and sized_list ~ground l sizes =
    match l, sizes with
    | [], [] -> G.return []
    | ty :: r, size :: rest ->
      G.(typed ~ground ty size >>= fun t ->
         sized_list ~ground r rest >|= fun tail ->
         t :: tail)
    | _ -> assert false

  let sized size =
    G.(Ty.sized (min 5 size) >>= fun ty -> typed ty size)

  let gen = G.sized sized

  let t = QCheck.make ~print ~small ~shrink gen

end

(* Formula generation for unification poblems *)
(* ************************************************************************ *)

module Formula = struct

  let print f =
    Format.asprintf "%a" Expr.Formula.print f

  let small =
    let rec aux acc = function
      | { Expr.formula = Expr.True }
      | { Expr.formula = Expr.False } ->
        acc + 1
      | { Expr.formula = Expr.Pred t } ->
        acc + Term.small t
      | { Expr.formula = Expr.Equal (a, b) } ->
        acc + Term.small a + Term.small b
      | { Expr.formula = Expr.Not p } ->
        aux (acc + 1) p
      | { Expr.formula = Expr.Or l }
      | { Expr.formula = Expr.And l } ->
        List.fold_left aux (acc + 1) l
      | { Expr.formula = Expr.Imply (p, q) }
      | { Expr.formula = Expr.Equiv (p, q) } ->
        aux (aux (acc + 1) p) q
      | { Expr.formula = Expr.Ex (l, _, p) }
      | { Expr.formula = Expr.All (l, _, p) } ->
        aux (acc + List.length l) p
      | { Expr.formula = Expr.ExTy (l, _, p) }
      | { Expr.formula = Expr.AllTy (l, _, p) } ->
        aux (acc + List.length l) p
    in
    aux 0

  let rec shrink = function
    | { Expr.formula = Expr.True }
    | { Expr.formula = Expr.False } ->
      I.empty
    | { Expr.formula = Expr.Not p } ->
      I.return p
    | { Expr.formula = Expr.Pred t } ->
      I.map Expr.Formula.pred (Term.shrink t)
    | { Expr.formula = Expr.Equal (a, b) } ->
      I.(pair (Term.shrink a) (Term.shrink b)
         >|= fun (x, y) -> Expr.Formula.eq x y)
    | { Expr.formula = Expr.Or l } ->
      I.(append (of_list l)
           (S.list ~shrink l >|= Expr.Formula.f_or))
    | { Expr.formula = Expr.And l } ->
      I.(append (of_list l)
           (S.list ~shrink l >|= Expr.Formula.f_and))
    | { Expr.formula = Expr.Imply (p, q) } ->
      I.(pair (shrink p) (shrink q)
         >|= fun (x, y) -> Expr.Formula.imply x y)
    | { Expr.formula = Expr.Equiv (p, q) } ->
      I.(pair (shrink p) (shrink q)
         >|= fun (x, y) -> Expr.Formula.equiv x y)
    | { Expr.formula = Expr.Ex (l, _, p) } ->
      I.(shrink p >|= fun q ->
         let _, vars = Expr.Formula.fv q in
         let l' = List.filter (fun x ->
             List.exists (Expr.Id.equal x) vars) l in
         Expr.Formula.ex l' q)
    | { Expr.formula = Expr.All (l, _, p) } ->
      I.(shrink p >|= fun q ->
         let _, vars = Expr.Formula.fv q in
         let l' = List.filter (fun x ->
             List.exists (Expr.Id.equal x) vars) l in
         Expr.Formula.all l' q)
    | { Expr.formula = Expr.ExTy (l, _, p) } ->
      I.(shrink p >|= fun q ->
         let vars, _ = Expr.Formula.fv q in
         let l' = List.filter (fun x ->
             List.exists (Expr.Id.equal x) vars) l in
         Expr.Formula.exty l' q)
    | { Expr.formula = Expr.AllTy (l, _, p) } ->
      I.(shrink p >|= fun q ->
         let vars, _ = Expr.Formula.fv q in
         let l' = List.filter (fun x ->
             List.exists (Expr.Id.equal x) vars) l in
         Expr.Formula.allty l' q)

  let pred ?ground size =
    G.(return Expr.Formula.pred <*>
       (Term.typed ?ground Expr.Ty.prop size))

  let eq ?ground size =
    G.(split_int size >>= fun (a, b) ->
       Ty.sized (min 5 size) >>= fun ty ->
       return Expr.Formula.eq
       <*> (Term.typed ?ground ty a)
       <*> (Term.typed ?ground ty b)
      )

  let all f =
    let _, vars = Expr.Formula.fv f in
    G.(sublist vars >|= fun l ->
       Expr.Formula.all l f)

  let ex f =
    let _, vars = Expr.Formula.fv f in
    G.(sublist vars >|= fun l ->
       Expr.Formula.ex l f)

  let allty f =
    let vars, _ = Expr.Formula.fv f in
    G.(sublist vars >|= fun l ->
       Expr.Formula.allty l f)

  let exty f =
    let vars, _ = Expr.Formula.fv f in
    G.(sublist vars >|= fun l ->
       Expr.Formula.exty l f)

  let sized_free_aux ?ground = fun self n ->
    if n = 0 then
      G.frequency [
        1, G.return Expr.Formula.f_true;
        1, G.return Expr.Formula.f_false;
      ]
    else
      G.frequency [
        2, eq ?ground (n - 1);
        3, pred ?ground (n - 1);
        1, G.(return Expr.Formula.neg <*> self (n-1));
        1, G.(split_int (n-1) >>= fun (a, b) ->
              self a >>= fun p -> self b >>= fun q ->
              return @@ Expr.Formula.f_and [p; q]);
        1, G.(split_int (n-1) >>= fun (a, b) ->
              self a >>= fun p -> self b >>= fun q ->
              return @@ Expr.Formula.f_or [p; q]);
        1, G.(split_int (n-1) >>= fun (a, b) ->
              return Expr.Formula.imply <*> self a <*> self b);
        1, G.(split_int (n-1) >>= fun (a, b) ->
              return Expr.Formula.equiv <*> self a <*> self b);
      ]

  let sized_free ?ground = G.fix sized_free_aux

  let sized_closed_aux =
    G.fix (fun self n ->
        if n = 0 then sized_free_aux ~ground:true self n
        else
          G.frequency [
            5, sized_free_aux ~ground:false self n;
            1, G.(self (n-1) >>= ex);
            1, G.(self (n-1) >>= all);
            1, G.(self (n-1) >>= exty);
            1, G.(self (n-1) >>= allty);
          ]
      )

  let sized_closed size =
    G.(sized_closed_aux size >|= (fun f ->
        let tys, vars = Expr.Formula.fv f in
        Expr.Formula.allty tys (Expr.Formula.all vars f)))

  let sized = sized_closed

  let gen = G.sized sized

  let t = QCheck.make ~print ~small ~shrink gen

  let meta gen size =
    G.(gen size >|= fun f ->
       let tys, l = Expr.Formula.fv f in
       assert (tys = []);
       match Expr.Formula.all l f with
       | { Expr.formula = Expr.All (vars, _, _) } as q_f ->
         let metas = List.map Expr.Term.of_meta (Expr.Meta.of_all q_f) in
         let subst = List.fold_left2 (fun s v t -> Expr.Subst.Id.bind v t s)
             Expr.Subst.empty vars metas in
         Expr.Formula.subst Expr.Subst.empty subst f
       | _ -> f)

end


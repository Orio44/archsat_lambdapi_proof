
let section = Section.make "proof"

(* Proof environments *)
(* ************************************************************************ *)

module Env = struct

  exception Added_twice of Term.t
  exception Not_introduced of Term.t

  let () =
    Printexc.register_printer (function
        | Added_twice f ->
          Some (Format.asprintf
                  "Following formula has been added twice to context:@ %a"
                  Term.print f)
        | Not_introduced f ->
          Some (Format.asprintf
                  "Following formula is used in a context where it is not declared:@ %a"
                  Term.print f)
        | _ -> None
      )

  module Mt = Map.Make(Term)
  module Ms = Map.Make(String)

  type t = {
    (** Bindings *)
    names : Term.id Mt.t; (** local bindings *)
    global : Term.id Mt.t; (** global bindings *)
    reverse : (Term.id, unit) Term.S.t; (** Set of ids present that are bound *)

    (** Options for nice names *)
    prefix : string;  (** current prefix *)
    count : int Ms.t; (** use count for each prefix *)
  }

  let print_aux fmt (t, id) =
    Format.fprintf fmt "%a (%d): @[<hov>%a@]" Expr.Print.id id (Term.hash t) Term.print t

  let bindings t =
    let l = Mt.bindings t.names in
    let l = List.sort (fun (_, x) (_, y) ->
        compare x.Expr.id_name y.Expr.id_name) l in
    let l' = Mt.bindings t.global in
    let l' = List.sort (fun (_, x) (_, y) ->
        compare x.Expr.id_name y.Expr.id_name) l' in
    l @ l'

  let print fmt t =
    CCFormat.(vbox @@ list ~sep:(return "@ ") print_aux) fmt (bindings t)

  let empty = {
    names = Mt.empty;
    global = Mt.empty;
    reverse = Term.S.empty;
    prefix = "";
    count = Ms.empty;
  }

  let prefix t s =
    { t with prefix = s }

  let mem t id = Term.S.Id.mem id t.reverse

  let find t f =
    try Mt.find f t.names
    with Not_found ->
      begin try
          Mt.find f t.global
        with Not_found ->
          raise (Not_introduced f)
      end

  let local_count t s =
    try Ms.find s t.count with Not_found -> 0

  let add t id =
    let f = id.Expr.id_type in
    match Mt.find f t.names with
    | name -> raise (Added_twice f)
    | exception Not_found ->
      { t with names = Mt.add f id t.names;
               reverse = Term.S.Id.bind t.reverse id (); }

  let intro t f =
    match Mt.find f t.names with
    | name -> raise (Added_twice f)
    | exception Not_found ->
      let n = local_count t t.prefix in
      let name = Format.sprintf "%s%d" t.prefix n in
      let id = Term.var name f in
      { t with names = Mt.add f id t.names;
               count = Ms.add t.prefix (n + 1) t.count;
               reverse = Term.S.Id.bind t.reverse id (); }

  let declare t id =
    assert (not (Term.is_var id));
    { t with global = Mt.add id.Expr.id_type id t.global;
             reverse = Term.S.Id.bind t.reverse id (); }

  let count t = Mt.cardinal t.names + Mt.cardinal t.global

  let strip t = { empty with global = t.global }

end

(* Proof preludes *)
(* ************************************************************************ *)

module Prelude = struct

  let section = Section.make ~parent:section "prelude"

  module Aux = struct

    type t =
      | Require of unit Expr.id
      | Alias of Term.id * Term.t

    let _discr = function
      | Require _ -> 0
      | Alias _ -> 1

    let hash_aux t id =
      CCHash.(pair int Expr.Id.hash) (_discr t, id)

    let hash t =
      match t with
      | Require id -> hash_aux t id
      | Alias (id, _) -> hash_aux t id

    let compare t t' =
      match t, t' with
      | Require v, Require v' -> Expr.Id.compare v v'
      | Alias (v, e), Alias (v', e') ->
        let res = Expr.Id.compare v v' in
        if res = 0 then assert (Term.equal e e');
        res
      | _ -> Pervasives.compare (_discr t) (_discr t')

    let equal t t' = compare t t' = 0

    let print fmt = function
      | Require id ->
        Format.fprintf fmt "require: %a" Expr.Id.print id
      | Alias (v, t) ->
        Format.fprintf fmt "alias: %a ->@ %a" Expr.Print.id v Term.print t

  end

  include Aux

  module S = Set.Make(Aux)
  module G = Graph.Imperative.Digraph.Concrete(Aux)
  module T = Graph.Topological.Make_stable(G)
  module O = Graph.Oper.I(G)

  let dep_graph = G.create ()

  let mk ~deps t =
    let () = G.add_vertex dep_graph t in
    let () = List.iter (fun x ->
        Util.debug ~section "%a ---> %a" print x print t;
        G.add_edge dep_graph x t) deps in
    t

  let require ?(deps=[]) s = mk ~deps (Require s)
  let alias ?(deps=[]) id t = mk ~deps (Alias (id, t))

  let topo l iter =
    let s = List.fold_left (fun s x -> S.add x s) S.empty l in
    let _ = O.add_transitive_closure ~reflexive:true dep_graph in
    T.iter (fun v -> if S.exists (G.mem_edge dep_graph v) s then iter v) dep_graph

end

(* Proof printing data *)
(* ************************************************************************ *)

type lang =
  | Dot     (**)
  | Coq     (**)
(* Proof languages supported. *)

type pretty =
  | Branching           (* All branches are equivalent *)
  | Last_but_not_least  (* Last branch is the 'rest of the proof *)
(** Pretty pinting information to know better how to print proofs.
    For instance, 'split's would probably be [Branching], while
    cut/pose proof, would preferably be [Last_but_not_least]. *)

(* Proofs *)
(* ************************************************************************ *)

type sequent = {
  env : Env.t;
  goal : Term.t;
}

type ('input, 'state) step = {

  (* step name *)
  name : string;

  (* Printing information *)
  print : lang ->
    pretty * (Format.formatter -> 'state -> unit);

  (* Semantics *)
  compute   : sequent -> 'input -> 'state * sequent array;
  prelude   : 'state -> Prelude.t list;
  elaborate : 'state -> Term.t array -> Term.t;
}


type node = {
  id : int;
  pos : pos;
  proof : proof_node;
}

and pos = node array * int

and proof_node =
  | Open  : sequent -> proof_node
  | Proof : (_, 'state) step * 'state * node array -> proof_node

(* Alias for proof *)
type proof = sequent * node array
(** Simpler option would be a node ref, but it would complexify functions
    and positions neddlessly. *)


(* Proof tactics *)
type ('a, 'b) tactic = 'a -> 'b
(** The type of tactics. Should represent computations that manipulate
    proof positions. Using input ['a] and output ['b].

    Most proof tactics should take a [pos] as input, and return:
    - [unit] if it closes the branch
    - a single [pos] it it does not create multple branches
    - a tuple, list or array of [pos] if it branches
*)

exception Open_proof
(** Raised by functions that encounter an unexpected open proof. *)

(* Sequents *)
(* ************************************************************************ *)

let env { env; _ } = env
let goal { goal; _ } = goal
let mk_sequent env goal = Env.{ env; goal; }

let print_sequent fmt sequent =
  Format.fprintf fmt
    "@[<hv 2>sequent:@ @[<hv 2>env:@ @[<v>%a@]@] @[<hv 2>goal:@ @[<hov>%a@]@]@]"
    Env.print sequent.env Term.print sequent.goal

(* Failure *)
(* ************************************************************************ *)

exception Failure of string * sequent

let () = Printexc.register_printer (function
    | Failure (msg, sequent) ->
      Some (Format.asprintf "@[<hv>In context:@ %a@ %s@]" print_sequent sequent msg)
    | _ -> None)

(* Steps *)
(* ************************************************************************ *)

let _prelude _ = []

let _dummy_dot_print = Branching, (fun fmt _ -> Format.fprintf fmt "N/A")

let mk_step ?(prelude=_prelude) ?(dot=_dummy_dot_print) ~coq ~compute ~elaborate name =
  { name ;prelude; compute; elaborate;
    print = (function Dot -> dot | Coq -> coq); }

(* Building proofs *)
(* ************************************************************************ *)

let _node_idx = ref 0

let get ((t, i) : pos) = t.(i)

let set ((t, i) as pos : pos) step state branches =
  match (get pos).proof with
  | Open _ ->
    incr _node_idx;
    t.(i) <- { id = !_node_idx; pos; proof = Proof (step, state, branches); }
  | Proof _ ->
    Util.error ~section "Trying to apply reasonning step to an aleardy closed proof";
    assert false

let dummy_node = {
  id = 0; pos = [| |], -1;
  proof = Open (mk_sequent Env.empty Term.true_term);
}

let mk_branches n f =
  let res = Array.make n dummy_node in
  for i = 0 to n - 1 do
    let pos = (res, i) in
    incr _node_idx;
    res.(i) <- { id = !_node_idx; pos; proof = f i; }
  done;
  res

let mk sequent =
  sequent, mk_branches 1 (fun _ -> Open sequent)

let apply_step pos step input =
  match (get pos).proof with
  | Proof _ ->
    Util.error ~section "Trying to apply reasonning step to an aleardy closed proof";
    assert false
  | Open sequent ->
    let state, a = step.compute sequent input in
    let branches = mk_branches (Array.length a) (fun i -> Open a.(i)) in
    let () = set pos step state branches in
    state, Array.map (fun { pos; _} -> pos) branches

(* Printing Dot proofs *)
(* ************************************************************************ *)

let print_hyp_dot fmt (t, v) =
  Format.fprintf fmt "<TD>%a</TD><TD>%a</TD>"
    Dot.Print.Proof.id v (Dot.box Dot.Print.Proof.term) t

let print_hyp_line fmt (t, v) =
  Format.fprintf fmt "<TR>%a</TR>" print_hyp_dot (t, v)

let print_sequent_dot fmt (s, color, seq) =
  Format.fprintf fmt "<TR><TD BGCOLOR=\"YELLOW\" colspan=\"3\">%a</TD></TR>"
    (Dot.box Dot.Print.Proof.term) (goal seq);
  match Env.bindings (env seq) with
  | [] -> Format.fprintf fmt "<TR><TD BGCOLOR=\"%s\" colspan=\"3\">%s</TD></TR>" color s
  | h :: r ->
    Format.fprintf fmt
      "<TR><TD BGCOLOR=\"%s\" rowspan=\"%d\">%s</TD>%a</TR>"
      color (List.length r + 1) s print_hyp_dot h;
    List.iter (print_hyp_line fmt) r

let print_step_dot fmt (s, st) =
  let _, pp = s.print Dot in
  Format.fprintf fmt "<TR><TD>%s</TD><TD>%a</TD></TR>" s.name pp st

let print_dot_id fmt { id; _ } =
  Format.fprintf fmt "node_%d" id

let print_table_options fmt color =
  Format.fprintf fmt
    "BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" BGCOLOR=\"%s\"" color

let print_edge src fmt dst =
  Format.fprintf fmt "%a -> %a;@\n"
    print_dot_id src print_dot_id dst

let print_edges src fmt a =
  Array.iter (print_edge src fmt) a

let rec print_node_dot fmt node =
  match node.proof with
  | Open s ->
    Format.fprintf fmt
      "%a [shape=plaintext, label=<<TABLE %a>%a</TABLE>>];@\n"
      print_dot_id node
      print_table_options "LIGHTBLUE"
      print_sequent_dot ("OPEN", "RED", s)
  | Proof (s, st, br) ->
    Format.fprintf fmt
      "%a [shape=plaintext, label=<<TABLE %a>%a</TABLE>>];@\n"
      print_dot_id node
      print_table_options "LIGHTBLUE"
      print_step_dot (s, st);
    let () = print_edges node fmt br in
    Array.iter (print_node_dot fmt) br

let print_root fmt (seq, node) =
  Format.fprintf fmt
    "root [shape=plaintext, label=<<TABLE %a>%a</TABLE>>];@\n"
    print_table_options "LIGHTBLUE"
    print_sequent_dot ("ROOT", "PURPLE", seq);
  Format.fprintf fmt "root -> %a;@\n" print_dot_id node;
  print_node_dot fmt node

let print_dot fmt root =
  Format.fprintf fmt "digraph proof {@\n%a}@." print_root root

(* Printing Coq proofs *)
(* ************************************************************************ *)

let bullet_list = [ '-'; '+' ]
let bullet_n = List.length bullet_list

let bullet depth =
  let k = depth mod bullet_n in
  let n = depth / bullet_n + 1 in
  let c = List.nth bullet_list k in
  String.make n c

let rec print_branching_coq ~depth fmt t =
  Format.fprintf fmt "%s @[<hov>%a@]"
    (bullet depth) (print_node_coq ~depth:(depth + 1)) t

and print_bracketed_coq ~depth fmt t =
  Format.fprintf fmt "{ @[<hov>%a@] }" (print_node_coq ~depth) t

and print_lbnl_coq ~depth fmt t =
  print_node_coq ~depth fmt t

and print_array_coq ~depth ~pretty fmt a =
  match a with
  | [| |] -> ()
  | [| x |] -> print_node_coq ~depth fmt x
  | _ ->
    begin match pretty with
      | Branching ->
        Format.fprintf fmt "@[<v>%a@]"
          CCFormat.(array ~sep:(return "@ ") (print_branching_coq ~depth)) a
      | Last_but_not_least ->
        let a' = Array.sub a 0 (Array.length a - 1) in
        Format.fprintf fmt "@[<v>%a@ @]"
          CCFormat.(array ~sep:(return "@ ") (print_bracketed_coq ~depth)) a';
        (* separate call to ensure tail call, useful for long proofs *)
        print_lbnl_coq ~depth fmt a.(Array.length a - 1)
    end

and print_proof_node_coq ~depth fmt = function
  | Open _ -> raise Open_proof
  | Proof (step, state, branches) ->
    let pretty, pp = step.print Coq in
    Format.fprintf fmt "@[<hov 2>%a@]" pp state;
    print_array_coq ~depth ~pretty fmt branches

and print_node_coq ~depth fmt { proof; _ } =
  print_proof_node_coq ~depth fmt proof

let print_coq fmt (_, p) = print_node_coq ~depth:0 fmt p

(* Printing proofs *)
(* ************************************************************************ *)

let print ~lang fmt = function
  | seq, [| p |] ->
    begin match lang with
      | Dot -> print_dot fmt (seq, p)
      | Coq -> print_coq fmt (seq, p)
    end
  | _ -> assert false

(* Inspecting proofs *)
(* ************************************************************************ *)

let root = function
  | _, [| p |] -> p
  | _ -> assert false

let pos { pos; _ } = pos

let extract { proof; _ } = proof

let branches node =
  match node.proof with
  | Open _ -> raise Open_proof
  | Proof (_, _, branches) -> branches

(* Proof elaboration *)
(* ************************************************************************ *)

let rec elaborate_array_aux k a res i =
  if i >= Array.length a then k res
  else
    elaborate_node (fun x ->
        res.(i) <- x;
        elaborate_array_aux k a res (i + 1)) a.(i)

and elaborate_array k a =
  let res = Array.make (Array.length a) Term._Type in
  elaborate_array_aux k a res 0

and elaborate_proof_node k = function
  | Open _ -> raise Open_proof
  | Proof (step, state, branches) ->
    elaborate_array (fun args -> k @@ step.elaborate state args) branches

and elaborate_node k { proof; _ } =
  elaborate_proof_node k proof

let elaborate = function
  | _, [| p |] -> elaborate_node (fun x -> x) p
  | _ -> assert false

(* Match an arrow type *)
(* ************************************************************************ *)

let match_arrow ty =
  match Term.reduce ty with
  | { Term.term = Term.Binder (Term.Forall, v, ret) }
    when not (Term.occurs v ret) ->
    Some (v.Expr.id_type, ret)
  | _ -> None

let match_arrows ty =
  let rec aux acc t =
    match match_arrow t with
    | Some (arg, ret) -> aux (arg :: acc) ret
    | None -> List.rev acc, t
  in
  aux [] ty

let rec match_n_arrow acc n ty =
  if n <= 0 then Some (List.rev acc, ty)
  else begin
    match match_arrow ty with
    | None -> None
    | Some (arg_ty, ret) -> match_n_arrow (arg_ty :: acc) (n - 1) ret
  end

(* Proof steps *)
(* ************************************************************************ *)

let apply =
  let prelude (_, _, l) = l in
  let compute ctx (f, n, prelude) =
    let g = goal ctx in
    match match_n_arrow [] n f.Term.ty with
    | None ->
      Util.warn ~section
        "@[<hv 2>Expected a non-dependant product type but got:@ %a@]"
        Term.print f.Term.ty;
      assert false
    | Some (l, ret) ->
      (** Ceck that the application proves the current goal *)
      if not (Term.equal ret g) then
        raise (Failure (
            Format.asprintf "@[<hv>Couldn't apply@ %a:@  @[<hov>%a@]@]"
              Term.print f Term.print f.Term.ty, ctx));
      let e = env ctx in
      (** Check that the term used in closed in the current environment *)
      let unbound_vars = Term.S.fold (fun id () acc ->
          if not (Env.mem e id) then id :: acc else acc
        ) (Term.free_vars f) [] in
      begin match unbound_vars with
      | [] -> (* Everything is good, let's proceed *)
        (f, n, prelude), Array.map (fun g' -> mk_sequent e g') (Array.of_list l)
      | l -> (** Some variables are unbound, complain about them loudly *)
        raise (Failure (
            Format.asprintf
              "@[<hv>The variables@ @[<hov>[%a]@]@ are free in@ %a@ this is not allowed"
              CCFormat.(list ~sep:(return ";@ ") Expr.Id.print) l Term.print f, ctx))
      end
  in
  let elaborate (f, _, _) args = Term.apply f (Array.to_list args) in
  let coq = Branching, (fun fmt (f, n, _) ->
      Format.fprintf fmt "%s %a."
        (if n = 0 then "exact" else "apply") Coq.Print.term f
    ) in
  let dot = Branching, Dot.box (fun fmt (f, n, _) ->
      Format.fprintf fmt "%a" Dot.Print.Proof.term f
    ) in
  mk_step ~prelude ~dot ~coq ~compute ~elaborate "apply"

let intro =
  let prelude _ = [] in
  let compute ctx prefix =
    match Term.reduce @@ goal ctx with
    | { Term.term = Term.Binder (Term.Forall, v (* : p *), q) } ->
      if Term.occurs v q then begin
        v, [| mk_sequent (env ctx) q |]
      end else begin
        let p = v.Expr.id_type in
        let e = Env.intro (Env.prefix (env ctx) prefix) p in
        Env.find e p, [| mk_sequent e q |]
      end
    | t ->
      Util.warn ~section "Expected a universal quantification, but got: %a"
        Term.print t;
      raise (Failure ("Can't introduce formula", ctx))
  in
  let elaborate id = function
    | [| body |] -> Term.lambda id body
    | _ -> assert false
  in
  let coq = Last_but_not_least, (fun fmt p ->
      Format.fprintf fmt "intro %a." Coq.Print.id p
    ) in
  let dot = Branching, Dot.box (fun fmt p ->
      Format.fprintf fmt "%a: @[<hov>%a@]"
        Dot.Print.Proof.id p Dot.Print.Proof.term p.Expr.id_type
    ) in
  mk_step ~prelude ~dot ~coq ~compute ~elaborate "intro"

let letin =
  let prelude _ = [] in
  let compute ctx (prefix, t) =
    let e = Env.prefix (env ctx) prefix in
    let e' = Env.intro e t.Term.ty in
    (Env.find e' t, t), [| mk_sequent e' (goal ctx) |]
  in
  let elaborate (id, t) = function
    | [| body |] -> Term.letin id t body
    | _ -> assert false
  in
  let coq = Last_but_not_least, (fun fmt (id, t) ->
      Format.fprintf fmt "@[<hv 2>pose proof (@,%a@;<0,-2>) as %a.@]"
        Coq.Print.term t Coq.Print.id id
    ) in
  let dot = Branching, Dot.box (fun fmt (id, t) ->
      Format.fprintf fmt "%a = @[<hov>%a@]"
        Dot.Print.Proof.id id Dot.Print.Proof.term t
    ) in
  mk_step ~prelude ~dot ~coq ~compute ~elaborate "letin"

let cut =
  let prelude _ = [] in
  let compute ctx (keep_env, prefix, t) =
    let e = env ctx in
    let e' = Env.prefix e prefix in
    let e'' = Env.intro e' t in
    let e_cut = if keep_env then e else Env.strip e in
    Env.find e'' t, [| mk_sequent e_cut t ; mk_sequent e'' (goal ctx) |]
  in
  let elaborate id = function
    | [| t; body |] -> Term.letin id t body
    | _ -> assert false
  in
  let coq = Last_but_not_least, (fun fmt id ->
      Format.fprintf fmt "assert (%a:@ @[<hov>%a@])."
        Coq.Print.id id Coq.Print.term id.Expr.id_type
    ) in
  let dot = Branching, Dot.box (fun fmt id ->
      Format.fprintf fmt "%a = @[<hov>%a@]"
        Dot.Print.Proof.id id Dot.Print.Proof.term id.Expr.id_type
    ) in
  mk_step ~prelude ~dot ~coq ~compute ~elaborate "cut"



let section = Section.make ~parent:Dispatcher.section "logic"

(* Module aliases & initialization *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Formula)

type info =
  | True

  | And of Expr.formula * Expr.formula
  | Not_or of Expr.formula * Expr.formula

  | Or of Expr.formula * Expr.formula list
  | Not_and of Expr.formula * Expr.formula list

  | Imply of Expr.formula
             * Expr.formula * Expr.formula list
             * Expr.formula * Expr.formula list

  | Not_imply_left of Expr.formula
  | Not_imply_right of Expr.formula

  | Equiv_right of Expr.formula
  | Equiv_left of Expr.formula

  | Not_equiv of Expr.formula

type Dispatcher.lemma_info += Logic of info

let st = H.create 1024

(* Small wrappers *)
(* ************************************************************************ *)

let push name info l =
  Dispatcher.push l (Dispatcher.mk_proof "logic" name (Logic info))

let push_and r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_false) l then
    push "and" (And (r, Expr.Formula.f_false))
      [Expr.Formula.neg r; Expr.Formula.f_false]
  else
    List.iter (fun p -> push "and" (And (r, p)) [Expr.Formula.neg r; p]) l

let push_not_or r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_true) l then
    push "not-or" (Not_or (r, Expr.Formula.f_false))
      [ r; Expr.Formula.f_false ]
  else
    List.iter (fun p -> push "not-or" (Not_or (r, p)) [r; Expr.Formula.neg p]) l

let push_or r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_true) l then
    () (* clause is trivially true *)
  else
    push "or" (Or (r, l)) (Expr.Formula.neg r :: l)

let push_not_and r l =
  if List.exists (Expr.Formula.equal Expr.Formula.f_false) l then
    () (* clause is trivially true *)
  else
    push "not-and" (Not_and (r, l)) (r :: List.rev_map Expr.Formula.neg l)

let imply_left p =
  List.map Expr.Formula.neg @@
  match p with
  | { Expr.formula = Expr.And l } -> l
  | p -> [p]

let imply_right = function
  | { Expr.formula = Expr.Or l } -> l
  | q -> [q]


(* Main function *)
(* ************************************************************************ *)

let tab = function
  (* 'True/False' traduction *)
  | { Expr.formula = Expr.False } ->
    raise (Dispatcher.Absurd
             ([Expr.Formula.f_true],
              Dispatcher.mk_proof "logic" "true" (Logic True)))

  (* 'And' traduction *)
  | { Expr.formula = Expr.And l } as r ->
    push_and r l
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.And l } as r) } ->
    push_not_and r l

  (* 'Or' traduction *)
  | { Expr.formula = Expr.Or l } as r ->
    push_or r l
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Or l } as r) } ->
    push_not_or r l

  (* 'Imply' traduction *)
  | { Expr.formula = Expr.Imply (p, q) } as r ->
    let left = imply_left p in
    let right = imply_right q in
    push "imply" (Imply (r, p, left, q, right)) (Expr.Formula.neg r :: (left @ right))
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Imply (p, q) } as r )  } ->
    push "not-imply_l" (Not_imply_left r) [r; p];
    push "not-imply_r" (Not_imply_right r) [r; Expr.Formula.neg q]

  (* 'Equiv' traduction *)
  | { Expr.formula = Expr.Equiv (p, q) } as r ->
    push "equiv" (Equiv_right r) [Expr.Formula.neg r; Expr.Formula.imply p q];
    push "equiv" (Equiv_left r) [Expr.Formula.neg r; Expr.Formula.imply q p]
  | { Expr.formula = Expr.Not ({ Expr.formula = Expr.Equiv (p, q) } as r )  } ->
    push "not-equiv" (Not_equiv r)
      [r; Expr.Formula.f_and [p; Expr.Formula.neg q]; Expr.Formula.f_and [Expr.Formula.neg p; q] ]

  (* Other formulas (not treated) *)
  | _ -> ()

let tab_assume f =
    if not (H.mem st f) then begin
      tab f;
      H.add st f true
    end

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | True -> None, []

  | And (t, t') ->
    Some "LIGHTBLUE", List.map (CCFormat.const Dot.Print.formula) [t; t']
  | Not_or (t, t') ->
    Some "LIGHTBLUE", List.map (CCFormat.const Dot.Print.formula) [t; t']

  | Or (f, _)
  | Not_and (f, _)
  | Imply (f, _, _, _, _)
  | Not_imply_left f
  | Not_imply_right f
  | Equiv_right f
  | Equiv_left f
  | Not_equiv f ->
    Some "LIGHTBLUE", [CCFormat.const Dot.Print.formula f]

let coq_imply_left_aux fmt (indent, (i, n)) =
  Util.debug ~section "coq_imply_left_aux (%d, (%d, %d))" indent n i;
  Format.fprintf fmt "%s %a. exact R."
    (String.make indent '+')
    Coq.Print.path (i, n)

let rec coq_imply_left fmt (total, n, i) =
  if n = 2 then
    Format.fprintf fmt "@[<v 2>%s destruct (%s _ _ T%d) as [R | R].@ %a@ %a@]"
      (if i = 0 then "-" else String.make i '+')
      "Coq.Logic.Classical_Prop.not_and_or" i
      coq_imply_left_aux (i + 1, (i + 1, total))
      coq_imply_left_aux (i + 1, (i + 2, total))
  else (* n > 2 *)
    Format.fprintf fmt "@[<v 2>%s destruct (%s _ _ T%d) as [R | T%d].@ %a@ %a@]"
      (if i = 0 then "-" else String.make i '+')
      "Coq.Logic.Classical_Prop.not_and_or" i (i + 1)
      coq_imply_left_aux (i + 1, (i + 1, total))
      coq_imply_left (total, n - 1, i + 1)

let rec coq_imply_right fmt (n, i) =
  if i > n then ()
  else begin
    Format.fprintf fmt "- %a. exact R.@ " Coq.Print.path (i, n);
    coq_imply_right fmt (n, i + 1)
  end

let coq_proof = function
  | True -> Coq.Raw (CCFormat.return "exact I.")

  | And (init, res) ->
    Coq.(Implication {
        left = [init];
        right = [res];
        prefix = "H";
        proof = (fun fmt m ->
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "destruct %s as %a; exact %s."
              (Coq.M.find init m)
              (Coq.Print.pattern_and (fun fmt f ->
                   if Expr.Formula.equal f res
                   then Format.fprintf fmt "F"
                   else Format.fprintf fmt "_")) order
              "F"
          );
      })
  | Not_or (init, res) ->
    Coq.(Implication {
        left = [res];
        right = [init];
        prefix = "H";
        proof = (fun fmt m ->
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "%a.@ exact %s."
              Coq.Print.path_to (res, order) (Coq.M.find res m)
          )
      })

  | Or (init, l) ->
    Coq.(Implication {
        left = [init];
        right = l;
        prefix = "H";
        proof = (fun fmt m ->
            let n = List.length l in
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "destruct %s as %a.@\n@[<hv>%a@]"
              (M.find init m)
              (Print.pattern_or (fun fmt f -> Format.fprintf fmt "F")) order
            (fun fmt -> List.iteri (fun i _ ->
                  Format.fprintf fmt "@[<hov 2>- %a.@ exact F.@]@ "
                    Print.path (i + 1, n))) l
          )
      })
  | Not_and (init, l) ->
    Coq.(Implication {
        left = l;
        right = [init];
        prefix = "H";
        proof = (fun fmt m ->
            let aux fmt f = Format.fprintf fmt "%s" (M.find f m) in
            let order = CCOpt.get_exn (Expr.Formula.get_tag init Expr.f_order) in
            Format.fprintf fmt "exact @[<hov>%a@]." (Print.pattern_intro_and aux) order
          )
      })

  | Imply (init, _, [p], _, [q]) ->
    Coq.(Ordered {
        order = [Expr.Formula.neg init; p; q];
        proof = (fun fmt () ->
            Format.fprintf fmt "apply Coq.Logic.Classical_Prop.imply_to_or.@ ";
            Format.fprintf fmt "apply Coq.Logic.Classical_Prop.imply_to_or."
          );
      })
  | Imply (init, p, lp, q, lq) ->
    Coq.(Implication {
        left = [init];
        right = lp @ lq;
        prefix = "H";
        proof = (fun fmt m ->
            let np = List.length lp in
            let nq = List.length lq in
            let order_right = CCOpt.get_exn (Expr.Formula.get_tag q Expr.f_order) in
            Format.fprintf fmt
              "destruct (Coq.Logic.Classical_Prop.imply_to_or _ _ %s) as [T0 | %a].@\n"
              (Coq.M.find init m)
              (Coq.Print.pattern_or (fun fmt _ -> Format.fprintf fmt "R")) order_right;
            Format.fprintf fmt "@[<v>%a@ %a@]"
              coq_imply_left (np + nq, np, 0) coq_imply_right (np + nq, np + 1)
          )
      })
  | _ -> Coq.Raw (fun fmt () ->
      Format.fprintf fmt "tauto.")

(* Handle & plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Logic info -> Some (dot_info info)
  | Coq.Prove Logic info -> Some(coq_proof info)
  | _ -> None

let register () =
  Dispatcher.Plugin.register "logic"
    ~descr:"Does lazy cnf conversion on input formulas whose top constructor is a logical connective
          (i.e quantified formulas are $(b,not) handled by this plugin)."
    (Dispatcher.mk_ext ~handle:{Dispatcher.handle} ~section ~assume:tab_assume ())


require open Logic.Zenon.FOL Logic.Zenon.zen lambdapi_static.lp_logic;


symbol true_intro : ϵ ⊤ ≔ λ (p : Prop), λ (x : ϵ p), x;
symbol false_elim (p : Prop) : ϵ ⊥ → ϵ p
  ≔ λ (H : ϵ ⊥), H p;
symbol and_intro (p : Prop) (q : Prop)
  : ϵ p → ϵ q → ϵ (@∧ p q) ≔ and_intro p q;
symbol and_ind (p : Prop) (q : Prop) (r : Prop)
  : (ϵ p → ϵ q → ϵ r) → ϵ (@∧ p q) → ϵ r
  ≔ λ (f : ϵ p → ϵ q → ϵ r),
        λ (H : ϵ (@∧ p q)), H r f;
symbol and_elim (p : Prop) (q : Prop) (r : Prop)
  : ϵ (@∧ p q) → (ϵ p → ϵ q → ϵ r) → ϵ r
  ≔ λ (H : ϵ (@∧ p q)),
        λ (f : ϵ p → ϵ q → ϵ r), H r f;
symbol or_introl (p : Prop) (q : Prop) : ϵ p → ϵ (@∨ p q)
  ≔ λ (H1 : ϵ p),
        λ (z : Prop),
          λ (H2 : ϵ p → ϵ z), λ (H3 : ϵ q → ϵ z), H2 H1;
symbol or_intror (p : Prop) (q : Prop) : ϵ q → ϵ (@∨ p q)
  ≔ λ (H1 : ϵ q),
        λ (z : Prop),
          λ (H2 : ϵ p → ϵ z), λ (H3 : ϵ q → ϵ z), H3 H1;
symbol or_ind (p : Prop) (q : Prop) (r : Prop)
  : (ϵ p → ϵ r)
    → (ϵ q → ϵ r) → ϵ (@∨ p q) → ϵ r
  ≔ λ (f : ϵ p → ϵ r),
        λ (g : ϵ q → ϵ r), λ (H : ϵ (@∨ p q)), H r f g;
symbol or_elim (p : Prop) (q : Prop) (r : Prop)
  : ϵ (@∨ p q)
    → (ϵ p → ϵ r) → (ϵ q → ϵ r) → ϵ r
  ≔ λ (H : ϵ (@∨ p q)),
        λ (f : ϵ p → ϵ r), λ (g : ϵ q → ϵ r), H r f g;
symbol equiv_refl (p : Prop) : ϵ (@⇔ p p)
  ≔ and_intro (@⇒  p p) (@⇒  p p) (λ (x : ϵ p), x)
      (λ (x : ϵ p), x);
symbol equiv_trans (p : Prop) (q : Prop) (r : Prop)
  : ϵ (@⇔ p q) → ϵ (@⇔ q r) → ϵ (@⇔ p r)
  ≔ λ (H1 : ϵ (@⇔ p q)),
        λ (H2 : ϵ (@⇔ q r)),
          and_intro (@⇒  p r) (@⇒  r p)
          (λ (x : ϵ p),
             and_elim (@⇒  p q) (@⇒  q p) r H1
             (λ (pq : ϵ (@⇒  p q)),
                λ (_ : ϵ (@⇒  q p)),
                  and_elim (@⇒  q r) (@⇒  r q) r H2
                  (λ (qr : ϵ (@⇒  q r)),
                     λ (_ : ϵ (@⇒  r q)), qr (pq x))))
          (λ (x : ϵ r),
             and_elim (@⇒  p q) (@⇒  q p) p H1
             (λ (_ : ϵ (@⇒  p q)),
                λ (qp : ϵ (@⇒  q p)),
                  and_elim (@⇒  q r) (@⇒  r q) p H2
                  (λ (_ : ϵ (@⇒  q r)),
                     λ (rq : ϵ (@⇒  r q)), qp (rq x))));
symbol equiv_not (p : Prop) (q : Prop)
  : ϵ (@⇔ p q) → ϵ (@⇔ (¬ p) (¬ q))
  ≔ λ (H : ϵ (@⇔ p q)),
        and_elim (@⇒  p q) (@⇒  q p) (@⇔ (¬ p) (¬ q)) H
        (λ (pq : ϵ (@⇒  p q)),
           λ (qp : ϵ (@⇒  q p)),
             and_intro (@⇒  (¬ p) (¬ q)) (@⇒  (¬ q) (¬ p))
             (λ (x : ϵ (¬ p)), λ (y : ϵ q), x (qp y))
             (λ (x : ϵ (¬ q)), λ (y : ϵ p), x (pq y)));
symbol eq_subst (a : Type) (x : τ a) (y : τ a)
  (p : τ a → Prop) : ϵ (@=α a x y) → ϵ (p x) → ϵ (p y)
  ≔ λ (H1 : ϵ (@=α a x y)),
        λ (H2 : ϵ (p x)), equal_ind a p x y H1 H2;
symbol eq_refl (a : Type) (x : τ a) : ϵ (@=α a x x)
  ≔ refl a x;
symbol eq_sym (a : Type) (x : τ a) (y : τ a)
  : ϵ (@=α a x y) → ϵ (@=α a y x)
  ≔ λ (H1 : ϵ (@=α a x y)), equal_sym a x y H1;
symbol not_eq_sym (a : Type) (x : τ a) (y : τ a)
  : ϵ (¬ (@=α a x y)) → ϵ (¬ (@=α a y x))
  ≔ λ (H1 : ϵ (¬ (@=α a x y))),
        λ (H2 : ϵ (@=α a y x)), H1 (eq_sym a y x H2);
symbol eq_trans (a : Type) (x : τ a) (y : τ a) (z : τ a)
  : ϵ (@=α a x y) → ϵ (@=α a y z) → ϵ (@=α a x z)
  ≔ λ (H1 : ϵ (@=α a x y)),
        λ (H2 : ϵ (@=α a y z)),
          eq_subst a y z (λ (s : τ a), @=α a x s) H2 H1;
symbol f_equal (a : Type) (b : Type) (f : τ a → τ b)
  (x : τ a) (y : τ a)
  : ϵ (@=α a x y) → ϵ (@=α b (f x) (f y))
  ≔ λ (H : ϵ (@=α a x y)),
        eq_subst a x y (λ (z : τ a), @=α b (f x) (f z)) H
        (eq_refl b (f x));
symbol f_equal2 (a : Type) (b : Type) (c : Type)
  (f : τ a → τ b → τ c) (x1 : τ a) (y1 : τ a)
  (x2 : τ b) (y2 : τ b)
  : ϵ (@=α a x1 y1)
    → ϵ (@=α b x2 y2) → ϵ (@=α c (f x1 x2) (f y1 y2))
  ≔ λ (H1 : ϵ (@=α a x1 y1)),
        λ (H2 : ϵ (@=α b x2 y2)),
          eq_subst a x1 y1 (λ (z1 : τ a), @=α c (f x1 x2) (f z1 y2)) H1
          (eq_subst b x2 y2 (λ (z2 : τ b), @=α c (f x1 x2) (f x1 z2))
           H2 (eq_refl c (f x1 x2)));
symbol inhabited : Type → Prop;
symbol inhabits : Π (a : Type), τ a → ϵ (inhabited a);

rule ϵ (@∀α $t $f) ↪ Π x: τ $t, ϵ ($f x);
rule ϵ (foralltype $f) ↪ Π i: Type, ϵ ($f i);

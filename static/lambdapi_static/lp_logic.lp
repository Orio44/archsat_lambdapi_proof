require open Logic.Zenon.FOL Logic.Zenon.zen;

constant symbol False_elim : Π (A : Prop), ϵ ⊥ → ϵ A;
symbol and_intro (f1 : Prop) (f2 : Prop) (H1 : ϵ f1) (H2 : ϵ f2)
  : ϵ (@∧ f1 f2)
  ≔ λ (f3 : Prop), λ (H3 : ϵ f1 → ϵ f2 → ϵ f3), H3 H1 H2;
symbol and_elim1 (f1 : Prop) (f2 : Prop) (H3 : ϵ (@∧ f1 f2)) : ϵ f1
  ≔ H3 f1 (λ (H1 : ϵ f1), λ (H2 : ϵ f2), H1);
symbol and_elim2 (f1 : Prop) (f2 : Prop) (H3 : ϵ (@∧ f1 f2)) : ϵ f2
  ≔ H3 f2 (λ (H1 : ϵ f1), λ (H2 : ϵ f2), H2);
symbol or_intro1 (f1 : Prop) (f2 : Prop) (H1 : ϵ f1) : ϵ (@∨ f1 f2)
  ≔ λ (f3 : Prop),
        λ (H13 : ϵ f1 → ϵ f3), λ (H23 : ϵ f2 → ϵ f3), H13 H1;
symbol or_intro2 (f1 : Prop) (f2 : Prop) (H2 : ϵ f2) : ϵ (@∨ f1 f2)
  ≔ λ (f3 : Prop),
        λ (H13 : ϵ f1 → ϵ f3), λ (H23 : ϵ f2 → ϵ f3), H23 H2;
symbol or_elim (f1 : Prop) (f2 : Prop) (f3 : Prop) (H3 : ϵ (@∨ f1 f2))
  (H13 : ϵ (@⇒ f1 f3)) (H23 : ϵ (@⇒ f2 f3)) : ϵ f3 ≔ H3 f3 H13 H23;
symbol eqv_intro
  ≔ λ (f1 : Prop), λ (f2 : Prop), and_intro (@⇒ f1 f2) (@⇒ f2 f1);
symbol eqv_elim1
  ≔ λ (f1 : Prop), λ (f2 : Prop), and_elim1 (@⇒ f1 f2) (@⇒ f2 f1);
symbol eqv_elim2
  ≔ λ (f1 : Prop), λ (f2 : Prop), and_elim2 (@⇒ f1 f2) (@⇒ f2 f1);
symbol equalc (A : Type) (x : τ A) (y : τ A) : Prop
  ≔ ¬ (¬ (@=α A x y));
symbol refl : Π (A : Type), Π (x : τ A), ϵ (@=α A x x); /*
  ≔ λ (A : Type),
        λ (x : τ A), λ (H : τ A → Prop), λ (px : ϵ (H x)), px; */
symbol equal_ind
  : Π (A : Type),
      Π (H : τ A → Prop),
        Π (x : τ A),
          Π (y : τ A), ϵ (@=α A x y) → ϵ (H x) → ϵ (H y); /*
  ≔ λ (A : Prop),
        λ (P : ϵ A → Prop),
          λ (x : ϵ A),
            λ (y : ϵ A), λ (eq : ϵ (@=α A x y)), eq P; */
symbol equal_sym
  : Π (A : Type),
      Π (x : τ A),
        Π (y : τ A), ϵ (@=α A x y) → ϵ (@=α A y x); /*
  ≔ λ (A : Prop),
        λ (x : ϵ A),
          λ (y : ϵ A),
            λ (eq : ϵ (@=α A x y)),
              equal_ind A (λ (z : ϵ A), @=α A z x) x y eq (refl A x); */
symbol equal_congr
  : Π (A : Type),
      Π (B : Type),
        Π (f : τ A → τ B),
          Π (x : τ A),
            Π (y : τ A), ϵ (@=α A x y) → ϵ (@=α B (f x) (f y)); /*
  ≔ λ (A : Prop),
        λ (B : Prop),
          λ (f : ϵ A → ϵ B),
            λ (x : ϵ A),
              λ (y : ϵ A),
                λ (H : ϵ (@=α A x y)),
                  equal_ind A (λ (z : ϵ A), @=α B (f x) (f z)) x y H
                  (refl B (f x));
*/
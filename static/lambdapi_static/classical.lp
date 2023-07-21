require open Logic.Zenon.FOL Logic.Zenon.zen;

constant symbol classic
  : Π (p : Prop),
      Π (z : Prop),
        (ϵ p → ϵ z)
        → (ϵ (¬ p) → ϵ z) → ϵ z;
symbol nnpp (p : Prop)
  : ϵ (¬ (¬ p)) → ϵ p
  ≔ λ (H1 : ϵ (¬ (¬ p))),
        classic p p (λ (H2 : ϵ p), H2)
        (λ (H3 : ϵ (¬ p)), H1 H3 p);
symbol not_all_not_ex (u : Type) (p : τ u → Prop)
  : ϵ (¬ (@∀α u (λ x : τ u, ¬ (p x))))
    → ϵ (@∃α u p); /*
  ≔ λ
        
        notall : ϵ
                 (¬
                  (@∀α u (λ (x : τ u), ¬ (p x))))
        ,
        nnpp (@∃α u p)
        (λ abs : ϵ (¬ (@∃α u p)),
           notall
           (λ n : τ u,
              λ H : ϵ (p n),
                abs
                (λ z : Prop,
                   λ p0 : Π (x : τ u),
                            ϵ (p x) → ϵ z
                     , p0 n H)));*/
symbol not_all_ex_not (u : Type) (p : τ u → Prop)
  : ϵ (¬ (@∀α u p))
    → ϵ (@∃α u (λ (x : τ u), ¬ (p x))); /*
  ≔ λ (notall : ϵ (¬ (@∀α u p))),
        not_all_not_ex u (λ (x : u), ¬ (p x))
        (λ
           (
           all : ϵ
                 (@∀α u
                  (λ (x : u), ¬ (¬ (p x))))
           ), notall (λ (n : u), nnpp (p n) (all n))); */
symbol not_ex_all_not (u : Type) (p : τ u → Prop)
  : ϵ (¬ (@∃α u p))
    → ϵ (@∀α u (λ (x : τ u), ¬ (p x))); /*
  ≔ λ (notex : ϵ (¬ (@∃α u p))),
        λ (n : u),
          λ (abs : ϵ (p n)),
            notex
            (λ (z : Prop),
               λ
                 (
                 p0 : Π (x : u),
                        ϵ (p x) → ϵ z
                 ), p0 n abs); */
symbol not_ex_not_all (u : Type) (p : τ u → Prop)
  : ϵ
    (¬ (@∃α u (λ (x : τ u), ¬ (p x))))
    → ϵ (@∀α u p); /*
  ≔ λ
        (
        H : ϵ
            (¬
             (@∃α u (λ (x : u), ¬ (p x))))
        ),
        λ (n : u),
          nnpp (p n)
          (λ (k : ϵ (¬ (p n))),
             H
             (λ (z : Prop),
                λ
                  (
                  p0 : Π (x : u),
                         ϵ (¬ (p x)) → ϵ z
                  ), p0 n k)); */
symbol not_all_not_ex_type (p : Type → Prop)
  : ϵ
    (¬ (foralltype (λ (x : Type), ¬ (p x))))
    → ϵ (existstype p); /*
  ≔ λ
        (
        notall : ϵ
                 (¬
                  (foralltype
                   (λ (x : Type), ¬ (p x))))
        ),
        nnpp (existstype p)
        (λ (abs : ϵ (¬ (existstype p))),
           notall
           (λ (n : Type),
              λ (H : ϵ (p n)),
                abs
                (λ (z : Prop),
                   λ
                     (
                     p0 : Π (x : Type),
                            ϵ (p x) → ϵ z
                     ), p0 n H)));*/
symbol not_all_ex_not_type (p : Type → Prop)
  : ϵ (¬ (foralltype p))
    → ϵ
        (existstype (λ (x : Type), ¬ (p x))); /*
  ≔ λ (notall : ϵ (¬ (foralltype p))),
        not_all_not_ex_type (λ (x : Type), ¬ (p x))
        (λ
           (
           all : ϵ
                 (foralltype
                  (λ (x : Type), ¬ (¬ (p x))))
           ), notall (λ (n : Type), nnpp (p n) (all n))); */
symbol not_ex_all_not_type (p : Type → Prop)
  : ϵ (¬ (existstype p))
    → ϵ
        (foralltype (λ (x : Type), ¬ (p x))); /*
  ≔ λ (notex : ϵ (¬ (existstype p))),
        λ (n : Type),
          λ (abs : ϵ (p n)),
            notex
            (λ (z : Prop),
               λ
                 (
                 p0 : Π (x : Type),
                        ϵ (p x) → ϵ z
                 ), p0 n abs); */
symbol not_ex_not_all_type (p : Type → Prop)
  : ϵ
    (¬ (existstype (λ (x : Type), ¬ (p x))))
    → ϵ (foralltype p); /*
  ≔ λ
        (
        H : ϵ
            (¬
             (existstype (λ (x : Type), ¬ (p x))))
        ),
        λ (n : Type),
          nnpp (p n)
          (λ (k : ϵ (¬ (p n))),
             H
             (λ (z : Prop),
                λ
                  (
                  p0 : Π (x : Type),
                         ϵ (¬ (p x)) → ϵ z
                  ), p0 n k)); */

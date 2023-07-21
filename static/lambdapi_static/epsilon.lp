require open Logic.Zenon.FOL Logic.Zenon.zen lambdapi_static.logic;

symbol epsilon
  : Π (a : Type),
      ϵ (inhabited a)
      → (τ a → Prop) → τ a;
symbol epsilon_spec
  : Π (a : Type),
      Π (i : ϵ (inhabited a)),
        Π (p : τ a → Prop),
          ϵ (@∃α a p) → ϵ (p (epsilon a i p));
symbol epsilon_type : (Type → Prop) → Type;
symbol epsilon_type_spec
  : Π (p : Type → Prop),
      ϵ (existstype p) → ϵ (p (epsilon_type p));

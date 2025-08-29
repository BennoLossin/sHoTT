# Orthogonal type families

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
```

```rzk
#def orthogonal-to
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( φ : ψ → TOPE)
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( a : ψ → A)
  → ( f : (t : φ) → C (a t))
  → is-contr ((t : ψ) → C (a t) [φ t ↦ f t])
```

## Leibniz Cotensor is an Equivalence

### Leibniz cotensor

```rzk
#def leibniz-cotensor-codomain
  ( Y X E B : U)
  ( j : Y → X)
  ( p : E → B)
  : U
  := Σ (f : Y → E) , Σ (g : X → B) , comp Y E B p f = comp Y X B g j

#def leibniz-cotensor-shape-codomain
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  : U
  := Σ (f : Y → E) , Σ (g : X → B) , (\ (y : Y) → p (f y)) =_{ Y → B } (\ (y : Y) → g y)

#def leibniz-cotensor
  ( Y X E B : U)
  ( j : Y → X)
  ( p : E → B)
  ( f : X → E)
  : leibniz-cotensor-codomain Y X E B j p
  := (comp Y X E f j , (comp X E B p f , refl))

#def leibniz-cotensor-shape
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  ( f : X → E)
  : leibniz-cotensor-shape-codomain I X Y E B p
  := (\ (y : Y) → f y , (\ (x : X) → p (f x), refl))
```

### Orthogonal Families: Leibniz Cotensor is an Equivalence

```rzk
#def is-equiv-leibniz-cotensor-shap-orthogonal-to
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( B : U)
  ( P : B → U)
  : is-equiv
  ( X → total-type B P)
  ( leibniz-cotensor-shape-codomain I X Y (total-type B P) B
    ( projection-total-type B P))
  ( leibniz-cotensor-shape I X Y (total-type B P) B
    ( projection-total-type B P))
  :=
  TODO (is-equiv
  ( X → total-type B P)
  ( leibniz-cotensor-shape-codomain I X Y (total-type B P) B
    ( projection-total-type B P))
  ( leibniz-cotensor-shape I X Y (total-type B P) B
    ( projection-total-type B P)))
```

## Inner Families

```rzk
#def is-inner-fib-type-fam
  ( A : U)
  ( B : A → U)
  : U
  := orthogonal-to (2 × 2) Δ² Λ²₁ A B
```

```rzk
#section inner-fib-lifts

#variable A : U
#variable B : A → U
#variable is-inner-fib-type-fam-B : is-inner-fib-type-fam A B
#variable a : Δ² → A
#variable b : (t : Λ²₁) → B (a t)

#def lift-is-inner-fib-type-fam uses (A)
  : (t : Δ²) → B (a t) [Λ²₁ t ↦ b t]
  :=
  center-contraction
  ( (t : Δ²) → B (a t) [Λ²₁ t ↦ b t])
  ( is-inner-fib-type-fam-B a b)

#def is-unique-lift-is-inner-fib-type-fam uses (A)
  : (z : (t : Δ²) → B (a t) [Λ²₁ t ↦ b t]) → lift-is-inner-fib-type-fam = z
  :=
  homotopy-contraction
  ( (t : Δ²) → B (a t) [Λ²₁ t ↦ b t])
  ( is-inner-fib-type-fam-B a b)

#end inner-fib-lifts
```

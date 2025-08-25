# Orthogonal type families

```rzk
#lang rzk-1
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

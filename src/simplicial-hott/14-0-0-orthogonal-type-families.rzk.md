# Orthogonal type families

```rzk
#lang rzk-1
```

```rzk
#assume TODO : (A : U) → A
#assume extext : ExtExt
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
#section has-contr-relative-extension-types-iff-orthogonal-to

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U
#variable C : A → U

#def has-contr-relative-extension-types-orthogonal-to
  ( orthogonal-to-C : orthogonal-to I ψ ϕ A C)
  : has-contr-relative-extension-types I ψ ϕ
  ( \ _ → total-type A C)
  ( \ _ → A)
  ( \ _ → projection-total-type A C)
  :=
  \ σ τ → is-contr-equiv-is-contr'
  ( Σ ( τ' : (t : ψ) → total-type A C [ϕ t ↦ σ t])
    , ( (t : ψ) → (projection-total-type A C (τ' t) = τ t) [ϕ t ↦ refl]))
  ( (t : ψ) → C (τ t) [ϕ t ↦ π₂ (σ t)])
  ( equiv-comp
    ( Σ ( τ' : (t : ψ) → total-type A C [ϕ t ↦ σ t])
      , ( (t : ψ) → (projection-total-type A C (τ' t) = τ t) [ϕ t ↦ refl]))
    ( (t : ψ) → (Σ (τ' : total-type A C) , (π₁ τ' = τ t)) [ϕ t ↦ (σ t, refl)])
    ( (t : ψ) → C (τ t) [ϕ t ↦ π₂ (σ t)])
    ( equiv-is-inverse
      ( Σ ( τ' : (t : ψ) → total-type A C [ϕ t ↦ σ t])
        , ( (t : ψ) → (projection-total-type A C (τ' t) = τ t) [ϕ t ↦ refl]))
      ( (t : ψ) → (Σ (τ' : total-type A C) , (π₁ τ' = τ t)) [ϕ t ↦ (σ t, refl)])
      ( \ (τ', p) t → (τ' t, p t))
      ( \ f → (\ t → π₁ (f t), \ t → π₂ (f t)))
      ( \ _ → refl)
      ( \ _ → refl))
    ( equiv-is-inverse
      ( (t : ψ) → (Σ (τ' : total-type A C) , (π₁ τ' = τ t)) [ϕ t ↦ (σ t, refl)])
      ( (t : ψ) → C (τ t) [ϕ t ↦ π₂ (σ t)])
      ( \ f t → transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
      ( \ f t → ((τ t, f t), refl))
      ( \ f → naiveextext-extext extext I ψ ϕ
        ( \ t → Σ (τ' : total-type A C) , (π₁ τ' = τ t))
        ( \ t → (σ t, refl))
        ( \ t → ((τ t
            , transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
          , refl))
        ( f)
        ( \ t → path-of-pairs-pair-of-paths (total-type A C) (\ τ' → π₁ τ' = τ t)
          ( τ t , transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
          ( π₁ (f t))
          ( rev (total-type A C)
            ( π₁ (f t))
            ( τ t , transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
            ( transport-lift A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t)))))
          ( refl)
          ( π₂ (f t))
          ( triple-concat
            ( π₁ (π₁ (f t)) = τ t)
            ( transport
              ( total-type A C)
              ( \ (a, _) → a = τ t)
              ( τ t , transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
              ( π₁ (f t))
              ( rev (total-type A C)
                ( π₁ (f t))
                ( τ t , transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
                ( transport-lift A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t)))))
              ( refl))
            ( ap
              ( total-type A C)
              ( A)
              ( π₁ (f t))
              ( τ t, transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
              ( \ (a, _) → a)
              ( rev
                ( total-type A C)
                ( τ t, transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
                ( π₁ (f t))
                ( rev
                  ( total-type A C)
                  ( π₁ (f t))
                  ( τ t, transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
                  ( transport-lift A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t)))))))
            ( ap
              ( total-type A C)
              ( A)
              ( π₁ (f t))
              ( τ t , transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
              ( \ (a, _) → a)
              ( transport-lift A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t)))))
            ( π₂ (f t))
            ( transport-eq-concat-ap-rev
              ( total-type A C)
              ( A)
              ( τ t)
              ( \ (a, _) → a)
              ( τ t , transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
              ( π₁ (f t))
              ( rev (total-type A C)
                ( π₁ (f t))
                ( τ t , transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
                ( transport-lift A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t)))))
              ( refl))
            ( ap
              ( ( π₁ (f t))
                = ( τ t, transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t)))))
              ( π₁ (π₁ (f t)) = τ t)
              ( rev
                ( total-type A C)
                ( τ t, transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
                ( π₁ (f t))
                ( rev
                  ( total-type A C)
                  ( π₁ (f t))
                  ( τ t, transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
                  ( transport-lift A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))))
              ( transport-lift A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
              ( ap
                ( total-type A C)
                ( A)
                ( π₁ (f t))
                ( τ t, transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
                ( \ (a, _) → a))
              ( rev-rev
                ( total-type A C)
                ( π₁ (f t))
                ( τ t, transport A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))
                ( transport-lift A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t))))))
            ( transport-lift-first A C (π₁ (π₁ (f t))) (τ t) (π₂ (f t)) (π₂ (π₁ (f t)))))))
      ( \ _ → refl)))
  ( orthogonal-to-C τ (\ t → π₂ (σ t)))


  {-
  Σ ( τ' : (t : ψ) → total-type A C [ϕ t ↦ σ t])
  , ( (t : ψ) → (pr (τ' t) = τ t) [ϕ t ↦ refl])

  ~=

  (t : ψ) → (Σ (x: total-type A C), pr x = τ t) [ϕ t ↦ (σ t, refl)]

  ~=

  (t : ψ) → (fib pr (τ t)) [ϕ t ↦ (σ t, refl)]

  ~=

  (t : ψ) → C (τ t) [ϕ t ↦ π₂ (σ t)]
  -}
#end has-contr-relative-extension-types-iff-orthogonal-to
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

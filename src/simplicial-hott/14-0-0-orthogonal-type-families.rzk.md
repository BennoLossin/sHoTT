# Orthogonal type families

```rzk
#lang rzk-1
```

```rzk
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

## `orthogonal-to` is the same as `is-right-orthogonal-to-shape`

```rzk
#section has-contr-relative-extension-types-iff-orthogonal-to

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U
#variable C : A → U

#def equiv-relative-extension-type-orthogonal-ext
  ( σ : (t : ϕ) → total-type A C)
  ( τ : (t : ψ) → A [ϕ t ↦ projection-total-type A C (σ t)])
  : Equiv
  ( Σ ( τ' : (t : ψ) → total-type A C [ϕ t ↦ σ t])
    , ( (t : ψ) → (projection-total-type A C (τ' t) = τ t) [ϕ t ↦ refl]))
  ( (t : ψ) → C (τ t) [ϕ t ↦ π₂ (σ t)])
  :=
  equiv-comp
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
    ( \ _ → refl))

#def has-contr-relative-extension-types-orthogonal-to uses (extext)
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
  ( equiv-relative-extension-type-orthogonal-ext σ τ)
  ( orthogonal-to-C τ (\ t → π₂ (σ t)))

#def orthogonal-to-has-contr-relative-extension-types uses (extext)
  ( has-contr-rel : has-contr-relative-extension-types I ψ ϕ
                    ( \ _ → total-type A C)
                    ( \ _ → A)
                    ( \ _ → projection-total-type A C))
  : orthogonal-to I ψ ϕ A C
  :=
  \ a f → is-contr-equiv-is-contr
  ( Σ ( τ' : (t : ψ) → total-type A C [ϕ t ↦ (a t, f t)])
    , ( (t : ψ) → (projection-total-type A C (τ' t) = a t) [ϕ t ↦ refl]))
  ( (t : ψ) → C (a t) [ϕ t ↦ f t])
  ( equiv-relative-extension-type-orthogonal-ext (\ t → (a t, f t)) a)
  ( has-contr-rel (\ t → (a t, f t)) a)

#end has-contr-relative-extension-types-iff-orthogonal-to
```

```rzk

#section orthogonal-to-iff-is-right-orthogonal-to-shape

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U
#variable C : A → U

#def is-right-orthogonal-to-shape-orthogonal-to
  ( orthogonal-to-C : orthogonal-to I ψ ϕ A C)
  : is-right-orthogonal-to-shape I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C)
  :=
  is-right-orthogonal-to-shape-has-contr-relative-extension-types
  ( extext) I ψ ϕ
  ( total-type A C)
  ( A)
  ( projection-total-type A C)
  ( has-contr-relative-extension-types-orthogonal-to I ψ ϕ A C
    ( orthogonal-to-C))

#def orthogonal-to-is-right-orthogonal-to-shape
  ( is-right-orth-C : is-right-orthogonal-to-shape I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C))
  : orthogonal-to I ψ ϕ A C
  :=
  orthogonal-to-has-contr-relative-extension-types I ψ ϕ A C
  ( has-contr-relative-extension-types-is-right-orthogonal-to-shape
    ( extext) I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C)
    ( is-right-orth-C))

#end orthogonal-to-iff-is-right-orthogonal-to-shape
```

## Leibniz Cotensor is an Equivalence

### Leibniz cotensor

```rzk
#def leibniz-cotensor-codomain
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  : U
  := Σ (f : Y → E) , Σ (g : X → B) , (\ (y : Y) → p (f y)) =_{ Y → B } (\ (y : Y) → g y)

#def leibniz-cotensor
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  ( f : X → E)
  : leibniz-cotensor-codomain I X Y E B p
  := (\ (y : Y) → f y , (\ (x : X) → p (f x), refl))
```

### Orthogonal Families: Leibniz Cotensor is an Equivalence


```rzk
#def equiv-sigma-ext
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( A : U)
  : Equiv (X → A) (Σ (f : Y → A) , ((x : X) → A [Y x ↦ f x]))
  :=
  equiv-is-inverse (X → A) (Σ (f : Y → A) , ((x : X) → A [Y x ↦ f x]))
  ( \ f → (\ y → f y, \ x → f x))
  ( \ (_, f) x → f x)
  ( \ _ → refl)
  ( \ _ → refl)
```

```rzk
#def equiv-ext-sigma-eq-ext-constraint
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( A : U)
  ( g : Y → A)
  : Equiv (Σ (f : X → A) , g =_{Y → A} (\ y → f y)) ((x : X) → A [Y x ↦ g x])
  :=
  equiv-comp
  ( Σ (f : X → A) , g =_{Y → A} (\ y → f y))
  ( Σ (f : Y → A) , product (g = f) ((x : X) → A [Y x ↦ f x]))
  ( (x : X) → A [Y x ↦ g x])
  ( equiv-is-inverse
    ( Σ (f : X → A) , g =_{Y → A} (\ y → f y))
    ( Σ (f : Y → A) , product (g = f) ((x : X) → A [Y x ↦ f x]))
    ( \ (f, p) → ((\ y → f y), (p, f)))
    ( \ (_, (p, F)) → (F, p))
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-based-paths-family (Y → A) (\ f → ((x : X) → A [Y x ↦ f x])) g)
```

```rzk
#def is-equiv-leibniz-cotensor-is-right-orthogonal-to-shape
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  ( orth : is-right-orthogonal-to-shape I X Y E B p)
  : is-equiv
    ( X → E)
    ( leibniz-cotensor-codomain I X Y E B p)
    ( leibniz-cotensor I X Y E B p)
  :=
  π₂
  ( equiv-triple-comp
    ( X → E)
    ( Σ (f : Y → E) , (x : X) → E [Y x ↦ f x])
    ( Σ (f : Y → E) , (x : X) → B [Y x ↦ p (f x)])
    ( leibniz-cotensor-codomain I X Y E B p)
    ( equiv-sigma-ext I X Y E)
    ( total-equiv-family-of-equiv
      ( Y → E)
      ( \ f → (x : X) → E [Y x ↦ f x])
      ( \ f → (x : X) → B [Y x ↦ p (f x)])
      ( \ f → (\ F x → p (F x), orth f)))
    ( total-equiv-family-of-equiv
      ( Y → E)
      ( \ f → (x : X) → B [Y x ↦ p (f x)])
      ( \ f → Σ (g : X → B) , (\ y → p (f y)) =_{Y → B} (\ y → g y))
      ( \ f → inv-equiv
        ( Σ (g : X → B) , (\ y → p (f y)) =_{Y → B} (\ y → g y))
        ( (x : X) → B [Y x ↦ p (f x)])
        ( equiv-ext-sigma-eq-ext-constraint I X Y B (\ y → p (f y))))))
```


```rzk
#def is-equiv-leibniz-cotensor-orthogonal-to uses (extext)
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( B : U)
  ( P : B → U)
  ( orth : orthogonal-to I X Y B P)
  : is-equiv
  ( X → total-type B P)
  ( leibniz-cotensor-codomain I X Y (total-type B P) B
    ( projection-total-type B P))
  ( leibniz-cotensor I X Y (total-type B P) B
    ( projection-total-type B P))
  :=
  is-equiv-leibniz-cotensor-is-right-orthogonal-to-shape I X Y
  ( total-type B P) (B)
  ( projection-total-type B P)
  ( is-right-orthogonal-to-shape-orthogonal-to I X Y B P orth)
```

## Inner Families

```rzk
#def is-inner-family
  ( A : U)
  ( B : A → U)
  : U
  := orthogonal-to (2 × 2) Δ² Λ²₁ A B
```

```rzk
#section inner-fib-lifts

#variable A : U
#variable B : A → U
#variable is-inner-family-B : is-inner-family A B
#variable a : Δ² → A
#variable b : (t : Λ²₁) → B (a t)

#def lift-is-inner-family uses (A)
  : (t : Δ²) → B (a t) [Λ²₁ t ↦ b t]
  :=
  center-contraction
  ( (t : Δ²) → B (a t) [Λ²₁ t ↦ b t])
  ( is-inner-family-B a b)

#def is-unique-lift-is-inner-family uses (A)
  : (z : (t : Δ²) → B (a t) [Λ²₁ t ↦ b t]) → lift-is-inner-family = z
  :=
  homotopy-contraction
  ( (t : Δ²) → B (a t) [Λ²₁ t ↦ b t])
  ( is-inner-family-B a b)

#end inner-fib-lifts
```

```rzk
#def is-segal-fiber-is-inner-family
  ( B : U)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( b : B)
  : is-segal (P b)
  :=
  \ x y z f g → is-contr-equiv-is-contr
  ( ((t, s) : Δ²) → P b [s ≡ 0₂ ↦ f t, t ≡ 1₂ ↦ g s])
  ( Σ (h : hom (P b) x z) , (hom2 (P b) x y z f g h))
  ( equiv-is-inverse
    ( ((t, s) : Δ²) → P b [s ≡ 0₂ ↦ f t, t ≡ 1₂ ↦ g s])
    ( Σ (h : hom (P b) x z) , (hom2 (P b) x y z f g h))
    ( \ σ → (\ t → σ (t, t), (\ ts → σ ts)))
    ( \ (_, σ) ts → σ ts)
    ( \ _ → refl)
    ( \ _ → refl))
  ( is-inner-family-P
    ( \ _ → b)
    ( \ (t, s) → recOR(s ≡ 0₂ ↦ f t, t ≡ 1₂ ↦ g s)))
```

## Isoinner Families

```rzk
#def Iso-arr
  ( A : U)
  ( is-segal-A : is-segal A)
  : U
  := Σ (f : arr A) , is-iso-arrow A is-segal-A (f 0₂) (f 1₂) f

#def iso-arr-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( p : x = y)
  : Iso-arr A is-segal-A
  := ( hom-eq A x y p, is-iso-arrow-hom-eq A is-segal-A x y p)
```

```rzk
#def is-isoinner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
  Σ ( is-inner-family-P : is-inner-family B P)
  , ( (b : B)
    → (f : Iso-arr (P b)
           ( is-segal-fiber-is-inner-family B P is-inner-family-P b))
    → is-contr (Σ (e : P b)
      , f = iso-arr-eq (P b)
            ( is-segal-fiber-is-inner-family B P is-inner-family-P b)
            ( e) (e) (refl)))
```

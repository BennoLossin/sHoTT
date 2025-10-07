# LARI adjunctions are initial sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```



```rzk
#assume funext : FunExt
#assume extext : ExtExt
-- #assume is-iso-arrow-nat-trans-is-iso-arrow-boundary : is-iso-arrow-nat-trans-is-iso-arrow-boundary-type
```


```rzk

#def ctie
  ( A : Δ¹ → U)
  ( is-contr-A : (t : Δ¹) → is-contr (A t))
  ( x : A 0₂)
  ( y : A 1₂)
  ( f g : (t : Δ¹) → A t [t ≡ 0₂ ↦ x, t ≡ 1₂ ↦ y])
  : (t : Δ¹) → (f t = g t) [t ≡ 0₂ ↦ refl, t ≡ 1₂ ↦ refl]
  :=
  dhom-ext-is-locally-contr-extext extext
  ( \ t → f t = g t)
  ( \ t → is-prop-is-contr (A t) (is-contr-A t) (f t) (g t))
  ( refl)
  ( refl)
```

```rzk
#section is-initial-section-is-transposing-LARI-adj-is-rezk

#variables A B : U
#variable is-rezk-A : is-rezk A
#variable is-segal-B : is-segal B
#variable f : A → B
#variable u : B → A
#variable adj : is-transposing-adj A B f u
#variable is-LARI-f-u : is-transposing-LARI-adj A B (π₁ is-rezk-A) f u adj

#def hom-eq-is-transposing-adj-is-rezk
  ( a : A)
  ( b : B)
  : (u b = a) → (hom B (f a) b)
  :=
  quadruple-comp
  ( u b = a)
  ( a = u b)
  ( Iso A (π₁ is-rezk-A) a (u b))
  ( hom A a (u b))
  ( hom B (f a) b)
  ( π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
  ( \ f → π₁ f)
  ( iso-eq A (π₁ is-rezk-A) a (u b))
  ( rev A (u b) a)

#def total-hom-iso
  ( a : A)
  ( (b, g) : Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b))
  : Σ (b : B) , hom A a (u b)
  := (b, π₁ g)

#def equiv-dhom-iso-dhom-hom uses (extext)
  ( a : A)
  ( (x₁, x₂) (y₁, y₂) : (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)))
  ( g : hom B x₁ y₁)
  : Equiv
    ( dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂)
    ( dhom B x₁ y₁ g (\ b → hom A a (u b)) (π₁ x₂) (π₁ y₂))
  :=
  equiv-is-inverse
  ( dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂)
  ( dhom B x₁ y₁ g (\ b → hom A a (u b)) (π₁ x₂) (π₁ y₂))
  ( \ γ t → π₁ (γ t))
  ( \ γ t → ( γ t
  , is-iso-arrow-square-sides-iso-is-rezk A is-rezk-A
    ( a) (a) (u x₁) (u y₁)
    ( id-hom A a)
    ( \ t → u (g t))
    ( x₂)
    ( y₂)
    ( \ t s → γ t s)
    ( t)))
  ( \ γ → naiveextext-extext extext 2 Δ¹ ∂Δ¹
    ( \ t → Iso A (π₁ is-rezk-A) a (u (g t)))
    ( \ t → recOR(t ≡ 0₂ ↦ x₂, t ≡ 1₂ ↦ y₂))
    ( \ t → ( π₁ (γ t)
      , is-iso-arrow-square-sides-iso-is-rezk A is-rezk-A
        ( a) (a) (u x₁) (u y₁)
        ( id-hom A a)
        ( \ t → u (g t))
        ( x₂)
        ( y₂)
        ( \ t s → π₁ (γ t) s)
        ( t)))
    ( γ)
    ( \ t → path-of-pairs-pair-of-paths
      ( hom A a (u (g t)))
      ( is-iso-arrow A (π₁ is-rezk-A) a (u (g t)))
      ( π₁ (γ t))
      ( π₁ (γ t))
      ( refl)
      ( is-iso-arrow-square-sides-iso-is-rezk A is-rezk-A
        ( a) (a) (u x₁) (u y₁)
        ( id-hom A a)
        ( \ t → u (g t))
        ( x₂)
        ( y₂)
        ( \ t s → π₁ (γ t) s)
        ( t))
      ( π₂ (γ t))
      ( ctie
        ( \ t → is-iso-arrow A (π₁ is-rezk-A) a (u (g t)) (π₁ (γ t)))
        ( \ t → is-contr-is-inhabited-is-prop
          ( is-iso-arrow A (π₁ is-rezk-A) a (u (g t)) (π₁ (γ t)))
          ( is-prop-is-iso-arrow extext A (π₁ is-rezk-A) a (u (g t)) (π₁ (γ t)))
          ( π₂ (γ t)))
        ( π₂ x₂)
        ( π₂ y₂)
        ( is-iso-arrow-square-sides-iso-is-rezk A is-rezk-A
          ( a) (a) (u x₁) (u y₁)
          ( id-hom A a)
          ( \ t → u (g t))
          ( x₂)
          ( y₂)
          ( \ t s → π₁ (γ t) s))
        ( \ t → π₂ (γ t))
        ( t))))
  (\ _ → refl)

#def is-full-emb-total-hom-iso uses (extext)
  ( a : A)
  : is-full-emb (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) (Σ (b : B) , hom A a (u b)) (total-hom-iso a)
  :=
  \ x y → π₂ (equiv-triple-comp
  ( hom (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) x y)
  ( Σ (g : hom B (π₁ x) (π₁ y))
  , dhom B (π₁ x) (π₁ y) g (\ b → Iso A (π₁ is-rezk-A) a (u b)) (π₂ x) (π₂ y))
  ( Σ (g : hom B (π₁ x) (π₁ y))
  , dhom B (π₁ x) (π₁ y) g (\ b → hom A a (u b)) (π₁ (π₂ x)) (π₁ (π₂ y)))
  ( hom (Σ (b : B) , hom A a (u b)) (total-hom-iso a x) (total-hom-iso a y))
  ( equiv-hom-sigma-dhom B (\ b → Iso A (π₁ is-rezk-A) a (u b)) x y)
  ( total-equiv-family-of-equiv (hom B (π₁ x) (π₁ y))
    ( \ g → dhom B (π₁ x) (π₁ y) g (\ b → Iso A (π₁ is-rezk-A) a (u b)) (π₂ x) (π₂ y))
    ( \ g → dhom B (π₁ x) (π₁ y) g (\ b → hom A a (u b)) (π₁ (π₂ x)) (π₁ (π₂ y)))
    ( equiv-dhom-iso-dhom-hom a x y))
  ( equiv-sigma-dhom-hom B (\ b → hom A a (u b)) (π₁ x, π₁ (π₂ x)) (π₁ y, π₁ (π₂ y))))

#def sigma-hom-fib-is-transposing-adj-is-rezk uses (adj is-rezk-A)
  ( a : A)
  : fib B A u a → (Σ (b : B) , hom B (f a) b)
  := \ (b , p) → (b , hom-eq-is-transposing-adj-is-rezk a b p)

#def is-full-emb-sigma-hom-fib-is-transposing-adj-is-rezk
  uses (adj is-rezk-A funext extext)
  ( a : A)
  : is-full-emb (fib B A u a) (Σ (b : B) , hom B (f a) b)
  ( sigma-hom-fib-is-transposing-adj-is-rezk a)
  :=
  is-full-emb-quadruple-comp funext
  ( fib B A u a)
  ( rev-fib B A u a)
  ( Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b))
  ( Σ (b : B) , hom A a (u b))
  ( Σ (b : B) , hom B (f a) b)
  ( \ (b, p) → (b, rev A (u b) a p))
  ( is-full-emb-is-equiv extext
    ( fib B A u a)
    ( rev-fib B A u a)
    ( \ (b, p) → (b, rev A (u b) a p))
    ( is-equiv-total-is-equiv-fiberwise
      ( B)
      ( \ b → u b = a)
      ( \ b → a = u b)
      ( \ b → rev A (u b) a)
      ( \ b → is-equiv-rev A (u b) a)))
  ( \ (b, p) → (b, iso-eq A (π₁ is-rezk-A) a (u b) p))
  ( is-full-emb-is-equiv extext
    ( rev-fib B A u a)
    ( Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b))
    ( \ (b, p) → (b, iso-eq A (π₁ is-rezk-A) a (u b) p))
    ( is-equiv-total-is-equiv-fiberwise
      ( B)
      ( \ b → a = u b)
      ( \ b → Iso A (π₁ is-rezk-A) a (u b))
      ( \ b → iso-eq A (π₁ is-rezk-A) a (u b))
      ( \ b → π₂ is-rezk-A a (u b))))
  ( total-hom-iso a)
  ( is-full-emb-total-hom-iso a)
  ( \ (b, g) → (b, π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)) g))
  ( is-full-emb-is-equiv extext
    ( Σ (b : B) , hom A a (u b))
    ( Σ (b : B) , hom B (f a) b)
    ( \ (b, g) → (b, π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)) g))
    ( is-equiv-total-is-equiv-fiberwise
      ( B)
      ( \ b → hom A a (u b))
      ( \ b → hom B (f a) b)
      ( \ b → π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
      ( \ b → π₂ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))))


```

```rzk
#def section-is-transposing-LARI-adj
  ( a : A)
  : fib B A u a
  :=
  ( f a
  , rev A a (u (f a))
    ( eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))

#def tmpp-eq
  ( a : A)
  : ( id-hom B (f a))
  = ( quadruple-comp
      ( u (f a) = a)
      ( a = u (f a))
      ( Iso A (π₁ is-rezk-A) a (u (f a)))
      ( hom A a (u (f a)))
      ( hom B (f a) (f a))
      ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
      ( \ f → π₁ f)
      ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
      ( rev A (u (f a)) a)
      ( rev A a (u (f a))
        ( eq-iso-is-rezk A is-rezk-A a (u (f a))
          ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  :=
  sextuple-concat (hom B (f a) (f a))
  ( id-hom B (f a))
  ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a)))
    (π₁ (adj a (f a)) (id-hom B (f a))))
  ( comp
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))
  ( comp
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)) (eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( triple-comp
    ( a = u (f a))
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
    ( eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))
  ( triple-comp
    ( a = u (f a))
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
    ( rev A (u (f a)) a (rev A a (u (f a))
      ( eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))))
  ( quadruple-comp
    ( u (f a) = a)
    ( a = u (f a))
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
    ( rev A (u (f a)) a)
    ( rev A a (u (f a))
      ( eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( rev (hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a)))
      (π₁ (adj a (f a)) (id-hom B (f a))))
    ( id-hom B (f a))
    ( inv-equiv-cancel (hom B (f a) (f a)) (hom A a (u (f a)))
      ( adj a (f a))
      ( id-hom B (f a))))
  ( refl)
  ( ap (Iso A (π₁ is-rezk-A) a (u (f a))) (hom B (f a) (f a))
    ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)) (eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))
    ( comp
      ( Iso A (π₁ is-rezk-A) a (u (f a)))
      ( hom A a (u (f a)))
      ( hom B (f a) (f a))
      ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
      ( \ f → π₁ f))
    ( rev (Iso A (π₁ is-rezk-A) a (u (f a)))
      ( iso-eq A (π₁ is-rezk-A) a (u (f a)) (eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)
      ( iso-eq-iso-is-rezk' A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( refl)
  ( ap (a = u (f a)) (hom B (f a) (f a))
    ( eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))
    ( rev A (u (f a)) a (rev A a (u (f a))
      ( eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
    ( triple-comp
      ( a = u (f a))
      ( Iso A (π₁ is-rezk-A) a (u (f a)))
      ( hom A a (u (f a)))
      ( hom B (f a) (f a))
      ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
      ( \ f → π₁ f)
      ( iso-eq A (π₁ is-rezk-A) a (u (f a))))
    ( rev-rev' A a (u (f a)) (eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( refl)

#def tmpp uses (is-LARI-f-u adj u is-rezk-A)
  ( a : A)
  : (f a, id-hom B (f a))
  =_{coslice B (f a)} (sigma-hom-fib-is-transposing-adj-is-rezk a (section-is-transposing-LARI-adj a))
  :=
  path-of-pairs-pair-of-paths B (\ b → hom B (f a) b)
  ( f a)
  ( f a)
  ( refl)
  ( id-hom B (f a))
  ( quadruple-comp
    ( u (f a) = a)
    ( a = u (f a))
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
    ( rev A (u (f a)) a)
    ( rev A a (u (f a))
      ( eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( tmpp-eq a)

#def is-initial-section-is-transposing-LARI-adj
  uses (is-LARI-f-u adj is-rezk-A f funext extext)
  : is-initial-section A (fib B A u) section-is-transposing-LARI-adj
  :=
  \ a → is-initial-is-full-emb-is-initial (fib B A u a) (Σ (b : B) , hom B (f a) b)
  ( sigma-hom-fib-is-transposing-adj-is-rezk a)
  ( is-full-emb-sigma-hom-fib-is-transposing-adj-is-rezk a)
  ( section-is-transposing-LARI-adj a)
  ( transport (coslice B (f a)) (\ x → is-initial (coslice B (f a)) x)
    ( f a, id-hom B (f a))
    ( sigma-hom-fib-is-transposing-adj-is-rezk a (section-is-transposing-LARI-adj a))
    ( tmpp a)
    ( is-initial-id-hom-is-segal B is-segal-B (f a)))


#end is-initial-section-is-transposing-LARI-adj-is-rezk
```

```rzk
#def toname2
  ( B : U)
  ( P : B → U)
  ( is-rezk-B : is-rezk B)
  ( s : (b : B) → P b)
  ( adj : is-transposing-adj B (total-type B P)
          ( \ b → (b, s b))
          ( projection-total-type B P))
  : ( \ b → homotopy-fiber-strict-fiber B P b (s b))
  = ( section-is-transposing-LARI-adj B (total-type B P) is-rezk-A
      ( \ b → (b, s b))
      ( projection-total-type B P)
      ( adj))
  := TODO (( \ b → homotopy-fiber-strict-fiber B P b (s b))
  = ( section-is-transposing-LARI-adj B (total-type B P) is-rezk-A
      ( \ b → (b, s b))
      ( projection-total-type B P)
      ( adj)))
```

```rzk
#def toname
  ( B : U)
  ( P : B → U)
  ( is-rezk-B : is-rezk B)
  ( is-segal-P : is-segal (total-type B P))
  ( s : (b : B) → P b)
  ( adj : is-transposing-adj B (total-type B P)
          ( \ b → (b, s b))
          ( projection-total-type B P))
  ( LARI-adj : is-transposing-LARI-adj B (total-type B P)
               ( π₁ is-rezk-B)
               ( \ b → (b, s b))
               ( projection-total-type B P)
               ( adj))
  : is-initial-section B P s
  :=
  is-initial-section-equiv-is-initial-section extext
  ( B) (fib (total-type B P) B (projection-total-type B P)) (P)
  ( \ b → inv-equiv (P b)
    ( fib (total-type B P) B (projection-total-type B P) b)
    ( equiv-homotopy-fiber-strict-fiber B P b))
  ( \ b → homotopy-fiber-strict-fiber B P b (s b))
  ( transport ((a : A) → fib B A u a) ()
    is-initial-section-is-transposing-LARI-adj
    ( B) (total-type B P) is-rezk-B is-segal-P
    ( \ b → (b, s b))
    ( projection-total-type B P)
    ( adj)
    ( LARI-adj))
```

```rzk
#def ctie2
  ( B : U)
  ( P : B → U)
  ( is-rezk-B : is-rezk B)
  ( is-segal-P : is-segal (total-type B P))
  ( s : (b : B) → P b)
  ( adj : is-transposing-adj B (total-type B P)
          ( \ b → (b, s b))
          ( projection-total-type B P))
  ( is-LARI-proj : is-transposing-LARI-adj
                   ( B) ( total-type B P)
                   ( π₁ (is-rezk-B))
                   ( \ b → (b, s b))
                   ( projection-total-type B P)
                   ( adj))
  ( x : B)
  : section-is-transposing-LARI-adj B (total-type B P) is-rezk-B
    ( \ (b : B) → (b, s b))
    ( projection-total-type B P)
    ( adj)
    ( is-LARI-proj)
    ( x)
  = s x
  := TODO
```

```rzk
#def is-initial-section-is-transposing-LARI-adj-projection-total-type
  ( B : U)
  ( P : B → U)
  ( is-rezk-B : is-rezk B)
  ( is-segal-P : is-segal (total-type B P))
  ( s : (b : B) → P b)
  ( adj : is-transposing-adj B (total-type B P)
          ( \ b → (b, s b))
          ( projection-total-type B P))
  ( is-LARI-proj : is-transposing-LARI-adj
                   ( B) ( total-type B P)
                   ( π₁ (is-rezk-B))
                   ( \ b → (b, s b))
                   ( projection-total-type B P)
                   ( adj))
  : is-initial-section B P s
  :=
  is-initial-section-is-transposing-LARI-adj
  ( B)
  ( total-type B P)
  ( is-rezk-B)
  ( is-segal-P)
  ( \ b → (b, s b))
  ( projection-total-type B P)
  ( adj)
  ( is-LARI-proj)
```

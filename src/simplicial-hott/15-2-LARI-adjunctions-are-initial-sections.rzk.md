# LARI adjunctions are initial sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
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

#def is-full-emb-hom-eq-is-transposing-adj-is-rezk uses (adj is-rezk-A)
  ( a : A)
  ( b : B)
  : is-full-emb (u b = a) (hom B (f a) b) (hom-eq-is-transposing-adj-is-rezk a b)
  :=
  is-full-emb-quadruple-comp funext
  ( u b = a)
  ( a = u b)
  ( Iso A (π₁ is-rezk-A) a (u b))
  ( hom A a (u b))
  ( hom B (f a) b)
  ( rev A (u b) a)
  ( is-full-emb-rev extext A (u b) a)
  ( iso-eq A (π₁ is-rezk-A) a (u b))
  ( is-full-emb-is-equiv extext
    ( a = u b)
    ( Iso A (π₁ is-rezk-A) a (u b))
    ( iso-eq A (π₁ is-rezk-A) a (u b))
    ( π₂ is-rezk-A a (u b)))
  ( \ f → π₁ f)
  ( is-full-emb-isos TODO extext A (π₁ is-rezk-A) a (u b))
  ( π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
  ( is-full-emb-is-equiv extext
    ( hom A a (u b))
    ( hom B (f a) b)
    ( π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
    ( π₂ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b))))

#def total-hom-iso
  ( a : A)
  ( (b, g) : Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b))
  : Σ (b : B) , hom A a (u b)
  := (b, π₁ g)

#def total-hom-iso-ap-hom-inv
  ( a : A)
  ( x y : (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)))
  ( g : hom (Σ (b : B) , hom A a (u b)) (total-hom-iso a x) (total-hom-iso a y))
  : hom (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) x y
  :=
  \ t → ( π₁ (g t)
  , ( π₂ (g t)
    , is-iso-arrow-nat-trans-is-iso-arrow-boundary
      ( A)
      ( π₁ is-rezk-A)
      ( a) a
      ( u (π₁ x)) (u (π₁ y))
      ( id-hom A a) ( \ s → u (π₁ (g s)))
      ( \ s → π₂ (g s))
      ( π₂ (π₂ x))
      ( π₂ (π₂ y))
      ( t)))

#def dhom-dhom-htpy-elem
  ( a : A)
  ( (x₁, x₂) (y₁, y₂) : (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)))
  ( g : hom B x₁ y₁)
  ( γ : dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂)
  : dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂
  :=
  ( \ t → (π₁ (γ t)
    , is-iso-arrow-nat-trans-is-iso-arrow-boundary
      ( A)
      ( π₁ is-rezk-A)
      ( a) a
      ( u x₁) (u y₁)
      ( id-hom A a) ( \ s → u (g s))
      ( \ s → π₁ (γ s))
      ( π₂ x₂)
      ( π₂ y₂)
      ( t)))

#def dhom-dhom-htpy
  ( a : A)
  ( (x₁, x₂) (y₁, y₂) : (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)))
  ( g : hom B x₁ y₁)
  ( γ : dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂)
  : dhom-dhom-htpy-elem a (x₁, x₂) (y₁, y₂) g γ = γ
  :=
  eq-dhom-extext extext B x₁ y₁ g
  ( \ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂
  ( dhom-dhom-htpy-elem a (x₁, x₂) (y₁, y₂) g γ)
  ( γ)
  ( \ t →
    ( eq-iso-eq-base-is-segal extext A (π₁ is-rezk-A) a (u (g t))
      ( dhom-dhom-htpy-elem a (x₁, x₂) (y₁, y₂) g γ t)
      ( γ t)
      ( refl_{ (π₁ (γ t)) : hom A a (u (g t))})))

#def is-equiv-dhom-iso-dhom-hom
  ( a : A)
  ( (x₁, x₂) (y₁, y₂) : (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)))
  ( g : hom B x₁ y₁)
  : is-equiv
    ( dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂)
    ( dhom B x₁ y₁ g (\ b → hom A a (u b)) (π₁ x₂) (π₁ y₂))
    ( \ γ t → π₁ (γ t))
  :=
  is-equiv-has-inverse
  ( dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂)
  ( dhom B x₁ y₁ g (\ b → hom A a (u b)) (π₁ x₂) (π₁ y₂))
  ( \ γ t → π₁ (γ t))
  ( \ γ t → (γ t
    , is-iso-arrow-nat-trans-is-iso-arrow-boundary
      ( A)
      ( π₁ is-rezk-A)
      ( a) a
      ( u x₁) (u y₁)
      ( id-hom A a) ( \ s → u (g s))
      ( γ)
      ( π₂ x₂)
      ( π₂ y₂)
      ( t))
  , ( \ γ → eq-dhom-extext extext B x₁ y₁ g
          ( \ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂
          ( \ t →
            ( π₁ (γ t)
            , is-iso-arrow-nat-trans-is-iso-arrow-boundary
              ( A)
              ( π₁ is-rezk-A)
              ( a) a
              ( u x₁) (u y₁)
              ( id-hom A a) ( \ s → u (g s))
              ( \ s → π₁ (γ s))
              ( π₂ x₂)
              ( π₂ y₂)
              ( t)))
          ( \ t → γ t)
          ( \ t →
            ( eq-iso-eq-base-is-segal extext A (π₁ is-rezk-A) a (u (g t))
              ( π₁ (γ t)
                , is-iso-arrow-nat-trans-is-iso-arrow-boundary
                  ( A)
                  ( π₁ is-rezk-A)
                  ( a) a
                  ( u x₁) (u y₁)
                  ( id-hom A a) (\ s → u (g s))
                  ( \ s → π₁ (γ s))
                  ( π₂ x₂)
                  ( π₂ y₂)
                  ( t))
              ( γ t)
              ( refl_{ (π₁ (γ t)) : hom A a (u (g t))})))
    , \ _ → refl))

#def is-full-emb-total-hom-iso
  ( a : A)
  : is-full-emb (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) (Σ (b : B) , hom A a (u b)) (total-hom-iso a)
  :=
  \ x y → is-equiv-has-inverse
  ( hom (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) x y)
  ( hom (Σ (b : B) , hom A a (u b)) (total-hom-iso a x) (total-hom-iso a y))
  ( ap-hom (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) (Σ (b : B) , hom A a (u b)) (total-hom-iso a) x y)
  ( \ g t →
    ( π₁ (g t)
    , (π₂ (g t)
      , is-iso-arrow-nat-trans-is-iso-arrow-boundary
        ( A)
        ( π₁ is-rezk-A)
        ( a) a
        ( u (π₁ x)) (u (π₁ y))
        ( id-hom A a) ( \ s → u (π₁ (g s)))
        ( \ s → π₂ (g s))
        ( π₂ (π₂ x))
        ( π₂ (π₂ y))
        ( t)))
  , ( \ g → ap
      ( Σ (h : hom B (π₁ x) (π₁ y))
        , dhom B (π₁ x) (π₁ y) h (\ b → Iso A (π₁ is-rezk-A) a (u b)) (π₂ x) (π₂ y))
      ( hom (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) x y)
      ( \ t → π₁ (g t), \ t →
        ( π₁ (π₂ (g t))
        , is-iso-arrow-nat-trans-is-iso-arrow-boundary
          ( A)
          ( π₁ is-rezk-A)
          ( a) a
          ( u (π₁ x)) (u (π₁ y))
          ( id-hom A a) ( \ s → u (π₁ (g s)))
          ( \ s → π₁ (π₂ (g s)))
          ( π₂ (π₂ x))
          ( π₂ (π₂ y))
          ( t)))
      ( \ t → π₁ (g t), \ t → π₂ (g t))
      ( hom-sigma-dhom B (\ b → Iso A (π₁ is-rezk-A) a (u b)) x y)
      ( path-of-pairs-pair-of-paths
        ( hom B (π₁ x) (π₁ y))
        ( \ h → dhom B (π₁ x) (π₁ y) h (\ b → Iso A (π₁ is-rezk-A) a (u b)) (π₂ x) (π₂ y))
        ( \ t → π₁ (g t))
        ( \ t → π₁ (g t))
        ( refl)
        ( \ t →
          ( π₁ (π₂ (g t))
          , is-iso-arrow-nat-trans-is-iso-arrow-boundary
            ( A)
            ( π₁ is-rezk-A)
            ( a) a
            ( u (π₁ x)) (u (π₁ y))
            ( id-hom A a) ( \ s → u (π₁ (g s)))
            ( \ s → π₁ (π₂ (g s)))
            ( π₂ (π₂ x))
            ( π₂ (π₂ y))
            ( t)))
        ( \ t → π₂ (g t))
        ( eq-dhom-extext TODO B (π₁ x) (π₁ y) (\ t → π₁ (g t))
          ( \ b → Iso A (π₁ is-rezk-A) a (u b))
          ( π₂ x) (π₂ y)
          ( \ t →
            ( π₁ (π₂ (g t))
            , is-iso-arrow-nat-trans-is-iso-arrow-boundary
              ( A)
              ( π₁ is-rezk-A)
              ( a) a
              ( u (π₁ x)) (u (π₁ y))
              ( id-hom A a) ( \ s → u (π₁ (g s)))
              ( \ s → π₁ (π₂ (g s)))
              ( π₂ (π₂ x))
              ( π₂ (π₂ y))
              ( t)))
          ( \ t → π₂ (g t))
          ( \ t →
            ( eq-iso-eq-base-is-segal extext A (π₁ is-rezk-A) a (u (π₁ (g t)))
              ( π₁ (π₂ (g t))
                , is-iso-arrow-nat-trans-is-iso-arrow-boundary
                  ( A)
                  ( π₁ is-rezk-A)
                  ( a) a
                  ( u (π₁ x)) (u (π₁ y))
                  ( id-hom A a) ( \ s → u (π₁ (g s)))
                  ( \ s → π₁ (π₂ (g s)))
                  ( π₂ (π₂ x))
                  ( π₂ (π₂ y))
                  ( t))
              ( π₂ (g t))
              ( refl)))))
    , \ g2 → {-F (G g) = g-} refl
    ))

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
  ( is-full-emb-rev extext A (u b) a)
  ( \ (b, p) → (b, iso-eq A (π₁ is-rezk-A) a (u b) p))
  ( is-full-emb-is-equiv extext
    ( rev-fib B A u a)
    ( Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b))
    ( \ (b, p) → (b, iso-eq A (π₁ is-rezk-A) a (u b) p))
    ( π₂ is-rezk-A a (u b)))
  ( total-hom-iso a)
  ( is-full-emb-total-hom-iso a)
  ( \ (b, g) → (b, π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)) g))
  ( is-full-emb-is-equiv extext
    ( hom A a (u b))
    ( hom B (f a) b)
    ( π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
    ( π₂ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b))))

{-
#def is-full-emb-sigma-hom-fib-is-transposing-adj-is-rezk
  uses (adj is-rezk-A funext extext)
  ( a : A)
  : is-full-emb (fib B A u a) (Σ (b : B) , hom B (f a) b)
  ( sigma-hom-fib-is-transposing-adj-is-rezk a)
  :=
  is-full-emb-total-type-is-full-emb-fiber TODO B (\ b → u b = a) (\ b → hom B (f a) b)
  ( hom-eq-is-transposing-adj-is-rezk a)
  ( is-full-emb-hom-eq-is-transposing-adj-is-rezk a)
  -}

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
  uses (is-LARI-f-u adj is-rezk-A f funext extext TODO)
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

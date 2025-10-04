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

#def dhom-dhom-htpy-elem
  ( a : A)
  ( (x₁, x₂) (y₁, y₂) : (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)))
  ( g : hom B x₁ y₁)
  ( γ : dhom B x₁ y₁ g (\ b → hom A a (u b)) (π₁ x₂) (π₁ y₂))
  : dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂
  :=
  iso-square-sides-iso-is-rezk A is-rezk-A
  ( a) (a) (u x₁) (u y₁)
  ( \ t → γ t 0₂)
  ( \ t → γ t 1₂)
  ( x₂)
  ( y₂)
  ( \ (t, s) → γ t s)
  {-( \ t → (γ t
    , is-iso-arrow-nat-trans-is-iso-arrow-boundary
      ( A)
      ( is-rezk-A)
      ( a) a
      ( u x₁) (u y₁)
      ( id-hom A a)
      ( \ s → u (g s))
      ( γ)
      ( π₂ x₂)
      ( π₂ y₂)
      ( t)))-}

#def dhom-dhom-htpy
  ( a : A)
  ( (x₁, x₂) (y₁, y₂) : (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)))
  ( g : hom B x₁ y₁)
  ( γ : dhom B x₁ y₁ g (\ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂)
  : dhom-dhom-htpy-elem a (x₁, x₂) (y₁, y₂) g (\ t → π₁ (γ t)) = γ
  :=
  eq-dhom-extext extext B x₁ y₁ g
  ( \ b → Iso A (π₁ is-rezk-A) a (u b)) x₂ y₂
  ( dhom-dhom-htpy-elem a (x₁, x₂) (y₁, y₂) g (\ t → π₁ (γ t)))
  ( γ)
  ( \ t → path-of-pairs-pair-of-paths (hom A a (u (g t)))
    ( is-iso-arrow A (π₁ is-rezk-A) a (u (g t)))
    ( π₁ (γ t)) (π₁ (γ t)) refl
    ( π₂ (dhom-dhom-htpy-elem a (x₁, x₂) (y₁, y₂) g (\ s → π₁ (γ s)) t)) (π₂ (γ t))
    ( ctie
      ( \ s → is-iso-arrow A (π₁ is-rezk-A) a (u (g s)) (π₁ (γ s)))
      ( \ s → is-contr-is-inhabited-is-prop
        ( is-iso-arrow A (π₁ is-rezk-A) a (u (g s)) (π₁ (γ s)))
        ( is-prop-is-iso-arrow extext A (π₁ is-rezk-A) a (u (g s)) (π₁ (γ s)))
        ( π₂ (γ s)))
      ( π₂ x₂)
      ( π₂ y₂)
      ( \ s → π₂ (dhom-dhom-htpy-elem a (x₁, x₂) (y₁, y₂) g (\ s' → π₁ (γ s')) s))
      ( \ s → π₂ (γ s))
      ( t)))

#def is-equiv-dhom-iso-dhom-hom uses (extext)
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
  ( \ γ → dhom-dhom-htpy-elem a (x₁, x₂) (y₁, y₂) g γ
  , ( \ γ → dhom-dhom-htpy a (x₁, x₂) (y₁, y₂) g γ
    , \ _ → refl))

#def is-full-emb-total-hom-iso uses (extext)
  ( a : A)
  : is-full-emb (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) (Σ (b : B) , hom A a (u b)) (total-hom-iso a)
  :=
  \ x y → is-equiv-has-inverse
  ( hom (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) x y)
  ( hom (Σ (b : B) , hom A a (u b)) (total-hom-iso a x) (total-hom-iso a y))
  ( ap-hom (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) (Σ (b : B) , hom A a (u b)) (total-hom-iso a) x y)
  ( \ g t →
    ( π₁ (g t)
    , dhom-dhom-htpy-elem a x y (\ s → π₁ (g s)) (\ s → π₂ (g s)) t)
  , ( \ g → ap
      ( Σ (h : hom B (π₁ x) (π₁ y))
        , dhom B (π₁ x) (π₁ y) h (\ b → Iso A (π₁ is-rezk-A) a (u b)) (π₂ x) (π₂ y))
      ( hom (Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b)) x y)
      ( \ t → π₁ (g t)
      , dhom-dhom-htpy-elem a x y (\ s → π₁ (g s)) (\ s → π₁ (π₂ (g s))))
      ( \ t → π₁ (g t), \ t → π₂ (g t))
      ( hom-sigma-dhom B (\ b → Iso A (π₁ is-rezk-A) a (u b)) x y)
      ( path-of-pairs-pair-of-paths
        ( hom B (π₁ x) (π₁ y))
        ( \ h → dhom B (π₁ x) (π₁ y) h (\ b → Iso A (π₁ is-rezk-A) a (u b)) (π₂ x) (π₂ y))
        ( \ t → π₁ (g t))
        ( \ t → π₁ (g t))
        ( refl)
        ( dhom-dhom-htpy-elem a x y (\ s → π₁ (g s)) (\ s → π₁ (π₂ (g s))))
        ( \ t → π₂ (g t))
        ( dhom-dhom-htpy a x y (\ s → π₁ (g s)) (\ s → π₂ (g s))))
    , \ g2 → refl))

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

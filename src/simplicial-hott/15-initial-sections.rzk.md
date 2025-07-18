# Initial sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

Not all proofs are done in this file:

```rzk
#assume TODO : (A : U) → A
```

## Definition

```rzk
#section initial-sections

#variable A : U
#variable B : A → U

#def is-initial-section
  ( s : (a : A) → B a)
  : U
  := (x : A) → is-initial (B x) (s x)

#def initial-section
  : U
  := Σ (s : (a : A) → B a) , is-initial-section s
```

We later want to show that this defines a LARI family. For the proof of this,
we need an a priori more powerful definition.

## Dependent initial sections

```rzk
#def is-dhom-initial-section
  ( s : (a : A) → B a)
  : U
  := (x : A) → (y : A) → (Y : B y) → (f : hom A x y)
  → is-contr (dhom A x y f B (s x) Y)

#def dhom-initial-section
  : U
  := Σ (s : (a : A) → B a) , is-dhom-initial-section s
```

We will now show that these are actually the same. The first direction is
simple:

```rzk
#def is-initial-section-is-dhom-initial-section
  ( s : (a : A) → B a)
  ( is-dhom-initial-section-s : is-dhom-initial-section s)
  : is-initial-section s
  :=
  \ (x : A) (X : B x) → is-contr-equiv-is-contr
  ( dhom A x x (id-hom A x) B (s x) X)
  ( hom (B x) (s x) X)
  ( equiv-hom-dhom A x B (s x) X)
  ( is-dhom-initial-section-s x x X (id-hom A x))
```

The second one requires a bit more work:

```rzkk
#section is-dhom-final-section-is-final-section

#variable is-segal-A : is-segal A
#variable is-dsegal-B : is-dsegal A is-segal-A B
#variable s : (a : A) → B a
#variable is-final-section-s : is-final-section s

#def center-dhom-temp
  ( a a' : A)
  ( f : hom A a a')
  ( b : B a)
  : dhom A a a' f B b (s a')
  :=
  transport
  ( hom A a a')
  ( \ f' → dhom A a a' f' B b (s a'))
  ( comp-is-segal A is-segal-A a a a' (id-hom A a) f)
  ( f)
  ( id-comp-is-segal A is-segal-A a a' f)
  ( dcomp-is-dsegal A is-segal-A B is-dsegal-B a a a'
    ( id-hom A a)
    ( f)
    ( b)
    ( s a)
    ( s a')
    ( dhom-hom A a B b (s a)
      ( center-contraction (hom (B a) b (s a)) (is-final-section-s a b)))
    ( \ t → s (f t)))

#def diag-dhom-temp
  ( a a' : A)
  ( f : hom A a a')
  ( b : B a)
  ( g : dhom A a a' f B b (s a'))
  : dhom A a a' f B b (s a')
  :=
  ( \ t → center-contraction
    ( hom (B (f t)) (g t) (s (f t)))
    ( is-final-section-s (f t) (g t))
    ( t))

{-

  b  -- g -- s a'
  |           |
 ctr        id-hom
  |           |
 s a -- _ -- s a'
        ^ s.lift f

-}

#def dhom2-center-diag-temp
  ( a a' : A)
  ( f : hom A a a')
  ( b : B a)
  ( g : dhom A a a' f B b (s a'))
  : dhom2
    ( A) a a' a' f (id-hom A a') f (comp-id-witness A a a' f)
    ( B) b (s a') (s a')
    ( g)
    ( id-dhom A a' B (s a'))
    ( diag-dhom-temp a a' f b g)
  :=
  \ (t₁ , t₂) → center-contraction
  ( hom (B (f t₁)) (g t₁) (s (f t₁)))
  ( is-final-section-s (f t₁) (g t₁))
  ( t₂)

#def dhom2-g-diag-temp
  ( a a' : A)
  ( f : hom A a a')
  ( b : B a)
  ( g : dhom A a a' f B b (s a'))
  : dhom2
    ( A) a a a' (id-hom A a) f f (id-comp-witness A a a' f)
    ( B) b b (s a')
    ( id-dhom A a B b)
    ( g)
    ( diag-dhom-temp a a' f b g)
  :=
  \ (t₁ , t₂) → center-contraction
  ( hom (B (f t₂)) (g t₂) (s (f t₂)))
  ( is-final-section-s (f t₂) (g t₂))
  ( t₁)

#def is-contr-dhom-temp
  ( a a' : A)
  ( f : hom A a a')
  ( b : B a)
  : is-contr (dhom A a a' f B b (s a'))
  :=
  ( center-dhom-temp a a' f b
  , \ g → concat
    ( dhom A a a' f B b (s a'))
    ( center-dhom-temp a a' f b)
    ( diag-dhom-temp a a' f b g)
    ( g)
    ( eq-homotopy-dhom2-is-dsegal TODO A is-segal-A B is-dsegal-B a a' f
      ( b) (s a')
      ( center-dhom-temp a a' f b)
      ( diag-dhom-temp a a' f b g)
      ( dhom2-center-diag-temp a a' f b g))
    ( rev
      ( dhom A a a' f B b (s a'))
      ( g)
      ( \ t → center-contraction
        ( hom (B (f t)) (g t) (s (f t)))
        ( is-final-section-s (f t) (g t))
        ( t))
      ( eq-homotopy-dhom2-is-dsegal TODO A is-segal-A B is-dsegal-B a a' f
        ( b) (s a')
        ( g)
        ( diag-dhom-temp a a' f b g)
        ( dhom2-g-diag-temp a a' f b g))))

#def is-dhom-final-section-is-final-section
  uses (B A TODO is-dsegal-B is-segal-A is-final-section-s)
  : dhom-final-section
  :=
  ( s
  , \ (a : A) (a' : A) (b : B a) (f : hom A a a') →
    is-contr-dhom-temp a a' f b)

#end is-dhom-final-section-is-final-section
```

```rzk
#end initial-sections
```

## Initial section are LARI

Now we want to show that an initial section is transposing LARI. Firstly, we
show that it is a transposing adjunction:

```rzk
#def is-transposing-adj-is-dhom-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dhom-initial-section-s : is-dhom-initial-section A B s)
  : is-transposing-adj A (total-type A B)
  ( \ a → (a , s a))
  ( projection-total-type A B)
  := \ x (y , Y) → equiv-comp
  ( hom (total-type A B) (x , s x) (y , Y))
  ( Σ ( f : hom A x y) , dhom A x y f B (s x) Y)
  ( hom A x y)
  ( equiv-hom-sigma-dhom A B (x , s x) (y , Y))
  ( equiv-total-type-is-contr
    ( hom A x y)
    ( \ f → dhom A x y f B (s x) Y)
    ( is-dhom-initial-section-s x y Y))
```

```rzk
#def is-transposing-LARI-is-dhom-initial-section
  ( A : U)
  ( is-segal-A : is-segal A)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dhom-initial-section-s : is-dhom-initial-section A B s)
  : is-transposing-LARI A (total-type A B) is-segal-A (\ a → (a , s a))
  :=
  ( projection-total-type A B
  , ( is-transposing-adj-is-dhom-initial-section A B s is-dhom-initial-section-s
    , \ a → is-iso-arrow-id-hom A is-segal-A a))
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

#def is-emb-hom-eq-is-transposing-adj-is-rezk uses (adj is-rezk-A)
  ( a : A)
  ( b : B)
  : is-emb (u b = a) (hom B (f a) b) (hom-eq-is-transposing-adj-is-rezk a b)
  :=
  is-emb-quadruple-comp funext
  ( u b = a)
  ( a = u b)
  ( Iso A (π₁ is-rezk-A) a (u b))
  ( hom A a (u b))
  ( hom B (f a) b)
  ( rev A (u b) a)
  ( is-emb-rev A (u b) a)
  ( iso-eq A (π₁ is-rezk-A) a (u b))
  ( is-emb-is-equiv
    ( a = u b)
    ( Iso A (π₁ is-rezk-A) a (u b))
    ( iso-eq A (π₁ is-rezk-A) a (u b))
    ( π₂ is-rezk-A a (u b)))
  ( \ f → π₁ f)
  ( is-emb-isos extext A (π₁ is-rezk-A) a (u b))
  ( π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
  ( is-emb-is-equiv
    ( hom A a (u b))
    ( hom B (f a) b)
    ( π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
    ( π₂ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b))))

#def sigma-hom-fib-is-transposing-adj-is-rezk uses (adj is-rezk-A)
  ( a : A)
  : fib B A u a → (Σ (b : B) , hom B (f a) b)
  := \ (b , p) → (b , hom-eq-is-transposing-adj-is-rezk a b p)

#def is-emb-sigma-hom-fib-is-transposing-adj-is-rezk
  uses (adj is-rezk-A funext extext)
  ( a : A)
  : is-emb (fib B A u a) (Σ (b : B) , hom B (f a) b)
  ( sigma-hom-fib-is-transposing-adj-is-rezk a)
  :=
  is-emb-total-type-is-emb-fiber B (\ b → u b = a) (\ b → hom B (f a ) b)
  ( hom-eq-is-transposing-adj-is-rezk a)
  ( is-emb-hom-eq-is-transposing-adj-is-rezk a)

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

#def tmpp uses (is-LARI-f-u adj u is-rezk-A)
  ( a : A)
  : (f a, id-hom B (f a))
  =_{coslice B (f a)} (sigma-hom-fib-is-transposing-adj-is-rezk a (section-is-transposing-LARI-adj a))
  :=
  TODO ((f a, id-hom B (f a))
  =_{coslice B (f a)} (sigma-hom-fib-is-transposing-adj-is-rezk a (section-is-transposing-LARI-adj a)))

#def is-initial-section-is-transposing-LARI-adj
  uses (is-LARI-f-u adj is-rezk-A f funext extext)
  : is-initial-section A (fib B A u) section-is-transposing-LARI-adj
  :=
  \ a → is-initial-is-emb TODO (fib B A u a) (Σ (b : B) , hom B (f a) b)
  ( sigma-hom-fib-is-transposing-adj-is-rezk a)
  ( is-emb-sigma-hom-fib-is-transposing-adj-is-rezk a)
  ( section-is-transposing-LARI-adj a)
  ( transport (coslice B (f a)) (\ x → is-initial (coslice B (f a)) x)
    ( f a, id-hom B (f a))
    ( sigma-hom-fib-is-transposing-adj-is-rezk a (section-is-transposing-LARI-adj a))
    ( tmpp a)
    ( is-initial-id-hom-is-segal B is-segal-B (f a)))


#end is-initial-section-is-transposing-LARI-adj-is-rezk
```

# Final sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Not all proofs are done in this file:

```rzk
#assume TODO : (A : U) → A
```

```rzk
-- #assume extext : ExtExt
```

## Initial definitions

```rzk
#section final-sections

#variable A : U
#variable B : A → U

#def is-final-section
  ( s : (a : A) → B a)
  : U
  := (a : A) → is-final (B a) (s a)

#def final-section
  : U
  := Σ (s : (a : A) → B a) , is-final-section s
```

We want to show that this actually defines a LARI family. For the proof of this,
we need to the auxiliary notion of a dependent final section.

## Dependent final sections

Next, an a priori more restrictive definition for finality.

```rzk
#def is-dhom-final-section
  ( s : (a : A) → B a)
  : U
  := (a : A) → (a' : A) → (b : B a) → (f : hom A a a')
  → is-contr (dhom A a a' f B b (s a'))

#def dhom-final-section
  : U
  := Σ (s : (a : A) → B a) , is-dhom-final-section s
```

We will now show that these are actually the same. The first direction is
simple:

```rzk
#def final-section-dhom-final-section
    ( dhom-final-section-B : dhom-final-section)
  : final-section
  :=
    ( π₁ dhom-final-section-B
    , \ (a : A) (b : B a) →
      is-contr-equiv-is-contr
        ( dhom A a a (id-hom A a) B b (π₁ dhom-final-section-B a))
        ( hom (B a) b (π₁ dhom-final-section-B a))
        ( equiv-hom-dhom A a B b (π₁ dhom-final-section-B a))
        ( π₂ dhom-final-section-B a a b (id-hom A a)))
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
#end final-sections
```

## Final section are LARI

```rzk
#def is-transposing-adj-is-dhom-final-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dhom-final-section-s : is-dhom-final-section A B s)
  : is-transposing-adj (total-type A B) A
  ( projection-total-type A B)
  ( \ a → (a , s a))
  := \ (a , b) a' → equiv-comp
  ( hom A a a')
  ( Σ ( f : hom A a a') , dhom A a a' f B b (s a'))
  ( hom (total-type A B) (a , b) (a' , s a'))
  ( equiv-total-type-is-contr'
    ( hom A a a')
    ( \ f → dhom A a a' f B b (s a'))
    ( is-dhom-final-section-s a a' b))
  ( equiv-sigma-dhom-hom A B (a , b) (a' , s a'))
```

```rzk
#section is-transposing-LARI-is-dsegal-is-dhom-final-section

#variable A : U
#variable is-segal-A : is-segal A
#variable B : A → U
#variable is-dsegal-B : is-dsegal A is-segal-A B
#variable s : (a : A) → B a
#variable is-dhom-final-section-s : is-dhom-final-section A B s

#def is-transposing-LARI-is-dsegal-is-dhom-final-section
  : is-transposing-LARI (total-type A B) A
  ( is-segal-total-type-is-dsegal TODO A is-segal-A B is-dsegal-B)
  ( projection-total-type A B)
  :=
  ( \ a → (a , s a)
  , ( is-transposing-adj-is-dhom-final-section A B s is-dhom-final-section-s
    , \ (a , b) → TODO (is-iso-arrow (total-type A B)
      ( is-segal-total-type-is-dsegal TODO A is-segal-A B is-dsegal-B)
      ( a , b)
      ( a , s a)
      ( π₁
        ( is-transposing-adj-is-dhom-final-section A B s is-dhom-final-section-s
          ( a , b) a)
        ( id-hom A a)))))

#end is-transposing-LARI-is-dsegal-is-dhom-final-section
```

```rzkk
#section is-transposing-LARI-has-final-section-is-dsegal
#variable A : U
#variable is-segal-A : is-segal A
#variable B : A → U
#variable is-dsegal-B : is-dsegal A is-segal-A B
#variable has-final-section-B : has-final-section A B

#def X
  ( a a' : A)
  ( f : hom A a a')
  ( b : B a)
  : is-contr (dhom A a a' f B b (π₁ has-final-section-B a'))
  := TODO (is-contr (dhom A a a' f B b (π₁ has-final-section-B a')))

#def projection-section-has-final-section
  : A → total-type A B
  := \ a → (a, π₁ has-final-section-B a)

#def is-transposing-adj-has-final-section uses (has-final-section-B)
  : is-transposing-adj (total-type A B) A
    ( projection-total-type A B)
    ( projection-section-has-final-section)
  :=
  \ (a , b) a' → equiv-comp
    ( hom A a a')
    ( Σ ( f : hom A a a') , dhom A a a' f B b (π₁ has-final-section-B a'))
    ( hom (total-type A B) (a, b) (a', π₁ has-final-section-B a'))
    ( inv-equiv
      ( Σ ( f : hom A a a') , dhom A a a' f B b (π₁ has-final-section-B a'))
      ( hom A a a')
      ( equiv-total-type-is-contr
        ( hom A a a')
        ( \ f → dhom A a a' f B b (π₁ has-final-section-B a'))
        ( \ f → X a a' f b)))
    ( equiv-sigma-dhom-hom A B (a , b) (a' , π₁ has-final-section-B a'))
```

```rzkk
#def is-transposing-LARI-has-final-section
  ( is-segal-total : is-segal (total-type A B))
  : is-transposing-LARI (total-type A B) A is-segal-total
    ( projection-total-type A B)
  :=
  (\ (f : (total-type A B) → A)
    (u : A → total-type A B)
  →
  (\ (adj : is-transposing-adj (total-type A B) A f u)
  →
  ( u
  , ( adj
    , \ ((a , b) : total-type A B) → TODO
      ( is-iso-arrow
        ( total-type A B)
        ( is-segal-total)
        ( a , b)
        ( u (f (a , b)))
        ( π₁
          ( adj (a , b) (f (a, b)))
          ( id-hom A (f (a , b)))))))
  )
  ( TODO (is-transposing-adj (total-type A B) A f u)) -- =: adj
  )
  ( projection-total-type A B) -- =: f
  ( \ a → (a, π₁ has-final-section-B a)) -- =: u
```

```rzk
-- #end is-transposing-LARI-has-final-section
```

# Initial sections are dependent initial sections

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

## Proof

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

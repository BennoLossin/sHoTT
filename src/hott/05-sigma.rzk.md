# 5. Sigma types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

It is convenient to have a shorthand for `Σ (x : A), B x` which avoids explicit
naming the variable `x : A`.

```rzk
#def total-type
  ( A : U)
  ( B : A → U)
  : U
  := Σ (x : A) , B x

#def projection-total-type
  ( A : U)
  ( B : A → U)
  : ( total-type A B) → A
  := \ z → first z
```

## Paths involving products

```rzk
#section paths-in-products

#variables A B : U

#def path-product
  ( a a' : A)
  ( b b' : B)
  ( e_A : a = a')
  ( e_B : b = b')
  : ( a , b) =_{product A B} (a' , b')
  :=
    transport A (\ x → (a , b) =_{product A B} (x , b')) a a' e_A
      ( transport B (\ y → (a , b) =_{product A B} (a , y)) b b' e_B refl)

#def first-path-product
  ( x y : product A B)
  ( e : x =_{product A B} y)
  : first x = first y
  := ap (product A B) A x y (\ z → first z) e

#def second-path-product
  ( x y : product A B)
  ( e : x =_{product A B} y)
  : second x = second y
  := ap (product A B) B x y (\ z → second z) e

#end paths-in-products
```

## Identity types of Sigma types

```rzk
#section paths-in-sigma

#variable A : U
#variable B : A → U

#def first-path-Σ
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : first s = first t
  := ap (Σ (a : A) , B a) A s t (\ z → first z) e

#def second-path-Σ
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : ( transport A B (first s) (first t) (first-path-Σ s t e) (second s))
  = ( second t)
  :=
    ind-path
      ( Σ ( a : A) , B a)
      ( s)
      ( \ t' e' →
        ( transport A B
          ( first s) (first t') (first-path-Σ s t' e') (second s))
      = ( second t'))
      ( refl)
      ( t)
      ( e)
```

```rzk title="Rijke 22, Definition 9.3.1"
#def Eq-Σ
  ( s t : Σ (a : A) , B a)
  : U
  :=
    Σ ( p : (first s) = (first t))
    , ( transport A B (first s) (first t) p (second s)) = (second t)
```

```rzk title="Rijke 22, Definition 9.3.3"
#def pair-eq
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : Eq-Σ s t
  := (first-path-Σ s t e , second-path-Σ s t e)
```

A path in a fiber defines a path in the total space.

```rzk
#def eq-eq-fiber-Σ
  ( x : A)
  ( u v : B x)
  ( p : u = v)
  : ( x , u) =_{Σ (a : A) , B a} (x , v)
  := ind-path (B x) (u) (\ v' p' → (x , u) = (x , v')) (refl) (v) (p)
```

The following is essentially `#!rzk eq-pair` but with explicit arguments.

```rzk
#def path-of-pairs-pair-of-paths
  ( x y : A)
  ( p : x = y)
  : ( u : B x)
  → ( v : B y)
  → ( ( transport A B x y p u) = v)
  → ( x , u) =_{Σ (z : A) , B z} (y , v)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' → (u' : B x) → (v' : B y')
      → ( ( transport A B x y' p' u') = v')
      → ( x , u') =_{Σ (z : A) , B z} (y' , v'))
      ( \ u' v' q' → (eq-eq-fiber-Σ x u' v' q'))
      ( y)
      ( p)
```

```rzk title="The inverse to pair-eq"
#def eq-pair
  ( s t : Σ (a : A) , B a)
  ( e : Eq-Σ s t)
  : ( s = t)
  :=
    path-of-pairs-pair-of-paths
      ( first s) (first t) (first e) (second s) (second t) (second e)

#def eq-pair-pair-eq
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : ( eq-pair s t (pair-eq s t e)) = e
  :=
    ind-path
      ( Σ ( a : A) , (B a))
      ( s)
      ( \ t' e' → (eq-pair s t' (pair-eq s t' e')) = e')
      ( refl)
      ( t)
      ( e)
```

Here we've decomposed `#!rzk e : Eq-Σ s t` as `#!rzk (e0, e1)` and decomposed
`#!rzk s` and `#!rzk t` similarly for induction purposes.

```rzk
#def pair-eq-eq-pair-split
  ( s0 : A)
  ( s1 : B s0)
  ( t0 : A)
  ( e0 : s0 = t0)
  : ( t1 : B t0)
  → ( e1 : (transport A B s0 t0 e0 s1) = t1)
  → ( ( pair-eq (s0 , s1) (t0 , t1) (eq-pair (s0 , s1) (t0 , t1) (e0 , e1)))
      =_{Eq-Σ (s0 , s1) (t0 , t1)}
      ( e0 , e1))
  :=
    ind-path
      ( A)
      ( s0)
      ( \ t0' e0' →
        ( t1 : B t0')
      → ( e1 : (transport A B s0 t0' e0' s1) = t1)
      → ( pair-eq (s0 , s1) (t0' , t1) (eq-pair (s0 , s1) (t0' , t1) (e0' , e1)))
        =_{Eq-Σ (s0 , s1) (t0' , t1)}
        ( e0' , e1))
      ( ind-path
        ( B s0)
        ( s1)
        ( \ t1' e1' →
          ( pair-eq
            ( s0 , s1)
            ( s0 , t1')
            ( eq-pair (s0 , s1) (s0 , t1') (refl , e1')))
          =_{Eq-Σ (s0 , s1) (s0 , t1')}
          ( refl , e1'))
        ( refl))
      ( t0)
      ( e0)

#def pair-eq-eq-pair
  ( s t : Σ (a : A) , B a)
  ( e : Eq-Σ s t)
  : ( pair-eq s t (eq-pair s t e)) =_{Eq-Σ s t} e
  :=
    pair-eq-eq-pair-split
      ( first s) (second s) (first t) (first e) (second t) (second e)


#def extensionality-Σ
  ( s t : Σ (a : A) , B a)
  : Equiv (s = t) (Eq-Σ s t)
  :=
    ( pair-eq s t
    , ( ( eq-pair s t , eq-pair-pair-eq s t)
      , ( eq-pair s t , pair-eq-eq-pair s t)))

#end paths-in-sigma

#def first-path-Σ-eq-pair
  ( A : U)
  ( B : A → U)
  ( ( a , b) (a' , b') : Σ (a : A) , B a)
  ( ( e0 , e1) : Eq-Σ A B (a , b) (a' , b'))
  : first-path-Σ A B (a , b) (a' , b') (eq-pair A B (a , b) (a' , b') (e0 , e1)) = e0
  :=
    first-path-Σ
      ( a = a')
      ( \ p → transport A B a a' p b = b')
      ( pair-eq A B (a , b) (a' , b') (eq-pair A B (a , b) (a' , b') (e0 , e1)))
      ( e0 , e1)
      ( pair-eq-eq-pair A B (a , b) (a' , b') (e0 , e1))
```

## Identity types of Sigma types over a product

```rzk
#section paths-in-sigma-over-product

#variables A B : U
#variable C : A → B → U

#def product-transport
  ( a a' : A)
  ( b b' : B)
  ( p : a = a')
  ( q : b = b')
  ( c : C a b)
  : C a' b'
  :=
    ind-path
      ( B)
      ( b)
      ( \ b'' q' → C a' b'')
      ( ind-path (A) (a) (\ a'' p' → C a'' b) (c) (a') (p))
      ( b')
      ( q)

#def Eq-Σ-over-product
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  : U
  :=
    Σ ( p : (first s) = (first t))
    , ( Σ ( q : (first (second s)) = (first (second t)))
        , ( product-transport
            ( first s) (first t)
            ( first (second s)) (first (second t)) p q (second (second s))
          = ( second (second t))))
```

!!! warning

    The following definition of `#!rzk triple-eq`
    is the lazy definition with bad computational properties.

```rzk
#def triple-eq
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  ( e : s = t)
  : Eq-Σ-over-product s t
  :=
    ind-path
      ( Σ ( a : A) , (Σ (b : B) , C a b))
      ( s)
      ( \ t' e' → (Eq-Σ-over-product s t'))
      ( ( refl , (refl , refl)))
      ( t)
      ( e)
```

It's surprising that the following typechecks since we defined product-transport
by a dual path induction over both `#!rzk p` and `#!rzk q`, rather than by
saying that when `#!rzk p` is `#!rzk refl` this is ordinary transport.

```rzk title="The inverse with explicit arguments"
#def triple-of-paths-path-of-triples
  ( a a' : A)
  ( u u' : B)
  ( c : C a u)
  ( p : a = a')
  : ( q : u = u')
  → ( c' : C a' u')
  → ( r : product-transport a a' u u' p q c = c')
  → ( ( a , (u , c)) =_{(Σ (x : A) , (Σ (y : B) , C x y))} (a' , (u' , c')))
  :=
    ind-path
      ( A)
      ( a)
      ( \ a'' p' →
        ( q : u = u')
      → ( c' : C a'' u')
      → ( r : product-transport a a'' u u' p' q c = c')
      → ( ( a , (u , c)) =_{(Σ (x : A) , (Σ (y : B) , C x y))} (a'' , (u' , c'))))
      ( \ q c' r →
        eq-eq-fiber-Σ
          ( A) (\ x → (Σ (v : B) , C x v)) (a)
          ( u , c) (u' , c')
          ( path-of-pairs-pair-of-paths B (\ y → C a y) u u' q c c' r))
      ( a')
      ( p)

#def eq-triple
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  ( e : Eq-Σ-over-product s t)
  : ( s = t)
  :=
    triple-of-paths-path-of-triples
    ( first s) (first t)
    ( first (second s)) (first (second t))
    ( second (second s)) (first e)
    ( first (second e)) (second (second t))
    ( second (second e))

#def eq-triple-triple-eq
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  ( e : s = t)
  : ( eq-triple s t (triple-eq s t e)) = e
  :=
    ind-path
      ( Σ ( a : A) , (Σ (b : B) , C a b))
      ( s)
      ( \ t' e' → (eq-triple s t' (triple-eq s t' e')) = e')
      ( refl)
      ( t)
      ( e)
```

Here we've decomposed `#!rzk s`, `#!rzk t` and `#!rzk e` for induction purposes:

```rzk
#def triple-eq-eq-triple-split
  ( a a' : A)
  ( b b' : B)
  ( c : C a b)

  : ( p : a = a')
  → ( q : b = b')
  → ( c' : C a' b')
  → ( r : product-transport a a' b b' p q c = c')
  → ( triple-eq
      ( a , (b , c)) (a' , (b' , c'))
      ( eq-triple (a , (b , c)) (a' , (b' , c')) (p , (q , r))))
  = ( p , (q , r))
  :=
    ind-path
      ( A)
      ( a)
      ( \ a'' p' →
        ( q : b = b')
      → ( c' : C a'' b')
      → ( r : product-transport a a'' b b' p' q c = c')
      → ( triple-eq
          ( a , (b , c)) (a'' , (b' , c'))
          ( eq-triple (a , (b , c)) (a'' , (b' , c')) (p' , (q , r))))
      = ( p' , (q , r)))
      ( ind-path
        ( B)
        ( b)
        ( \ b'' q' →
          ( c' : C a b'')
        → ( r : product-transport a a b b'' refl q' c = c')
        → ( triple-eq
            ( a , (b , c)) (a , (b'' , c'))
            ( eq-triple (a , (b , c)) (a , (b'' , c')) (refl , (q' , r))))
        = ( refl , (q' , r)))
        ( ind-path
            ( C a b)
            ( c)
            ( \ c'' r' →
              triple-eq
                ( a , (b , c)) (a , (b , c''))
                ( eq-triple
                  ( a , (b , c)) (a , (b , c''))
                  ( refl , (refl , r')))
              = ( refl , (refl , r')))
            ( refl))
        ( b'))
      ( a')

#def triple-eq-eq-triple
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  ( e : Eq-Σ-over-product s t)
  : ( triple-eq s t (eq-triple s t e)) = e
  :=
    triple-eq-eq-triple-split
      ( first s) (first t)
      ( first (second s)) (first (second t))
      ( second (second s)) (first e)
      ( first (second e)) (second (second t))
      ( second (second e))

#def extensionality-Σ-over-product
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  : Equiv (s = t) (Eq-Σ-over-product s t)
  :=
    ( triple-eq s t
    , ( ( eq-triple s t , eq-triple-triple-eq s t)
      , ( eq-triple s t , triple-eq-eq-triple s t)))

#end paths-in-sigma-over-product
```

## Symmetry of products

```rzk
#def sym-product
  ( A B : U)
  : Equiv (product A B) (product B A)
  :=
    ( \ (a , b) → (b , a)
    , ( ( \ (b , a) → (a , b) , \ p → refl)
      , ( \ (b , a) → (a , b) , \ p → refl)))
```

## Fubini

Given a family over a pair of independent types, the order of summation is
unimportant.

```rzk
#def fubini-Σ
  ( A B : U)
  ( C : A → B → U)
  : Equiv (Σ (x : A) , Σ (y : B) , C x y) (Σ (y : B) , Σ (x : A) , C x y)
  :=
    ( \ t → (first (second t) , (first t , second (second t)))
    , ( ( \ t → (first (second t) , (first t , second (second t)))
        , \ t → refl)
      , ( \ t → (first (second t) , (first t , second (second t)))
        , \ t → refl)))
```

```rzk title="Products distribute inside Sigma types"
#def distributive-product-Σ
  ( A B : U)
  ( C : B → U)
  : Equiv (product A (Σ (b : B) , C b)) (Σ (b : B) , product A (C b))
  :=
    ( \ (a , (b , c)) → (b , (a , c))
    , ( ( \ (b , (a , c)) → (a , (b , c)) , \ z → refl)
      , ( \ (b , (a , c)) → (a , (b , c)) , \ z → refl)))
```

## Associativity

```rzk
#def associative-Σ
  ( A : U)
  ( B : A → U)
  ( C : (a : A) → B a → U)
  : Equiv
      ( Σ ( a : A) , Σ (b : B a) , C a b)
      ( Σ ( ab : Σ (a : A) , B a) , C (first ab) (second ab))
  :=
    ( \ (a , (b , c)) → ((a , b) , c)
    , ( ( \ ((a , b) , c) → (a , (b , c)) , \ _ → refl)
      , ( \ ((a , b) , c) → (a , (b , c)) , \ _ → refl)))
```

## Currying

This is the dependent version of the currying equivalence.

```rzk
#def equiv-dependent-curry
  ( A : U)
  ( B : A → U)
  ( C : (a : A) → B a → U)
  : Equiv
      ( ( p : Σ (a : A) , (B a)) → C (first p) (second p))
      ( ( a : A) → (b : B a) → C a b)
  :=
    ( ( \ s a b → s (a , b))
    , ( ( ( \ f (a , b) → f a b
          , \ f → refl)
        , ( \ f (a , b) → f a b
          , \ s → refl))))
```

## Type theoretic principle of choice

```rzk title="Rijke 22, Theorem 13.2.1"
#def choice
  ( A : U)
  ( B : A → U)
  ( C : (x : A) → B x → U)
  : ( ( x : A) → Σ (y : B x) , C x y)
  → ( Σ ( f : (x : A) → B x) , (x : A) → C x (f x))
  := \ h → (\ x → first (h x) , \ x → second (h x))

#def choice-inverse
  ( A : U)
  ( B : A → U)
  ( C : (x : A) → B x → U)
  : ( Σ ( f : (x : A) → B x) , (x : A) → C x (f x))
  → ( ( x : A) → Σ (y : B x) , C x y)
  := \ s → \ x → ((first s) x , (second s) x)

#def is-equiv-choice
  ( A : U)
  ( B : A → U)
  ( C : (x : A) → B x → U)
  : is-equiv
      ( ( x : A) → Σ (y : B x) , C x y)
      ( Σ ( f : (x : A) → B x) , (x : A) → C x (f x))
      ( choice A B C)
  :=
    is-equiv-has-inverse
      ( ( x : A) → Σ (y : B x) , C x y)
      ( Σ ( f : (x : A) → B x) , (x : A) → C x (f x))
      ( choice A B C)
      ( choice-inverse A B C , (\ h → refl , \ s → refl))

#def equiv-choice
  ( A : U)
  ( B : A → U)
  ( C : (x : A) → B x → U)
  : Equiv
    ( ( x : A) → Σ (y : B x) , C x y)
    ( Σ ( f : (x : A) → B x) , (x : A) → C x (f x))
  := (choice A B C , is-equiv-choice A B C)

#def inv-equiv-choice
  ( A : U)
  ( B : A → U)
  ( C : (x : A) → B x → U)
  : Equiv
    ( Σ ( f : (x : A) → B x) , (x : A) → C x (f x))
    ( ( x : A) → Σ (y : B x) , C x y)
  :=
  inv-equiv
  ( ( x : A) → Σ (y : B x) , C x y)
  ( Σ ( f : (x : A) → B x) , (x : A) → C x (f x))
  ( equiv-choice A B C)
```

## Equivalences and sigma types

```rzkk
#section is-equiv-total-type-is-equiv

#variables A A' : U
#variable B : A → U
#variable B' : A' → U
#variable f : A → A'
#variable is-equiv-f : is-equiv A A' f
#variable ff : (a : A) → B a → B' (f a)
#variable is-equiv-ff : (a : A) → is-equiv (B a) (B' (f a)) (ff a)

#assume TODO : (A : U) → A

#def u uses (f)
  : A' → A
  := π₁ (has-inverse-is-equiv A A' f is-equiv-f)

#def H11
  : (a : A) → u (f a) = a
  := π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f))

#def H21 uses (A)
  : (a' : A') → f (u a') = a'
  := π₂ (π₂ (has-inverse-is-equiv A A' f is-equiv-f))

#def uu uses (A')
  ( a : A)
  : B' (f a) → B a
  := π₁ (has-inverse-is-equiv (B a) (B' (f a)) (ff a) (is-equiv-ff a))

#def H12 uses (A')
  ( a : A)
  : (b : B a) → uu a (ff a b) = b
  := π₁ (π₂ (has-inverse-is-equiv (B a) (B' (f a)) (ff a) (is-equiv-ff a)))

#def H22 uses (A')
  ( a : A)
  : (b' : B' (f a)) → ff a (uu a b') = b'
  := π₂ (π₂ (has-inverse-is-equiv (B a) (B' (f a)) (ff a) (is-equiv-ff a)))

#def m
  : total-type A B → total-type A' B'
  := \ (a, b) → (f a, ff a b)

#def M2 uses (is-equiv-ff ff is-equiv-f A)
  ( a' : A')
  ( b' : B' a')
  : B (u a')
  :=
  uu (u a') (transport A' B' a' (f (u a')) (rev A' (f (u a')) a' (H21 a')) b')

#def M uses (is-equiv-ff ff is-equiv-f f)
  : total-type A' B' → total-type A B
  := \ (a', b') → (u a', M2 a' b')

#variable H-compat : (a : A) → H21 (f a) = ap A A' (u (f a)) a f (H11 a)

#def tmp-0
  ( a : A)
  ( b : B a)
  : transport A' B' (f a) (f (u (f a)))
    ( rev A' (f (u (f a))) (f a) (H21 (f a))) (ff a b)
  = ff (u (f a)) (transport A B a (u (f a)) (rev A (u (f a)) a (H11 a)) b)
  :=
  concat
    ( B' (f (u (f a))))
    ( transport A' B' (f a) (f (u (f a)))
      ( rev A' (f (u (f a))) (f a) (H21 (f a))) (ff a b))
    ( transport A' B' (f a) (f (u (f a)))
      ( rev A' (f (u (f a))) (f a) (ap A A' (u (f a)) a f (H11 a))) (ff a b))
    ( transport A' B' (f a) (f (u (f a)))
      ( ap A A' a (u (f a)) f (rev A (u (f a)) a (H11 a))) (ff a b))
    ( transport A (\ x → B' (f x)) a (u (f a)) (rev A (u (f a)) a (H11 a)) (ff a b))
    ( ?)
    ( ff (u (f a)) (transport A B a (u (f a)) (rev A (u (f a)) a (H11 a)) b))
    ( transport-substitution A A' B' f a (u (f a)) )
#def MMM
  ( a : A)
  ( b : B a)
  : M2 (f a) (ff a b) = transport A B a (u (f a)) (?) b
  -- uu (u (f a)) (transport A' B' (f a) (f (u (f a))) (rev A' (f (u (f a))) (f a) (H21 (f a))) (ff a b))
  -- uu a (ff a b)
  := H12 (u (f a))

#def is-equiv-total-type-is-equiv uses (is-equiv-ff ff is-equiv-f f)
  : is-equiv (total-type A B) (total-type A' B') m
  :=
  is-equiv-has-inverse (total-type A B) (total-type A' B') m
  ( M
  , ( \ (a, b) →
      -- M (m (a, b)) = (a, b)
      -- M (f a, ff a b) = (a, b)
      -- (u (f a), uu (u (f a)) (tr (ff a b))) = (a, b)
      path-of-pairs-pair-of-paths
      ( A)
      ( B)
      ( u (f a))
      ( a)
      ( H11 a)
      ( M2 (f a) (ff a b))
      ( b)
      ( concat
        ( B a)
        ( transport A B (u (f a)) a (H11 a) (M2 (f a) (ff a b)))
        ( transport A B (u (f a)) a (H11 a)
          ( transport A B a (u (f a)) (ap A' A u ()) b))
        b
        ( TODO
          ( transport A B (u (f a)) a (H11 a) (M2 (f a) (ff a b))
          = b))
    , \ (a', b') → TODO (m (M (a', b')) = (a', b'))))

#end is-equiv-total-type-is-equiv
```


```rzkk
#def is-equiv-total-type-fiber-is-equiv
  ( A : U)
  ( B B' : A → U)
  ( f : (a : A) → B a → B' a)
  ( is-equiv-f : (a : A) → is-equiv (B a) (B' a) (f a))
  : is-equiv (total-type A B) (total-type A B') (\ (a, b) → (a, f a b))
  :=
  is-equiv-has-inverse
  ( total-type A B)
  ( total-type A B')
  ( \ (a, b) → (a, f a b))
  ( \ (a, b') →
    ( a, π₁ (has-inverse-is-equiv (B a) (B' a) (f a) (is-equiv-f a)) b')
  , ( \ (a, b) →
      eq-eq-fiber-Σ A B a
      ( π₁ (has-inverse-is-equiv (B a) (B' a) (f a) (is-equiv-f a)) (f a b))
      ( b)
      ( π₁ (π₂ (has-inverse-is-equiv (B a) (B' a) (f a) (is-equiv-f a))) b)
    , \ (a, b') →
      eq-eq-fiber-Σ A B' a
      ( f a ( π₁ (has-inverse-is-equiv (B a) (B' a) (f a) (is-equiv-f a)) b'))
      ( b')
      ( π₂ (π₂ (has-inverse-is-equiv (B a) (B' a) (f a) (is-equiv-f a))) b')))

#section is-equiv-total-type-base-is-equiv

#variables A A' : U
#variable B : A → U
#variable f : A → A'
#variable is-equiv-f : is-equiv A A' f

-- inverse of f
#def temp-rLmx-u uses (f)
  : A' → A
  := π₁ (has-inverse-is-equiv A A' f is-equiv-f)

#def temp-rLmx-map
  ( (a , b) : total-type A B)
  : total-type A' (\ a' → B (temp-rLmx-u a'))
  :=
  ( f a
  , transport A B a (temp-rLmx-u (f a))
    ( rev A (temp-rLmx-u (f a)) a
      ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a)) b)

#assume TODO : (A : U) → A

#def is-equiv-total-type-base-is-equiv uses (f is-equiv-f)
  : is-equiv (total-type A B) (total-type A' (\ a' → B (temp-rLmx-u a')))
  ( temp-rLmx-map)
  :=
  is-equiv-has-inverse
  ( total-type A B)
  ( total-type A' (\ a' → B (temp-rLmx-u a')))
  ( temp-rLmx-map)
  ( \ (a', b) → ( temp-rLmx-u a' , b)
  , ( \ (a , b) → path-of-pairs-pair-of-paths A B (temp-rLmx-u (f a)) a
      ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a)
      ( transport A B a (temp-rLmx-u (f a))
        ( rev A (temp-rLmx-u (f a)) a
          ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a)) b)
      ( b)
      ( transport-rev-transport A B (temp-rLmx-u (f a)) a
        ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a)
        ( b))
    , \ (a', b) →  path-of-pairs-pair-of-paths A' (\ a' → B (temp-rLmx-u a'))
      ( f (temp-rLmx-u a')) a'
      ( π₂ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a')
      ( transport A B (temp-rLmx-u a') (temp-rLmx-u (f (temp-rLmx-u a')))
        ( rev A (temp-rLmx-u (f (temp-rLmx-u a'))) (temp-rLmx-u a')
          ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) (temp-rLmx-u a'))) b)
      ( b)
      ( triple-concat
        ( B (temp-rLmx-u a'))
        ( transport
          ( A')
          ( \ (a' : A') → B (temp-rLmx-u a'))
          ( f (temp-rLmx-u a'))
          ( a')
          ( π₂ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a')
          ( transport
            ( A)
            ( B)
            ( temp-rLmx-u a')
            ( temp-rLmx-u (f (temp-rLmx-u a')))
            ( rev A (temp-rLmx-u (f (temp-rLmx-u a'))) (temp-rLmx-u a')
              ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f))
                ( temp-rLmx-u a'))) b))
        ( transport
          ( A)
          ( B)
          ( temp-rLmx-u (f (temp-rLmx-u a')))
          ( temp-rLmx-u a')
          ( ap A' A
            ( f (temp-rLmx-u a'))
            ( a')
            ( temp-rLmx-u)
            ( π₂ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a'))
          ( transport
            ( A)
            ( B)
            ( temp-rLmx-u a')
            ( temp-rLmx-u (f (temp-rLmx-u a')))
            ( rev A (temp-rLmx-u (f (temp-rLmx-u a'))) (temp-rLmx-u a')
              ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f))
                ( temp-rLmx-u a'))) b))
        ( b)
        ( transport-substitution A' A B temp-rLmx-u
          ( f (temp-rLmx-u a'))
          ( a')
          ( π₂ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a')
          ( transport
            ( A)
            ( B)
            ( temp-rLmx-u a')
            ( temp-rLmx-u (f (temp-rLmx-u a')))
            ( rev A (temp-rLmx-u (f (temp-rLmx-u a'))) (temp-rLmx-u a')
              ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f))
                ( temp-rLmx-u a'))) b))
        ( TODO
          ( transport
            ( A)
            ( B)
            ( temp-rLmx-u (f (temp-rLmx-u a')))
            ( temp-rLmx-u a')
            ( ap A' A
              ( f (temp-rLmx-u a'))
              ( a')
              ( temp-rLmx-u)
              ( π₂ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a'))
            ( transport
              ( A)
              ( B)
              ( temp-rLmx-u a')
              ( temp-rLmx-u (f (temp-rLmx-u a')))
              ( rev A (temp-rLmx-u (f (temp-rLmx-u a'))) (temp-rLmx-u a')
                ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f))
                  ( temp-rLmx-u a'))) b)
          =_{ B (temp-rLmx-u a') } b)))))

#end is-equiv-total-type-base-is-equiv
```

```rzkk

#section is-inverse-total-type-is-inverse

#assume TODO : (A : U) → A

#variable A : U
#variable B : A → U
#variable A' : U
#variable B' : A' → U
#variable f : A → A'
#variable u : A' → A
#variable is-inverse-f-u : is-inverse A A' f u
#variable ff : (a : A) → B a → B' (f a)
#variable uu : (a : A) → B' (f a) → B a
#variable is-inverse-ff-uu
  : (a : A) → is-inverse (B a) (B' (f a)) (ff a) (uu a)

#def map-total-type
  ((a, b) : total-type A B)
  : total-type A' B'
  := (f a, ff a b)

#def rev-map-total-type
  ((a', b') : total-type A' B')
  : total-type A B
  :=
  ( u a'
  , uu (u a') (transport A' B' a' (f (u a'))
    ( rev A' (f (u a')) a' (π₂ is-inverse-f-u a'))
    ( b')))


#def tmp-6
  ( a : A)
  : π₂ is-inverse-f-u (f a) = ap A A' (u (f a)) a f (π₁ is-inverse-f-u a)
  := refl

#def tmp-5
  ( a : A)
  : ap A A' a (u (f a)) f (rev A (u (f a)) a (π₁ is-inverse-f-u a))
  = rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a))
  := ap-rev A A' (u (f a)) a f (π₁ is-inverse-f-u a)

#def tmp-0
  (a : A)
  (b : B a)
  : transport
    ( A) (\ (a : A) → B' (f a))
    ( a) (u (f a))
    ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
    ( ff a b)
  =
    transport
    ( A') B'
    ( f a) (f (u (f a)))
    ( rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a)))
    ( ff a b)
  :=
  concat
    ( B' (f (u (f a))))
    ( transport
      ( A) (\ (a : A) → B' (f a))
      ( a) (u (f a))
      ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
      ( ff a b))
    ( transport
      ( A') B'
      ( f a) (f (u (f a)))
      ( ap A A' a (u (f a)) f (rev A (u (f a)) a (π₁ is-inverse-f-u a)))
      ( ff a b))
    ( transport
      ( A') B'
      ( f a) (f (u (f a)))
      ( rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a)))
      ( ff a b))
    ( transport-substitution
      ( A) A' B' f a (u (f a))
      ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
      ( ff a b))
    ( transport2
      ( A') B'
      ( f a) (f (u (f a)))
      ( ap A A' a (u (f a)) f (rev A (u (f a)) a (π₁ is-inverse-f-u a)))
      ( rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a)))
      ( TODO (( ap A A' a (u (f a)) f (rev A (u (f a)) a (π₁ is-inverse-f-u a)))
      =
      ( rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a)))))
      ( ff a b))

#def tmp-1 uses(TODO)
  (a : A)
  (b : B a)
  : transport
    ( A') B'
    ( f a) (f (u (f a)))
    ( rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a)))
    ( ff a b)
  = transport
    ( A) (\ (a : A) → B' (f a))
    ( a) (u (f a))
    ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
    ( ff a b)
  :=
  rev
  ( B' (f (u (f a))))
  ( transport
    ( A) (\ (a : A) → B' (f a))
    ( a) (u (f a))
    ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
    ( ff a b))
  ( transport
    ( A') B'
    ( f a) (f (u (f a)))
    ( rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a)))
    ( ff a b))
  ( tmp-0 a b)

#def tmp-2 uses(TODO)
  (a : A)
  (b : B a)
  : (uu (u (f a)) (transport A' B' (f a) (f (u (f a)))
    ( rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a)))
    ( ff a b)))
    = ( uu (u (f a)) (transport
      ( A) (\ (a : A) → B' (f a))
      ( a) (u (f a))
      ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
      ( ff a b)))
  :=
  ap
  ( B' (f (u (f a))))
  ( B (u (f a)))
  ( transport A' B' (f a) (f (u (f a)))
    ( rev A' (f (u (f a))) (f a) (π₂ is-inverse-f-u (f a)))
    ( ff a b))
  ( transport
      ( A) (\ (a : A) → B' (f a))
      ( a) (u (f a))
      ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
      ( ff a b))
  ( uu (u (f a)))
  ( tmp-1 a b)

#def is-inverse-total-type-is-inverse
  uses (uu ff is-inverse-f-u u f)
  : is-inverse
    ( total-type A B)
    ( total-type A' B')
    ( map-total-type)
    ( rev-map-total-type)
  :=
  ( \ (a , b) →
    path-of-pairs-pair-of-paths
    ( A)
    ( B)
    ( u (f a))
    ( a)
    ( π₁ is-inverse-f-u a)
    ( π₂ (rev-map-total-type (map-total-type (a, b))))
    ( b)
    ( quadruple-concat
      ( B a)
      ( transport
        ( A) B
        ( u (f a)) a
        ( π₁ is-inverse-f-u a)
        ( π₂ (rev-map-total-type (map-total-type (a, b)))))
      ( transport
        ( A) B
        ( u (f a)) a
        ( rev A a (u (f a)) (rev A (u (f a)) a (π₁ is-inverse-f-u a)))
        ( π₂ (rev-map-total-type (map-total-type (a, b)))))
      ( transport
        ( A) B
        ( u (f a)) a
        ( rev A a (u (f a)) (rev A (u (f a)) a (π₁ is-inverse-f-u a)))
        ( uu (u (f a)) (transport
          ( A) (\ (a : A) → B' (f a))
          ( a) (u (f a))
          ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
          ( ff a b))))
      ( uu a (ff a b))
      ( b)
      ( transport2
        ( A) B
        ( u (f a)) a
        ( π₁ is-inverse-f-u a)
        ( rev A a (u (f a)) (rev A (u (f a)) a (π₁ is-inverse-f-u a)))
        ( rev-rev' A (u (f a)) a (π₁ is-inverse-f-u a))
        ( π₂ (rev-map-total-type (map-total-type (a, b)))))
      ( transport-eq
        ( A) B
        ( u (f a)) a
        ( rev A a (u (f a)) (rev A (u (f a)) a (π₁ is-inverse-f-u a)))
        ( π₂ (rev-map-total-type (map-total-type (a, b))))
        ( uu (u (f a)) (transport
          ( A) (\ (a : A) → B' (f a))
          ( a) (u (f a))
          ( rev A (u (f a)) a (π₁ is-inverse-f-u a))
          ( ff a b)))
        ( tmp-2 a b))
      ( apd2 TODO A (\ a → B' (f a)) B a (u (f a)) uu (rev A (u (f a)) a (π₁ is-inverse-f-u a)) (ff a b))
      (π₁ (is-inverse-ff-uu a) b))
  , \ (a' , b') → TODO (map-total-type (rev-map-total-type (a', b')) = (a', b')))

#end is-inverse-total-type-is-inverse
```



```rzkk

#section is-equiv-total-type-is-equiv

#variable A : U
#variable B : A → U
#variable A' : U
#variable B' : A' → U
#variable f : A → A'
#variable is-equiv-f : is-equiv A A' f
#variable F : (a : A) → B a → B' (f a)
#variable is-equiv-F : (a : A) → is-equiv (B a) (B' (f a)) (F a)

#def map-total-type
  ((a, b) : total-type A B)
  : total-type A' B'
  := (f a, F a b)

#def rev-map-1-total-type-is-equiv
  ( a' : A')
  : A
  := π₁ (has-inverse-is-equiv A A' f is-equiv-f) a'

#def rev-map-2-total-type-is-equiv
  ( (a', b') : total-type A' B')
  : B (rev-map-1-total-type-is-equiv a')
  :=
  π₁ (has-inverse-is-equiv
    ( B (rev-map-1-total-type-is-equiv a'))
    ( B' (f (rev-map-1-total-type-is-equiv a')))
    ( F (rev-map-1-total-type-is-equiv a'))
    ( is-equiv-F (rev-map-1-total-type-is-equiv a')))
    ( transport A' B' a' (f (rev-map-1-total-type-is-equiv a'))
      ( rev A'
        ( f (rev-map-1-total-type-is-equiv a'))
        ( a')
        ( π₂ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) a')) b')

#def rev-map-total-type-is-equiv
  ((a', b') : total-type A' B')
  : total-type A B
  :=
  ( rev-map-1-total-type-is-equiv a'
  , rev-map-2-total-type-is-equiv (a' , b'))

#def is-equiv-total-type-is-equiv
  : is-equiv (total-type A B) (total-type A' B') map-total-type
  :=
  is-equiv-has-inverse
  ( total-type A B)
  ( total-type A' B')
  ( map-total-type)
  ( rev-map-total-type-is-equiv
  , ( \ (a , b) →
      {- u (f (a, b)) = (a, b) -}
      {- (u (f a), U (u (f a)) (F a b)) = (a, b) -}
      path-of-pairs-pair-of-paths
      A
      B
      ( rev-map-1-total-type-is-equiv (f a))
      ( a)
      ( π₁ (π₂ ( has-inverse-is-equiv A A' f is-equiv-f)) a)
      ( rev-map-2-total-type-is-equiv (f a, F a b))
      ( b)
      ( π₁ (π₂
        ( has-inverse-is-equiv
          ( B (rev-map-1-total-type-is-equiv (f a)))
          ( B' (f a))
          ( comp
            ( B (rev-map-1-total-type-is-equiv (f a)))
            ( B a)
            ( B' (f a))
            ( F a)
            ( transport A B
              ( rev-map-1-total-type-is-equiv (f a))
              ( a)
              ( π₁ (π₂ ( has-inverse-is-equiv A A' f is-equiv-f)) a)))
          ( is-equiv-F (rev-map-1-total-type-is-equiv (f a))))
        {-is-equiv
          ( B (rev-map-1-total-type-is-equiv (f (π₁ x₁))))
          ( B' (f (π₁ x₁)))
          ( comp
            ( B (rev-map-1-total-type-is-equiv (f (π₁ x₁))))
            ( B (π₁ x₁))
            ( B' (f (π₁ x₁)))
            ( F (π₁ x₁))
            ( transport A B
              ( rev-map-1-total-type-is-equiv (f (π₁ x₁)))
              ( π₁ x₁)
              ( π₁ (π₂ (has-inverse-is-equiv A A' f is-equiv-f)) (π₁ x₁))))-}
        ( F a b)) b)
    , \ (a', b') → {- f (u (a', b')) = (a', b') -}
      path-of-pairs-pair-of-paths
      A'
      B'
      ( f (rev-map-1-total-type-is-equiv a'))
      ( a')
      ( π₂ (π₂ ( has-inverse-is-equiv A A' f is-equiv-f)) a')
      ( rev-map-2-total-type-is-equiv (a', b'))
      ( π₂ (π₂
        ( has-inverse-is-equiv
          ( B (rev-map-1-total-type-is-equiv a'))
          ( B' a')
          ( F (rev-map-1-total-type-is-equiv a'))
          ( is-equiv-F (rev-map-1-total-type-is-equiv a')))
        ( b')) b')))

#end is-equiv-total-type-is-equiv
```

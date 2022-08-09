
```agda

{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes
  hiding (ua)

module Exercises6 where
```

In this problem set, you will look at a variation on the circle, a
higher inductive type for a "bowtie", i.e. two loops at a point.
(Unscaffolded harder exercise: do these problems for a "wedge of k
circles" for any natural number k.)

# HIT recursion from induction

In general, the dependent elimination rule for a higher inductive type
implies the simple/non-dependent elimination rule.  In this problem, you
will show this for the bowtie.  We could have done this for the circles
in the past lectures, but I wanted to introduce the non-dependent
elimination rule first, and then left both as postulates.

Note that this problem has a bit of a "metamathematical" flavor (showing
that a set of axioms is implied by a shorter set).  If you prefer to
jump right to the more "mathematical" problem of characterizing the loop
space of the bowtie below, I recommend turning Bowtie-rec and its
associated reductions into postulates like we have done for previous
higher inductive types, and adding a rewrite for the reduction on the
base point. This will make Agda display things in a more easy to read
way (otherwise, it will display Bowtie-rec as a meta-variable).

Here is the definition of the bowtie and its dependent elimination rule:

```agda
postulate
  Bowtie : Set
  baseB : Bowtie
  loop1 : baseB ≡ baseB
  loop2 : baseB ≡ baseB
  Bowtie-elim : {l : Level} (X : Bowtie → Type l)
                (x : X baseB)
                (p : x ≡ x [ X ↓ loop1 ])
                (q : x ≡ x [ X ↓ loop2 ])
                → (x : Bowtie) → X x
  Bowtie-elim-base : {l : Level} (X : Bowtie → Type l)
                     (x : X baseB)
                     (p : x ≡ x [ X ↓ loop1 ])
                     (q : x ≡ x [ X ↓ loop2 ])
                  → Bowtie-elim X x p q baseB ≡ x
{-# REWRITE Bowtie-elim-base #-}

postulate
  Bowtie-elim-loop1 : {l : Level} (X : Bowtie → Type l)
                      (x : X baseB)
                      (p : x ≡ x [ X ↓ loop1 ])
                      (q : x ≡ x [ X ↓ loop2 ])
                    → apd (Bowtie-elim X x p q) loop1 ≡ p
  Bowtie-elim-loop2 : {l : Level} (X : Bowtie → Type l)
                      (x : X baseB)
                      (p : x ≡ x [ X ↓ loop1 ])
                      (q : x ≡ x [ X ↓ loop2 ])
                    → apd (Bowtie-elim X x p q) loop2 ≡ q
```

Next, we will prove the non-dependent elim/"recursion principle" from
these. First, we need some lemmas.

(⋆) Paths over a path in a constant fibration are equivalent to paths.
It is simple to prove this by path induction.

```agda
PathOver-constant : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                  → {a1 a2 : A}
                  → (p : a1 ≡ a2)
                  → {b1 b2 : B}
                  → b1 ≡ b2
                  → b1 ≡ b2 [ (λ _ → B) ↓ p ]
PathOver-constant refll refll = reflo

PathOver-constant-inverse : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → b1 ≡ b2 [ (λ _ → B) ↓ p ]
                          → b1 ≡ b2
PathOver-constant-inverse refll reflo = refll

PathOver-constant-inverse-cancel1 : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (q : b1 ≡ b2)
                          → PathOver-constant-inverse p (PathOver-constant p q) ≡ q
PathOver-constant-inverse-cancel1 refll refll = refll

PathOver-constant-inverse-cancel2 : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (q : b1 ≡ b2 [ _ ↓ p ])
                          → PathOver-constant p (PathOver-constant-inverse p q) ≡ q
PathOver-constant-inverse-cancel2 refll reflo = refll

PathOver-constant-equiv : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (b1 ≡ b2) ≃ (b1 ≡ b2 [ (λ _ → B) ↓ p ])
PathOver-constant-equiv p = improve (Isomorphism (PathOver-constant p)
                                    (Inverse (PathOver-constant-inverse p)
                                             (PathOver-constant-inverse-cancel1 p)
                                             (PathOver-constant-inverse-cancel2 p)))

```

(⋆) Next, for a non-dependent function f, there is an annoying mismatch between
ap f and apd f, which we can reconcile as follows:

```agda
ap-apd-constant : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                → {a1 a2 : A}
                → (p : a1 ≡ a2)
                → (f : A → B)
                → ap f p ≡ PathOver-constant-inverse _ (apd f p)
ap-apd-constant refll f = refll
```

(⋆) Define Bowtie-rec and prove the reduction for base:

```agda
Bowtie-rec : {l : Level} {X : Type l}
             (x : X)
             (p : x ≡ x [ X ])
             (q : x ≡ x [ X ])
            → Bowtie → X
Bowtie-rec {_} {X} x p q = Bowtie-elim _ _ (PathOver-constant _ p) (PathOver-constant _ q)

Bowtie-rec-base : {l : Level} {X : Type l}
             (x : X)
             (p : x ≡ x [ X ])
             (q : x ≡ x [ X ])
           → Bowtie-rec x p q baseB ≡ x
Bowtie-rec-base _ p q = Bowtie-elim-base _ _ (PathOver-constant _ p) (PathOver-constant _ q)
```

(⋆⋆) Prove the reductions for loop:

```agda
Bowtie-rec-loop1 : {l : Level} {X : Type l}
               (x : X)
               (p : x ≡ x [ X ])
               (q : x ≡ x [ X ])
             → ap (Bowtie-rec x p q) loop1 ≡ p [ x ≡ x ]
Bowtie-rec-loop1 x p q = ap-apd-constant _ _
  ∙ ap (PathOver-constant-inverse loop1) (Bowtie-elim-loop1 _ _ _ _)
  ∙ PathOver-constant-inverse-cancel1 _ _

Bowtie-rec-loop2 : {l : Level} {X : Type l}
                   (x : X)
                   (p : x ≡ x [ X ])
                   (q : x ≡ x [ X ])
                 → ap (Bowtie-rec x p q) loop2 ≡ q [ x ≡ x ]
Bowtie-rec-loop2 x p q = ap-apd-constant _ _
  ∙ ap (PathOver-constant-inverse _) (Bowtie-elim-loop2 _ _ _ _)
  ∙ PathOver-constant-inverse-cancel1 _ _

```

# Loop space of the bowtie

In this problem, you will show that the loop space of the bowtie is the
"free group on two generators", which we will write in Agda as F2.  The
point of this problem is mainly for you to read and really understand
the proof that the loop space of the circle is ℤ.  All of the code is
essentially a rearrangement of code from that proof.  I'd suggest
trying the proof yourself, and looking at the analogous bits of the
Circle proof if you get stuck.

## Some lemmas (⋆⋆)

In the Circle proof in lecture, I inlined a couple of things that
can be proved more generally.  You might want to prove these general
versions in advance and use them in your proof, or, if that seems
confusing, you might first do the proof without these lemmas
to motivate them.

```agda
concat-equiv : ∀ {A : Type} (a : A) {a' a'' : A}
                     → (p : a' ≡ a'')
                     → (a ≡ a') ≃ (a ≡ a'')
concat-equiv a refll = improve (Isomorphism id (Inverse id refl refl))

concat-equiv-map : ∀ {A : Type} {a a' a'' : A}
                 → (p : a' ≡ a'')
                 → fwd (concat-equiv a p) ≡ λ q → q ∙ p
concat-equiv-map refll = refll
```

(Note: you could also write out all of the components, but this was easier.)

```agda
transport-∙ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
                  {a1 a2 a3 : A} (p : a1 ≡ a2) (q : a2 ≡ a3)
                → transport B (p ∙ q) ∼ transport B q ∘ transport B p
transport-∙ refll refll _ = refll
```
## Calculating the loop space

First, we will assume a type F2 representing the free group on 2
generators.

ℤ is the free group on one generator, with 0 as the neutral element and
succℤ corresponding to "addition" with the one generator.  succℤ is an
equivalence, with the inverse representing "addition" with -1.

For other groups, it is somewhat more common to think of the group
operation as "multiplication" rather than "addition", so we will name
the neutral element as "1" and the action of the elements as
"multiplication".  Thus, we assume a type with an element 1F, and two
equivalences, which we think of as "multiplication with generator 1" and
"multiplication with generator 2".

Unscaffolded hard exercise: You can implement F2 as lists whose
elements are a four-element type g1, g2, g1⁻¹, g2⁻¹ with no adjacent
pairs of inverse elements.  Then the forward directions of mult1/mult2
will be implement by cons'ing g1/g2 on and "reducing" if that creates
two adjacent inverses, the backwards directions by consing g1⁻¹ and g2⁻¹
on and reducing, and the inverse laws will hold because the reduction
cancels the inverses.

For this problem, we will simply assume the nice universal property for
this type: that it maps uniquely into any other type with a point and
two equivalences, and that it is a set.

```agda
module AssumeF2
    (F2 : Type)
    (1F : F2)
    (mult1 : F2 ≃ F2)
    (mult2 : F2 ≃ F2)
    (F2-rec : {X : Type}
              (o : X)
              (m1 : X ≃ X)
              (m2 : X ≃ X)
            → F2 → X)
    (F2-rec-1 : {X : Type}
                (z : X)
                (m1 : X ≃ X)
                (m2 : X ≃ X)
              → F2-rec z m1 m2 1F ≡ z)
    (F2-rec-mult1 : {X : Type}
                    (z : X)
                    (m1 : X ≃ X)
                    (m2 : X ≃ X)
                    (a : F2) → F2-rec z m1 m2 (fwd mult1 a) ≡ fwd m1 (F2-rec z m1 m2 a))
    (F2-rec-mult2 : {X : Type}
                    (z : X)
                    (m1 : X ≃ X)
                    (m2 : X ≃ X)
                    (a : F2) → F2-rec z m1 m2 (fwd mult2 a) ≡ fwd m2 (F2-rec z m1 m2 a))
    (F2-rec-unique : {X : Type}
                    (f : F2 → X)
                    (z : X)
                    (m1 : X ≃ X)
                    (m2 : X ≃ X)
                  → f 1F ≡ z
                  → ((f ∘ fwd mult1) ∼ (fwd m1 ∘ f))
                  → ((f ∘ fwd mult2) ∼ (fwd m2 ∘ f))
                 → (x : F2) → f x ≡ F2-rec z m1 m2 x)
     (hSetF : is-set F2) where
```

(⋆⋆⋆) Prove that the loop space of the Bowtie is F2.  Each bit of the
proof will be analogous to the corresponding part of the Circle proof.

```agda
    Cover : Bowtie → Type
    Cover = Bowtie-rec F2 (ua mult1) (ua mult2)

    encode : (x : Bowtie) → baseB ≡ x → Cover x
    encode _ p = transport Cover p 1F

    loop^ : F2 → baseB ≡ baseB
    loop^ = F2-rec refll
      (improve (Isomorphism (_∙ loop1) (Inverse (λ p → p ∙ ! loop1)
        (λ p → ! (∙assoc _ loop1 (! loop1)) ∙ ap (p ∙_) (!-inv-r loop1))
        (λ p → ! (∙assoc _ (! loop1) loop1) ∙ ap (p ∙_) (!-inv-l loop1)))))
      (improve (Isomorphism (_∙ loop2) (Inverse (λ p → p ∙ ! loop2)
        (λ p → ! (∙assoc _ loop2 (! loop2)) ∙ ap (p ∙_) (!-inv-r loop2))
        (λ p → ! (∙assoc _ (! loop2) loop2) ∙ ap (p ∙_) (!-inv-l loop2)))))

    transport-Cover1 : ∀ x → transport Cover loop1 x ≡ fwd mult1 x
    transport-Cover1 x = transport-ap-assoc Cover loop1 ∙
      ap (λ H → transport id H x) (Bowtie-rec-loop1 _ _ _) ∙
      uaβ mult1

    transport-Cover2 : ∀ x → transport Cover loop2 x ≡ fwd mult2 x
    transport-Cover2 x = transport-ap-assoc Cover loop2 ∙
      ap (λ H → transport id H x) (Bowtie-rec-loop2 _ _ _) ∙
      uaβ mult2

    decode : (x : Bowtie) → Cover x → baseB ≡ x
    decode = Bowtie-elim _ loop^
      (PathOver-→ (λ a → PathOver-path-to
        (! (F2-rec-mult1 _ _ _ a) ∙ ! (ap loop^ (transport-Cover1 _)))))
      (PathOver-→ (λ a → PathOver-path-to
        (! (F2-rec-mult2 _ _ _ a) ∙ ! (ap loop^ (transport-Cover2 _)))))

    encode-decode : (x : Bowtie) (p : baseB ≡ x) → decode x (encode x p) ≡ p
    encode-decode _ refll = F2-rec-1 _ _ _

    endo-F-is-id : (f : F2 → F2)
                 → f 1F ≡ 1F
                 → (f ∘ fwd mult1) ∼ (fwd mult1 ∘ f)
                 → (f ∘ fwd mult2) ∼ (fwd mult2 ∘ f)
                 → f ∼ id
    endo-F-is-id f f0 f1 f2 x =
      F2-rec-unique f 1F mult1 mult2 f0 f1 f2 x ∙
      ! (F2-rec-unique id 1F mult1 mult2 refll (λ _ → refll) (λ _ → refll) x)

    transport-Cover-then-loop1 : {x : Bowtie} (p : x ≡ baseB) (y : Cover x)
                              → transport Cover (p ∙ loop1) y ≡ fwd mult1 (transport Cover p y)
    transport-Cover-then-loop1 (refl _) y = ap (λ Z → transport Cover (Z) y) (∙unit-l loop1) ∙
                                          transport-Cover1 _

    transport-Cover-then-loop2 : {x : Bowtie} (p : x ≡ baseB) (y : Cover x)
                              → transport Cover (p ∙ loop2) y ≡ fwd mult2 (transport Cover p y)
    transport-Cover-then-loop2 (refl _) y = ap (λ Z → transport Cover (Z) y) (∙unit-l loop2) ∙
                                          transport-Cover2 _

    decode-encode-base : encode baseB ∘ decode baseB ∼ id
    decode-encode-base = endo-F-is-id encode-loop^ encode-loop^-1F encode-loop^-multi1 encode-loop^-multi2 where
      encode-loop^ : F2 → F2
      encode-loop^ = encode baseB ∘ loop^

      encode-loop^-1F : encode-loop^ 1F ≡ 1F
      encode-loop^-1F = ap (λ H → transport Cover H 1F) (F2-rec-1 _ _ _)

      encode-loop^-multi1 : (encode-loop^ ∘ fwd mult1) ∼ (fwd mult1 ∘ encode-loop^)
      encode-loop^-multi1 x = ap (λ H → transport Cover H 1F) (F2-rec-mult1 _ _ _ x) ∙
        transport-Cover-then-loop1 (loop^ x) 1F

      encode-loop^-multi2 : (encode-loop^ ∘ fwd mult2) ∼ (fwd mult2 ∘ encode-loop^)
      encode-loop^-multi2 x = ap (λ H → transport Cover H 1F) (F2-rec-mult2 _ _ _ x) ∙
        transport-Cover-then-loop2 (loop^ x) 1F

    decode-encode : (x : Bowtie) (p : Cover x) → encode x (decode x p) ≡ p
    decode-encode = Bowtie-elim _ decode-encode-base
      (PathOver-Π (λ x → fwd (transport-to-pathover _ _ _ _) (hSetF _ _ _ _)))
      (PathOver-Π (λ x → fwd (transport-to-pathover _ _ _ _) (hSetF _ _ _ _)))
```

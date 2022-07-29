```agda
{-# OPTIONS --without-K --rewriting #-}

open import new-prelude
open import Lecture4-notes

module Solutions4 where
```

# Constructing homotopies between paths

Give two "different" path-between-paths/homotopies between (loop ∙ !
loop) ∙ loop and loop.  They should be different in the sense that one
should cancel the !loop with the first loop, and one with the second
loop.  But these aren't really *really* different, in that there will be
a path-between-paths-between-paths between the two!  (Harder exercise
that we haven't really prepared for: prove this!)

```agda
homotopy1 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy1 = (loop ∙ ! loop) ∙ loop ≡⟨ ap ( λ H → H ∙ loop) (!-inv-r loop) ⟩
            refl _ ∙ loop ≡⟨ ∙unit-l loop ⟩
            loop ∎ 

homotopy2 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy2 = (loop ∙ ! loop) ∙ loop ≡⟨ ! (∙assoc loop (! loop) loop) ⟩
            loop ∙ (! loop ∙ loop) ≡⟨ ap (λ H → loop ∙ H) (!-inv-l loop) ⟩
            loop ∎
```

For fun, here's the proof they're the same.  The above proofs work for
any path p, so we can generalize the goal and then do path induction.
in practice, it would be better to define homotopy1 and homotopy2 for
a general p in the first place and then instantiate them to loop so
that you don't need to copy and paste their definitions into the goal
here, but I think it's helpful to be concrete when first practicing
these path algebra steps.


```agda
path-between-paths-between-paths : homotopy1 ≡ homotopy2
path-between-paths-between-paths = gen loop where
  gen : ∀ {A : Type} {x y : A} (p : x ≡ y)
      →  (ap ( λ H → H ∙ p) (!-inv-r p) ∙ ∙unit-l p)
         ≡  
         (! (∙assoc p (! p) p) ∙  ap (λ H → p ∙ H) (!-inv-l p))
         [ ((p ∙ ! p) ∙ p) ≡ p [ x ≡ y [ A ] ] ]
  gen (refl _) = refl _

```

# Functions are group homomorphism

State and prove a general lemma about what ap of a function on the
inverse of a path (! p) does (see ap-∙ for inspiration).  

State and prove a general lemma about what ! (p ∙ q) is.  

Us them to prove that the double function takes loop-inverse to
loop-inverse concatenated with itself.

```agda
!-∙ : {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → ! (p ∙ q) ≡ ! q ∙ ! p
!-∙ (refl _) (refl _) = refl _

ap-! : {A B : Type} {f : A → B} {x y : A} (p : x ≡ y) 
       → ap f (! p) ≡ ! (ap f p)
ap-! (refl _) = refl _

double-!loop : ap double (! loop) ≡ ! loop ∙ ! loop
double-!loop = ap double (! loop) ≡⟨ ap-! loop ⟩
               ! (ap double loop) ≡⟨  ap ! (S1-rec-loop _ _) ⟩
               ! (loop ∙ loop) ≡⟨ !-∙ loop _ ⟩
               ! loop ∙ ! loop ∎ 
```

```agda
invert : S1 → S1
invert = S1-rec base (! loop)
```

# Circles equivalence

See the maps between the 1 point circle and the 2 point circle in the
lecture code.  Check that the composite map S1 → S1 is
homotopic to the identity on base and loop.

```agda
to-from-base : from (to base) ≡ base
to-from-base = refl _

to-from-loop : ap from (ap to loop) ≡ loop
to-from-loop = ap from (ap to loop) ≡⟨ ap (ap from) (S1-rec-loop _ _) ⟩
               ap from (east ∙ ! west) ≡⟨ ap-∙ east (! west) ⟩
               ap from east ∙ ap from (! west) ≡⟨ ap₂ _∙_ (Circle2-rec-east _ _ _ _)
                                                          (ap-! west  ∙ ap ! (Circle2-rec-west _ _ _ _)) ⟩
               loop ∙ ! (refl base) ≡⟨ refl _  ⟩
               loop ∎
```

Note: the problems below here are progressively more optional, so if you
run out of time/energy at some point that is totally fine.  

# Torus to circles

The torus is equivalent to the product of two circles S1 × S1.  The idea
for the map from the torus to S1 × S1 that is part of this equivalence
is that one loop on on the torus is sent to to the circle loop in one
copy of S1, and the other loop on the torus to the loop in the other
copy of the circle.  Define this map.

Hint: for the image of the square, you might want a lemma saying how
paths in product types compose:

```agda
compose-pair≡ : {A B : Type} {x1 x2 x3 : A} {y1 y2 y3 : B}
                (p12 : x1 ≡ x2) (p23 : x2 ≡ x3)
                (q12 : y1 ≡ y2) (q23 : y2 ≡ y3)
              → (pair≡ p12 q12) ∙ (pair≡ p23 q23) ≡ pair≡ (p12 ∙ p23) (q12 ∙ q23)
compose-pair≡ (refl _) (refl _) (refl _) (refl _) = refl _

torus-to-circles : Torus → S1 × S1
torus-to-circles = T-rec (base , base)
                         (pair≡ (refl base) loop )
                         (pair≡ loop (refl base ))
                         (compose-pair≡ (refl _) loop loop (refl _) ∙
                          ap₂ pair≡ (∙unit-l loop) (! (∙unit-l loop)) ∙ 
                          ! (compose-pair≡ loop (refl _) (refl _) loop))
```

# Suspensions

Find a type X such that the two-point circle Circle2 is equivalent to
the suspension Susp X.  Check your answer by defining a logical
equivalence (functions back and forth), since we haven't seen how to
prove that such functions are inverse yet.

```agda
c2s : Circle2 → Susp Bool
c2s = Circle2-rec northS southS (merid true) (merid false)

s2c-f : Bool → north ≡ south
s2c-f true = west
s2c-f false = east

s2c : Susp Bool → Circle2
s2c = Susp-rec north south s2c-f
```

Suspension is a functor from types, which means that it acts on
functions as well as types.  Define the action of Susp on functions:

```agda
susp-func : {X Y : Type} → (f : X → Y) → Susp X → Susp Y
susp-func f = Susp-rec northS southS (λ x → merid (f x) )
```

To really prove that Susp is a functor, we should check that this action
on functions preserves the identity function and composition of
functions. But to do that we would need the dependent elimination rule
for suspensions, which we haven't talked about yet.


# Pushouts

Fix a type X.  Find types A,B,C with functions f : C → A and g : C → B
such that the suspension Susp X is equivalent to the Pushout C A B f g.
Check your answer by defining a logical equivalence (functions back and
forth), since we haven't seen how to prove that such functions are
inverse yet.

```agda
SuspFromPush : Type → Type
SuspFromPush A = Pushout A 𝟙 𝟙  (λ _ → ⋆) (λ _ → ⋆)

s2p : (A : Type) → Susp A → SuspFromPush A
s2p A = Susp-rec (inl ⋆) (inr ⋆) glue

p2s : (A : Type) → SuspFromPush A → Susp A
p2s A = Push-rec (λ _ → northS) (λ _ → southS) merid
```


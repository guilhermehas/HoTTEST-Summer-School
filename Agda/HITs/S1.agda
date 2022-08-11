{-# OPTIONS  --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Prelude
  renaming (ℓ-max to infixl 6 _⊔_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.S1 hiding (encode; decode)

open Iso

private variable
  ℓ l1 l2 : Level
  A B X : Type ℓ
  x y : X

fwd = fst

_∼_ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} → ((x : A) → B x) → ((x : A) → B x) → Type (l1 ⊔ l2)
f ∼ g = ∀ x → f x ≡ g x

ap : (f : X → B) (p : x ≡ y) → f x ≡ f y
ap f p i = f (p i)

PathOver : {A : Type l1} (B : A → Type l1) {a1 a2 : A} (p : a1 ≡ a2) (b1 : B a1) (b2 : B a2) → Type l1
PathOver B p b1 b2 = PathP (λ i → B (p i)) b1 b2

syntax PathOver B p b1 b2 = b1 ≡ b2 [ B ↓ p ]

S1-rec : (x : X) (p : x ≡ x) → S¹ → X
S1-rec x p base = x
S1-rec x p (loop i) = p i

S1-rec-base : (x : X) (p : x ≡ x) → S1-rec x p base ≡ x
S1-rec-base x p = refl

S1-rec-loop : (x : X) (p : x ≡ x) → cong (S1-rec x p) loop ≡ p
S1-rec-loop x p = refl

S1-elim : (X : S¹ → Type)
          (x : X base)
          (p : x ≡ x [ X ↓ loop ])
        → (x : S¹) → X x
S1-elim X x p base = x
S1-elim X x p (loop i) = p i

S1-elim-base : (X : S¹ → Type)
               (x : X base)
               (p : x ≡ x [ X ↓ loop ])
             → S1-elim X x p base ≡ x
S1-elim-base X x p = refl

S1-elim-loop : (X : S¹ → Type)
               (x : X base)
               (p : x ≡ x [ X ↓ loop ])
             → cong (S1-elim X x p) loop ≡ p
S1-elim-loop X x p = refl

record IntAxioms : Type₁ where
  field
    ℤ : Type
    0ℤ : ℤ
    succℤ : ℤ ≃ ℤ
    ℤ-rec : {X : Type}
            (b : X)
            (s : X ≃ X)
          → ℤ → X
    ℤ-rec-0ℤ : {X : Type}
               (b : X)
               (s : X ≃ X)
             → ℤ-rec b s 0ℤ ≡ b
    ℤ-rec-succℤ : {X : Type}
                  (b : X)
                  (s : X ≃ X)
                  (a : ℤ) → ℤ-rec b s (fwd succℤ a) ≡ fwd s (ℤ-rec b s a)
    ℤ-rec-unique : {X : Type}
                   (f : ℤ → X)
                   (z : X)
                   (s : X ≃ X)
                 → f 0ℤ ≡ z
                 → ((f ∘ fwd succℤ) ∼ (fwd s ∘ f))
                 → (x : ℤ) → f x ≡ ℤ-rec z s x
    hSetℤ : isSet ℤ

transport-ap-assoc : {A : Type} (C : A → Type) {a a' : A} (p : a ≡ a') {x : C a}
                       → subst C p x ≡ subst (idfun _) (cong C p) x
transport-ap-assoc C p = refl

PathOver-path-to' : ∀ {A : Type}
                      {a0 a a' : A} (p : a ≡ a')
                      (q : a0 ≡ a)
                      (r : a0 ≡ a')
                      → q ∙ p ≡ r
                      → q ≡ r [ a0 ≡_ ↓ p ]
PathOver-path-to' {A} {a0} {a} {a'} = J
  (λ a' p →  (q : a0 ≡ a) (r : a0 ≡ a') → q ∙ p ≡ r → q ≡ r [ a0 ≡_ ↓ p ] )
  (J (λ a q →  (r : a0 ≡ a) → q ∙ refl ≡ r → q ≡ r [ a0 ≡_ ↓ refl ])
  λ _ p → subst (PathOver (_≡_ a0) refl refl) p (lUnit _))


PathOver-path-to : ∀ {A : Type}
                     {a0 a a' : A} {p : a ≡ a'}
                     {q : a0 ≡ a}
                     {r : a0 ≡ a'}
                     → q ∙ p ≡ r
                     → q ≡ r [ a0 ≡_ ↓ p ]
PathOver-path-to = PathOver-path-to' _ _ _

transport-to-pathover : {A : Type l1} (B : A → Type l1)
                        {a1 a2 : A} (p : a1 ≡ a2)
                        (b1 : B a1) (b2 : B a2)
                        → subst B p b1 ≡ b2 → b1 ≡ b2 [ B ↓ p ]
transport-to-pathover B {a1} = J (λ a2 p → (b1 : B a1)
  (b2 : B a2) → subst B p b1 ≡ b2 → b1 ≡ b2 [ B ↓ p ] )
  λ b1 b2 p → subst (PathOver B refl b1) p (sym (substRefl {B = B} _))

transport-→ : {X : Type}
              {A : X → Type}
              {B : X → Type}
              {x x' : X} (p : x ≡ x')
              {f : A x → B x}
            → subst (λ z → (y : A z) → B (z)) p f ≡ λ a → subst B p (f (subst A (sym p) a))
transport-→ {_} {A} {B} {x} = J (λ x' p → 
  {f : A x → B x} → subst (λ z → (y : A z) → B (z)) p f ≡ λ a → subst B p (f (subst A (sym p) a)))
  λ {f} → funExt λ x' → refl

transport-to-pathover' : {A : Type l1} (B : A → Type l1)
                        {a1 a2 : A} (p : a1 ≡ a2)
                        (b1 : B a1) (b2 : B a2)
                        → b1 ≡ b2 [ B ↓ p ] → subst B p b1 ≡ b2
transport-to-pathover' B {a1} = J (λ a2 p →
  (b1 : B a1) (b2 : B a2) → b1 ≡ b2 [ B ↓ p ] → (subst B p b1 ≡ b2))
  λ b1 b2 p → subst (subst B refl b1 ≡_) p (substRefl {B = B} _)

PathOver-→' : {A : X → Type}
             {B : X → Type}
             {x x' : X} (p : x ≡ x')
             (f1 : A x → B x)
             (f2 : A x' → B x')
           → ((a : A x) → f1 a ≡ f2 (subst A p a) [ B ↓ p ])
           → f1 ≡ f2 [ (λ z → A z → B z) ↓ p ]
PathOver-→' {A = A} {B} {x} {x'} = J (λ x' p →
   (f1 : A x → B x) (f2 : A x' → B x') → ((a : A x) → f1 a ≡ f2 (subst A p a) [ B ↓ p ])
     → f1 ≡ f2 [ (λ z → A z → B z) ↓ p ])
  λ f1 f2 p → funExt λ a → p a ∙ cong f2 (substRefl {B = A} _)

PathOver-→ : {A : X → Type}
             {B : X → Type}
             {x x' : X} {p : x ≡ x'}
             {f1 : A x → B x}
             {f2 : A x' → B x'}
           → ((a : A x) → f1 a ≡ f2 (subst A p a) [ B ↓ p ])
           → f1 ≡ f2 [ (λ z → A z → B z) ↓ p ]
PathOver-→ {A = A} {B} {p = p} {f1 = f1} {f2 = f2} = PathOver-→' p f1 f2

PathOver-Π' : {A : X → Type}
              {B : Σ _ A → Type}
              {x x' : X} (p : x ≡ x')
              (f1 : (y : A x) → B (x , y))
              (f2 : (y' : A x') → B (x' , y'))
            → ({a : A x} {a' : A x'} (q : a ≡ a' [ A ↓ p ]) → f1 a ≡ f2 a' [ B ↓ (λ i → _ , q i) ])
            → f1 ≡ f2 [ (λ z → (y : A z) → B (z , y)) ↓ p ]
PathOver-Π' {A = A} {B} {x} {x'} = J (λ x' p →
    (f1 : (y : A x) → B (x , y))
    (f2 : (y' : A x') → B (x' , y'))
  → ({a : A x} {a' : A x'} (q : a ≡ a' [ A ↓ p ]) → f1 a ≡ f2 a' [ B ↓ (λ i → _ , q i) ])
  → f1 ≡ f2 [ (λ z → (y : A z) → B (z , y)) ↓ p ])
  λ f1 f2 eqn → funExt λ a → eqn refl

PathOver-Π : {X : Type}
             {A : X → Type}
             {B : Σ _ A → Type}
             {x x' : X} {p : x ≡ x'}
             {f1 : (y : A x) → B (x , y)}
             {f2 : (y' : A x') → B (x' , y')}
           → ({a : A x} {a' : A x'} (q : a ≡ a' [ A ↓ p ]) → f1 a ≡ f2 a' [ B ↓ (λ i → _ , q i) ])
           → f1 ≡ f2 [ (λ z → (y : A z) → B (z , y)) ↓ p ]
PathOver-Π {A = A} {B} {p = p} {f1 = f1} {f2} eqn = PathOver-Π' p f1 f2 eqn


module AssumeInts (intAxioms : IntAxioms) where

  open IntAxioms intAxioms

  loop^ : ℤ → ΩS¹
  loop^ = ℤ-rec refl (isoToEquiv isoBase) where
    isoBase : Iso ΩS¹ ΩS¹
    fun isoBase p = p ∙ loop
    inv isoBase p = p ∙ (sym loop)
    rightInv isoBase p = sym (assoc _ (sym loop) loop) ∙
      cong (p ∙_) (rCancel (sym loop)) ∙ sym (rUnit p)
    leftInv isoBase p =  sym (assoc _ loop (sym loop)) ∙
      cong (p ∙_) (lCancel (sym loop)) ∙ sym (rUnit p)

  Cover : S¹ → Type
  Cover = S1-rec ℤ (ua succℤ)

  encode : (x : S¹) → base ≡ x → Cover x
  encode x p = subst Cover p 0ℤ

  transport-Cover-loop : (x : ℤ) → subst Cover loop x ≡ fwd succℤ x
  transport-Cover-loop x = ap {y = ua succℤ} (λ H → transport H x) (S1-rec-loop _ _) ∙ uaβ succℤ x

  decode : (x : S¹) → Cover x → base ≡ x
  decode = S1-elim _ loop^ (PathOver-→ {A = Cover} {B = base ≡_} λ a →
    PathOver-path-to (sym (ℤ-rec-succℤ _ _ a) ∙ sym (cong loop^ (transport-Cover-loop _))))

  endo-ℤ-is-id : (f : ℤ → ℤ)
               → f 0ℤ ≡ 0ℤ
               → (f ∘ fwd succℤ) ∼ (fwd succℤ ∘ f)
               → f ∼ idfun _
  endo-ℤ-is-id f f0 fsucc x = ℤ-rec-unique f 0ℤ succℤ f0 fsucc x ∙
                           sym (ℤ-rec-unique (λ x → x) 0ℤ succℤ refl (λ _ → refl) x)

  transport-Cover-then-loop : {x : S¹} (p : x ≡ base) (y : Cover x)
                            → subst Cover (p ∙ loop) y ≡ fwd succℤ (subst Cover p y)
  transport-Cover-then-loop {x} p = J (λ x sp → let p = sym sp in
    (y : Cover x) → subst Cover (p ∙ loop) y ≡ fwd succℤ (subst Cover p y))
    (λ y → ap {B = ℤ} {refl ∙ loop} {loop} (λ Z → subst Cover Z y) (sym (lUnit loop))
      ∙ cong (subst Cover loop) (sym (substRefl {B = Cover} {base} y))
      ∙ transport-Cover-loop _)
    (sym p)



  decode-encode-base : (x : ℤ) → encode base (loop^ x) ≡ x
  decode-encode-base = endo-ℤ-is-id encode-loop^ encode-loop^-zero encode-loop^-succ where
    encode-loop^ : ℤ → ℤ
    encode-loop^ = encode base ∘ loop^

    encode-loop^-zero : encode-loop^ 0ℤ ≡ 0ℤ
    encode-loop^-zero = cong (λ H → subst Cover H 0ℤ) (ℤ-rec-0ℤ _ _) ∙ α where
      α : subst {_} {S¹} {_} {base} {base} Cover refl 0ℤ ≡ 0ℤ
      α = substRefl {B = Cover} {base} 0ℤ

    encode-loop^-succ : (encode-loop^ ∘ fwd succℤ) ∼ (fwd succℤ ∘ encode-loop^)
    encode-loop^-succ x = ap (λ H → encode base H) (ℤ-rec-succℤ _ _ x) ∙
                          transport-Cover-then-loop (loop^ x) 0ℤ

  decode-encode : (x : S¹) (p : Cover x) → encode x (decode x p) ≡ p
  decode-encode = S1-elim _
    decode-encode-base
    (PathOver-Π {S¹} {S1-rec ℤ (ua succℤ)}
    {λ (x , y) → encode x (decode x y) ≡ y}
    {base} {base} {loop}
    λ aa' → transport-to-pathover (λ (x , y) → encode x (decode x y) ≡ y)
    (λ i → loop i , aa' i) _ _ (hSetℤ _ _ _ _))

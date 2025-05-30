{-# OPTIONS --cubical #-}

{-

  A small library of helper functions and definitions used throughout the
  formalisation.
  
  We redefine some constructions already included in the Cubical library 
  for simplicity of presentation and proof development.

-}

module ContainersPlus where

open import CategoryTheory

open import Level renaming (suc to lsuc ; zero to lzero)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary
open Functor
open _≅ᶠ_

data ⊤ {l : Level} : Set l where
  tt : ⊤

⊤-singleton : ∀ {ℓ} → (x : ⊤ {ℓ}) → x ≡ tt
⊤-singleton tt = refl

⊤-ind : ∀ {ℓ ℓ'} (P : (s : ⊤ {ℓ}) → Set ℓ') → P tt → (s : ⊤ {ℓ}) → P s
⊤-ind P p tt = p

infix 5 _◁_
record Container (s p : Level) : Set (lsuc (s ⊔ p)) where
  constructor _◁_
  field
    Shape    : Set s
    Position : Shape → Set p
open Container public

⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ⊔ p ⊔ ℓ)
⟦ S ◁ P ⟧ X = Σ S (λ s → P s → X)

infixr 8 _⇒ᶜ_

record _⇒ᶜ_ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂)
           : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  constructor _◁_
  field
    shape    : Shape C₁ → Shape C₂
    position : ∀ {s} → Position C₂ (shape s) → Position C₁ s

◇ : {s s' p p' : Level} {S : Set s} {T : Set s'} → (P : S → Set p) → (Q : T → Set p') 
    → ⟦ S ◁ P ⟧ T → Set (p ⊔ p')
◇ P Q (s , f) = Σ (P s) (Q ∘ f)

⟦_⟧f : ∀ {s p} → Container s p → Functor (s ⊔ p) (s ⊔ p)
F-obj ⟦ S ◁ P ⟧f X = Σ S (λ s → P s → X)
F-mor ⟦ S ◁ P ⟧f g (s , f) = (s , g ∘ f)
F-id ⟦ S ◁ P ⟧f X = refl
F-comp ⟦ S ◁ P ⟧f g f = refl

⟦_⟧m : ∀ {s p} {C : Container s p} {C' : Container s p} →
         (C ⇒ᶜ C') → (⟦ C ⟧f ⇒ ⟦ C' ⟧f)
_⇒_.α ⟦ u ◁ v ⟧m X (s , f) = (u s , f ∘ v)
_⇒_.nat ⟦ u ◁ v ⟧m X Y f = ∣ refl ∣₁

contCompNatural : ∀ {s p} → (S : Set s) (P : S → Set p) → (⟦ S ◁ P ⟧f ∘ᶠ ⟦ S ◁ P ⟧f) ≅ᶠ ⟦ ⟦ S ◁ P ⟧ S ◁ ◇ P P ⟧f
_⇒_.α (to≅ (contCompNatural S P)) X (s , f) = ((s , fst ∘ f) , λ p → snd (f (fst p)) (snd p))
_⇒_.nat (to≅ (contCompNatural S P)) X Y f = ∣ refl ∣₁
_⇒_.α (from≅ (contCompNatural S P)) X ((s , f) , g) = (s , λ p → (f p , λ p' → g (p , p')))
_⇒_.nat (from≅ (contCompNatural S P)) X Y f = ∣ refl ∣₁
inv≅-1 (contCompNatural S P) i X x = x
inv≅-2 (contCompNatural S P) i X x = x

-- ⟨_,_⟩ notation - extremely dependant function pairing
[_,_,_]⟨_,_⟩ : ∀ {ℓs ℓt ℓr ℓp ℓq} {S : Set ℓs} {T : Set ℓt} {R : Set ℓr} (P : S → Set ℓp) (Q : T → Set ℓq) (s : S) 
        (f : P s → T) (g : (Σ[ p ∈ P s ] Q (f p)) → R)
        (x : P s) → Σ[ t ∈ T ] (Q t → R)
[ P , Q , s ]⟨ f , g ⟩ x = (f x , λ y → g (x , y))

-- A curried version of the above (i.e. where the second function can be curried)
[_,_,_]⟨_,_⟩' : ∀ {ℓs ℓt ℓr ℓp ℓq} {S : Set ℓs} {T : Set ℓt} {R : Set ℓr} (P : S → Set ℓp) (Q : T → Set ℓq) (s : S) 
        (f : P s → T) (g : (p : P s) → Q (f p) → R)
        (x : P s) → Σ[ t ∈ T ] (Q t → R)
[ P , Q , s ]⟨ f , g ⟩' x = (f x , g x)

_∘ᶜ_ : {s s' p p' : Level} → Container s p → Container s' p' → Container (s ⊔ s' ⊔ p) (p ⊔ p')
(S ◁ P) ∘ᶜ (T ◁ Q) = (⟦ S ◁ P ⟧ T) ◁ (◇ P Q)

-- Helper functions for proofs
contP-shape : ∀ {ℓs ℓp ℓa} {S : Set ℓs} {P : S → Set ℓp} {A : Set ℓa} → 
                {s s' : S} {f : P s → A} {f' : P s' → A} →
                (p : s ≡ s') (p' : PathP (λ i → P (p i) → A) f f') →
                PathP (λ i → Σ S (λ s → P s → A)) (s , f) (s' , f')
contP-shape p p' i = (p i , p' i)

contP-position : ∀ {ℓs ℓp ℓs' ℓp'} {S : Set ℓs} {P : S → Set ℓp} 
                   {T : Set ℓs'} {Q : T → Set ℓp'} → 
                   {s₀ s s' : S} {f₀ : P s₀ → T} {f : P s → T} {f' : P s' → T} →
                   (p : s ≡ s') (p' : PathP (λ i → P (p i) → T) f f') →
                   {g : ◇ P Q (s , f) → ◇ P Q (s₀ , f₀)} → 
                   {g' : ◇ P Q (s' , f') → ◇ P Q (s₀ , f₀)} →
                  (q : PathP (λ i → ◇ P Q (contP-shape p p' i) → P s₀) (fst ∘ g) (fst ∘ g')) →
                  (q' : PathP (λ i → (a : ◇ P Q (contP-shape p p' i)) → Q (f₀ (q i a))) (snd ∘ g) (snd ∘ g')) → 
                  PathP (λ i → ◇ P Q (contP-shape p p' i) → ◇ P Q (s₀ , f₀)) g g'
contP-position p p' q q' i z = ( q i z , q' i z )

Idᶜ : {s p : Level} → Container s p
Idᶜ = ⊤ ◁ λ _ → ⊤

-- Helper functions for the no-go theorem

case : ∀ {ℓ ℓ'} {P : Type ℓ} {A : Type ℓ'} → A → A → (Dec P) → A
case ifyes ifno (yes _) = ifyes
case ifyes ifno (no _) = ifno

cased : ∀ {ℓ ℓ' ℓ''} {P : Type ℓ} {A : Type ℓ'} {B : A → Type ℓ''} 
        → (a a' : A) (b : B a) (b' : B a')
        → (p : Dec P) → B (case a a' p)
cased _ _ ifyes ifno (yes _) = ifyes
cased _ _ ifyes ifno (no _) = ifno

decLem₁ : {ℓa ℓb ℓc ℓp : Level} {A : Set ℓa} {B : A → Set ℓb} {C : Set ℓc}
        {P : Set ℓp} (dec : Discrete P)
        (a₁ a₂ : A) (b₁ : B a₁) (b₂ : B a₂) (g : (a : A) → B a → C)
        (p p' : P)
        → case (g a₁ b₁) (g a₂ b₂) (dec p p')
        ≡ g (case a₁ a₂ (dec p p')) (cased a₁ a₂ b₁ b₂ (dec p p'))
decLem₁ dec a₁ a₂ b₁ b₂ g p p' i with dec p p' 
... | (yes _) = g a₁ b₁
... | (no _)  = g a₂ b₂

decLem₂ : {ℓa ℓb ℓc ℓp : Level} {A : Set ℓa} {B : A → Set ℓb} {C : Set ℓc}
        {P : Set ℓp} (dec : Discrete P)
        (a₁ a₂ : A) (c₁ c₂ : C)
        (p p' : P)
        → cased {B = λ a → B a → C} a₁ a₂ (const c₁) (const c₂) (dec p p')
        ≡ const (case c₁ c₂ (dec p p'))
decLem₂ dec a₁ a₂ c₁ c₂ p p' i with dec p p' 
... | (yes _) = const c₁
... | (no _)  = const c₂

decLem₃ : {ℓa ℓp : Level} {A : Set ℓa} 
        {P : Set ℓp} (dec : Discrete P)
        (a₁ a₂ a₃ : A) (p₁ p₂ p₃ : P)
        (pdist : ¬ (p₁ ≡ p₂))
        → case a₁ (case a₂ a₃ (dec p₃ p₂)) (dec p₃ p₁)
        ≡ case a₂ (case a₁ a₃ (dec p₃ p₁)) (dec p₃ p₂)
decLem₃ dec a₁ a₂ a₃ p₁ p₂ p₃ pdist with dec p₃ p₁ | dec p₃ p₂
... | (yes e) | (yes e') = rec⊥ (pdist (sym e ∙ e')) 
... | (yes e) | (no e')  = refl
... | (no e)  | (yes e') = refl
... | (no e)  | (no e')  = refl

dec⊤ : {ℓ : Level} → Discrete (⊤ {ℓ})
dec⊤ tt tt = yes refl

decRefl : {ℓ : Level} {A : Set ℓ}
        (dec : Discrete A) (a : A)
        → Σ[ e ∈ a ≡ a ] dec a a ≡ yes e
decRefl dec a with dec a a
... | (yes e) = (e , refl)
... | (no e)  = rec⊥ (e refl)

transpFun : {ℓa ℓb ℓc : Level} {A : Set ℓa} {B : A → Set ℓb} {C : Set ℓc}
            (a a' : A) (e : a ≡ a')
            (f : B a → C)
          → transport (λ i → B (e i) → C) f ≡ f ∘ transport (λ i → B (e (~ i)))
transpFun {B = B} a a' e f i b = transportRefl (f (transp (λ j → B (e (~ j))) i0 b)) i

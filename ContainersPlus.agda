{-# OPTIONS --cubical #-}

{-

  A small library of helper functions and definitions used throughout the
  formalisation.
  
  We redefine some constructions already included in the Cubical library 
  for simplicity of presentation and proof development.

-}

module ContainersPlus where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude hiding (_▷_)
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import CategoryTheory
open import Cubical.HITs.PropositionalTruncation
open Functor
open _≅ᶠ_

data ⊤ {l : Level} : Set l where
  tt : ⊤

⊤-singleton : ∀ {ℓ} → (x : ⊤ {ℓ}) → x ≡ tt
⊤-singleton tt = refl

⊤-ind : ∀ {ℓ ℓ'} (P : (s : ⊤ {ℓ}) → Set ℓ') → P tt → (s : ⊤ {ℓ}) → P s
⊤-ind P p tt = p

infix 5 _▷_
record Container (s p : Level) : Set (lsuc (s ⊔ p)) where
  constructor _▷_
  field
    Shape    : Set s
    Position : Shape → Set p
open Container public

⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ⊔ p ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ S (λ s → P s → X)

infixr 8 _⇒ᶜ_

record _⇒ᶜ_ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂)
           : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  constructor _▷_
  field
    shape    : Shape C₁ → Shape C₂
    position : ∀ {s} → Position C₂ (shape s) → Position C₁ s

◇ : {s s' p p' : Level} {S : Set s} {T : Set s'} → (P : S → Set p) → (Q : T → Set p') 
    → ⟦ S ▷ P ⟧ T → Set (p ⊔ p')
◇ P Q (s , f) = Σ (P s) (Q ∘ f)

⟦_⟧f : ∀ {s p} → Container s p → Functor (s ⊔ p) (s ⊔ p)
F-obj ⟦ S ▷ P ⟧f X = Σ S (λ s → P s → X)
F-mor ⟦ S ▷ P ⟧f g (s , f) = (s , g ∘ f)
F-id ⟦ S ▷ P ⟧f X = refl
F-comp ⟦ S ▷ P ⟧f g f = refl

⟦_⟧m : ∀ {s p} {C : Container s p} {C' : Container s p} →
         (C ⇒ᶜ C') → (⟦ C ⟧f ⇒ ⟦ C' ⟧f)
_⇒_.α ⟦ u ▷ v ⟧m X (s , f) = (u s , f ∘ v)
_⇒_.nat ⟦ u ▷ v ⟧m X Y f = ∣ refl ∣₁

contCompNatural : ∀ {s p} → (S : Set s) (P : S → Set p) → (⟦ S ▷ P ⟧f ∘ᶠ ⟦ S ▷ P ⟧f) ≅ᶠ ⟦ ⟦ S ▷ P ⟧ S ▷ ◇ P P ⟧f
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
(S ▷ P) ∘ᶜ (T ▷ Q) = (⟦ S ▷ P ⟧ T) ▷ (◇ P Q)

from-∘ᶜ : {ℓ s s' p p' : Level} (X : Set ℓ) (C : Container s p) (C' : Container s' p') 
        → ⟦ C ∘ᶜ C' ⟧ X → ⟦ C ⟧ (⟦ C' ⟧ X)
from-∘ᶜ X C C' ((s , f) , g) = (s , λ p → (f p , λ q → g (p , q)))

to-∘ᶜ : {ℓ s s' p p' : Level} (X : Set ℓ) (C : Container s p) (C' : Container s' p') 
        → ⟦ C ⟧ (⟦ C' ⟧ X) → ⟦ C ∘ᶜ C' ⟧ X
to-∘ᶜ X C C' (s , f) = ((s , fst ∘ f) , λ q → snd (f (fst q)) (snd q))

inv-∘ᶜ₁ : {ℓ s s' p p' : Level} (X : Set ℓ) (C : Container s p) (C' : Container s' p') 
        → (c : ⟦ C ⟧ (⟦ C' ⟧ X)) → from-∘ᶜ X C C' (to-∘ᶜ X C C' c) ≡ c
inv-∘ᶜ₁ X C C' (s , f) = refl

inv-∘ᶜ₂ : {ℓ s s' p p' : Level} (X : Set ℓ) (C : Container s p) (C' : Container s' p') 
        → (c : ⟦ C ∘ᶜ C' ⟧ X) → to-∘ᶜ X C C' (from-∘ᶜ X C C' c) ≡ c
inv-∘ᶜ₂ X C C' ((s , f) , g) = refl

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
Idᶜ = ⊤ ▷ λ _ → ⊤

α⁻¹ : {ℓ s p s' p' s'' p'' : Level} (X : Set ℓ) (A : Container s p) (B : Container s' p') (C : Container s'' p'')
  → ⟦ (A ∘ᶜ B) ∘ᶜ C ⟧ X → ⟦ A ∘ᶜ (B ∘ᶜ C) ⟧ X
-- ((s , f) , g) ↦ (s , ⟨ f , g ⟩)
(α⁻¹ X A B C) (((s , f) , g) , h) = ((s , λ p → (f p , λ q → g (p , q))) , λ r → h ((fst r , fst (snd r)) , snd (snd r)))

α : {ℓ s p s' p' s'' p'' : Level} (X : Set ℓ) (A : Container s p) (B : Container s' p') (C : Container s'' p'')
  → ⟦ A ∘ᶜ (B ∘ᶜ C) ⟧ X → ⟦ (A ∘ᶜ B) ∘ᶜ C ⟧ X
-- (s , ⟨ f , g ⟩) ↦ ((s , f) , g)
(α X A B C) ((s , f) , g) = (((s , λ p → fst (f p)) , λ q → snd (f (fst q)) (snd q)) , λ r → g (fst (fst r) , (snd (fst r) , snd r)))

inv-α₁ : {ℓ s p s' p' s'' p'' : Level} (X : Set ℓ) (A : Container s p) (B : Container s' p') (C : Container s'' p'')
       → (a : ⟦ A ∘ᶜ (B ∘ᶜ C) ⟧ X) → α⁻¹ X A B C (α X A B C a) ≡ a
inv-α₁ X A B C ((s , f) , g) = refl

inv-α₂ : {ℓ s p s' p' s'' p'' : Level} (X : Set ℓ) (A : Container s p) (B : Container s' p') (C : Container s'' p'')
       → (a : ⟦ (A ∘ᶜ B) ∘ᶜ C ⟧ X) → α X A B C (α⁻¹ X A B C a) ≡ a
inv-α₂ X A B C (((s , f) , g) , h) = refl

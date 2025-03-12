{-# OPTIONS --cubical #-}

open import ContainersPlus
open import MndContainer as MC
open MC.MndContainer
open import MndContainerMorphism

open import Level renaming (suc to lsuc ; zero to lzero)
open import Function
open import Cubical.Foundations.Prelude hiding (_▷_)
open import Cubical.Data.Sigma renaming (fst to π₁ ; snd to π₂)

record MndCompatibleComposite (ℓs ℓp : Level)
                              (S : Set ℓs) (P : S → Set ℓp) (T : Set ℓs) (Q : T → Set ℓp)
                              (Aₘ : MndContainer _ _ (S ▷ P)) (Bₘ : MndContainer _ _ (T ▷ Q)) :
                              Set (lsuc (ℓs ⊔ ℓp)) where

  ιᶜ : ⟦ S ▷ P ⟧ T
  ιᶜ = (ι Aₘ , const (ι Bₘ))
  
  field
    σᶜ : (s : ⟦ S ▷ P ⟧ T) → (◇ P Q s → ⟦ S ▷ P ⟧ T) → ⟦ S ▷ P ⟧ T
    prᶜ₁ : (s : ⟦ S ▷ P ⟧ T) → (f : ◇ P Q s → ⟦ S ▷ P ⟧ T) → 
           (p : ◇ P Q (σᶜ s f)) → ◇ P Q s 
    prᶜ₂ : (s : ⟦ S ▷ P ⟧ T) → (f : ◇ P Q s → ⟦ S ▷ P ⟧ T) → 
           (p : ◇ P Q (σᶜ s f)) → ◇ P Q (f (prᶜ₁ s f p))
    isMCont : IsMndContainer _ _ (⟦ S ▷ P ⟧ T) (◇ P Q) ιᶜ σᶜ prᶜ₁ prᶜ₂

  MCont : MndContainer _ _ ((⟦ S ▷ P ⟧ T) ▷ (◇ P Q))
  MCont = mContBuilder _ _ _ _ ιᶜ σᶜ prᶜ₁ prᶜ₂ isMCont

  field
    s-inj : IsMndContainerMorphism _ _ _ _ S P (⟦ S ▷ P ⟧ T) (◇ P Q) Aₘ MCont (λ s → (s , const (ι Bₘ))) π₁
    t-inj : IsMndContainerMorphism _ _ _ _ T Q (⟦ S ▷ P ⟧ T) (◇ P Q) Bₘ MCont (λ t → (ι Aₘ , const t)) π₂
    middle-unit-shape : (s : S) (f : P s → T) → (s , f) ≡ σᶜ (s , const (ι Bₘ)) (λ p → (ι Aₘ , const (f (π₁ p))))
    middle-unit-pos : (s : S) (f : P s → T) →
                      PathP (λ i → ◇ P Q (middle-unit-shape s f i) → ◇ P Q (s , f))
                            (λ x → x)
                            (λ x → (π₁ (prᶜ₁ _ _ x) , π₂ (prᶜ₂ _ _ x)))

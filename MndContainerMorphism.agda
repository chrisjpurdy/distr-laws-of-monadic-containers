{-# OPTIONS --cubical #-}

open import ContainersPlus
open import MndContainer as MC
open MC.MndContainer

open import Level renaming (suc to lsuc ; zero to lzero)
open import Cubical.Foundations.Prelude hiding (_▷_) renaming (fst to π₁ ; snd to π₂)
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

record IsMndContainerMorphism (ℓs ℓp ℓs' ℓp' : Level) (S : Set ℓs) (P : S → Set ℓp) (T : Set ℓs') (Q : T → Set ℓp')
                              (Aₘ : MndContainer _ _ (S ▷ P)) 
                              (Bₘ : MndContainer _ _ (T ▷ Q))
                              (shapeₘ : S → T) (positionₘ : {s : S} → Q (shapeₘ s) → P s) : 
                              Set (lsuc (ℓs ⊔ ℓp ⊔ ℓs' ⊔ ℓp')) where
  field
    ι-pres : shapeₘ (ι Aₘ) ≡ ι Bₘ
    σ-pres : (s : S) (f : P s → S) → shapeₘ (σ Aₘ s f) ≡ σ Bₘ (shapeₘ s) (shapeₘ ∘ f ∘ positionₘ)
    pr₁-pres : (s : S) (f : P s → S) →
               PathP (λ i → Q (σ-pres s f i) → P s)
                     (λ q → pr₁ Aₘ s f (positionₘ q))
                     (λ q → positionₘ (pr₁ Bₘ (shapeₘ s) (shapeₘ ∘ f ∘ positionₘ) q))
    pr₂-pres : (s : S) (f : P s → S) →
               PathP (λ i → (q : Q (σ-pres s f i)) → P (f (pr₁-pres s f i q)))
                     (λ q → pr₂ Aₘ s f (positionₘ q))
                     (λ q → positionₘ (pr₂ Bₘ (shapeₘ s) (shapeₘ ∘ f ∘ positionₘ) q))


record MndContainerMorphism (ℓs ℓp : Level) (S : Set ℓs) (P : S → Set ℓp) (T : Set ℓs) (Q : T → Set ℓp)
                            (Aₘ : MndContainer _ _ (S ▷ P)) 
                            (Bₘ : MndContainer _ _ (T ▷ Q)) : Set (lsuc (ℓs ⊔ ℓp)) where
  field
    shapeₘ : S → T
    positionₘ : {s : S} → Q (shapeₘ s) → P s 
    isMCMorphism : IsMndContainerMorphism _ _ _ _ S P T Q Aₘ Bₘ shapeₘ positionₘ
 

{-# OPTIONS --cubical #-}

open import MndContainer as MC
open import CategoryTheory
open import ContainersPlus

open import Level renaming (suc to lsuc ; zero to lzero)
open import Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.HITs.PropositionalTruncation


module _ where

module MndContainerToMonad {ℓs ℓp : Level} (S : Set ℓs) (P : S → Set ℓp)
                           (MCon : MndContainer ℓs ℓp (S ◁ P)) where

  open MC.MndContainer MCon hiding (S ; P)
  open MC.IsMndContainer isMndContainer
  open _⇒_
  open Monad

  monad : Monad (ℓs ⊔ ℓp) (ℓs ⊔ ℓp) ⟦ S ◁ P ⟧f
  α (η monad) X x = (ι , const x)
  nat (η monad) X Y f = ∣ refl ∣₁
  α (μ monad) X (s , f) = (σ s (fst ∘ f) , λ p → snd (f (pr₁ _ _ p)) (pr₂ _ _ p))
  nat (μ monad) X Y f = ∣ refl ∣₁
  μ-unit-l monad i X (s , f) = (unit-l s i , λ p → f (pr-unit-l i p))
  μ-unit-r monad i X (s , f) = (unit-r s i , λ p → f (pr-unit-r i p))
  μ-assoc monad i X (s , f) = (assoc s (fst ∘ f) (λ p p' → fst (snd (f p) p')) i 
                              , λ p → snd (snd (f (pr-mul₁ i p)) (pr-mul₁₂ i p)) (pr-mul₂₂ i p))

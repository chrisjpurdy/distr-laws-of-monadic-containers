{-# OPTIONS --cubical #-}

open import ContainersPlus
open import MndContainer as MC
open MC.MndContainer
open IsMndContainer
open import MndDistributiveLaw as MDL
open MDL.MndDistributiveLaw

open import Level renaming (suc to lsuc ; zero to lzero)
open import Function
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma renaming (fst to π₁ ; snd to π₂)
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to rec⊥ ; rec* to rec⊥*)
open import Cubical.Relation.Nullary

module NoGoTheorem where

  ConstantShape : (ℓs ℓp : Level) 
                  (S : Set ℓs) (P : S → Set ℓp) 
                  (s : S) → Set (lsuc ℓp)
  ConstantShape _ _ S P s = P s ≡ ⊥* 

  record S3Property (ℓs ℓp : Level) 
                    (S : Set ℓs) (P : S → Set ℓp) 
                    (Aₘ : MndContainer _ _ (S ◁ P)) 
                    (s : S) (f : P s → S) : Set (lsuc (ℓs ⊔ ℓp)) where
    field
      posInhabited : NonEmpty (P s)
      decEq : Discrete (P s)
      s3Shape : (p : P s) → σ Aₘ s (λ p' → case 
          (ι Aₘ) 
          (f p')
        (decEq p' p)) ≡ ι Aₘ
      s3Pos : (p : P s) → PathP (λ i → P (s3Shape p i) → P s)
                          (λ p' → pr₁ Aₘ _ _ p')
                          (λ p' → p)
  open S3Property

  compositeS3 : (ℓs ℓp : Level) 
                (S : Set ℓs) (P : S → Set ℓp) 
                (Aₘ : MndContainer _ _ (S ◁ P))
                (s : S) (f : P s → S)
                (s3 : S3Property _ _ S P Aₘ s f)
                (T : Set ℓs) (Q : T → Set ℓp)
                (Bₘ : MndContainer _ _ (T ◁ Q))
                (distr : MndDistributiveLaw _ _ S P T Q Aₘ Bₘ)
                (t : T) (p : P s) 
                → u₁ distr s (λ p' → case t (ι Bₘ) (decEq s3 p' p)) ≡ t
  compositeS3 ℓs ℓp S P Aₘ s f s3 T Q Bₘ distr t p = step₁ ∙ step₂ ∙ step₃ ∙ step₄ ∙ step₅ ∙ unit-ιA-shape₁ distr t
    where
      step₁ : u₁ distr s (λ p' → case 
                    t
                    (ι Bₘ)
                  (decEq s3 p' p)) 
            ≡ u₁ distr s (λ p' → case 
                    (u₁ distr (ι Aₘ) (λ _ → t))
                    (u₁ distr (f p') (λ _ → ι Bₘ))
                  (decEq s3 p' p))
      step₁ i = u₁ distr s (λ p' → case 
                  (unit-ιA-shape₁ distr t (~ i)) 
                  (unit-ιB-shape₁ distr (f p') (~ i)) 
                (decEq s3 p' p))

      step₂ : u₁ distr s (λ p' → case 
                  (u₁ distr (ι Aₘ) (λ _ → t))
                  (u₁ distr (f p') (λ _ → ι Bₘ))
                (decEq s3 p' p))
              ≡ u₁ distr s (λ p' →
                  u₁ distr (case (ι Aₘ) (f p') (decEq s3 p' p))
                           (const (case t (ι Bₘ) (decEq s3 p' p)))
                )
      step₂ i = u₁ distr s (λ p' → (decLem₁ (decEq s3) (ι Aₘ) (f p') (const t) (const (ι Bₘ)) (u₁ distr) p' p 
                                    ∙ cong (u₁ distr (case (ι Aₘ) (f p') (decEq s3 p' p))) (decLem₂ (decEq s3) _ _ _ _ p' p)
                                   ) i
                           )

      step₃ : u₁ distr s (λ p' → u₁ distr
                (case (ι Aₘ) (f p') (decEq s3 p' p))
                (const (case t (ι Bₘ) (decEq s3 p' p)))
              )
              ≡ u₁ distr 
                  (σ Aₘ s (λ p' → case (ι Aₘ) (f p') (decEq s3 p' p)))
                  (λ p' → case t (ι Bₘ) (decEq s3 (pr₁ Aₘ _ _ p') p))
      step₃ i = mul-A-shape₁ distr s (λ p' → case (ι Aₘ) (f p') (decEq s3 p' p)) (λ p₁ _ → case t (ι Bₘ) (decEq s3 p₁ p)) (~ i)

      step₄ : u₁ distr 
                (σ Aₘ s (λ p' → case (ι Aₘ) (f p') (decEq s3 p' p)))
                (λ p' → case t (ι Bₘ) (decEq s3 (pr₁ Aₘ _ _ p') p))
              ≡ u₁ distr (ι Aₘ) (λ p' → case t (ι Bₘ) (decEq s3 p p))
      step₄ i = u₁ distr (s3Shape s3 p i) (λ p' → case t (ι Bₘ) (decEq s3 (s3Pos s3 p i p') p))

      step₅ : u₁ distr (ι Aₘ) (λ p' → case t (ι Bₘ) (decEq s3 p p))
          ≡ u₁ distr (ι Aₘ) (const t)
      step₅ i = u₁ distr (ι Aₘ) (λ p' → case t (ι Bₘ) (snd (decRefl (decEq s3) p) i))

  module _ (ℓs ℓp : Level) 
           (S : Set ℓs) (P : S → Set ℓp) 
           (Aₘ : MndContainer _ _ (S ◁ P))
           (s : S) (f : P s → S)
           (s3 : S3Property _ _ S P Aₘ s f)
           (T : Set ℓs) (Q : T → Set ℓp)
           (Bₘ : MndContainer _ _ (T ◁ Q))
           (distr : MndDistributiveLaw _ _ S P T Q Aₘ Bₘ) where

    step₁ : (t t' : T) (constt : ConstantShape _ _ _ Q t)
            (p p' : P s)
          → σ Bₘ t (const (ι Bₘ))
          ≡ σ Bₘ (u₁ distr s (λ y → case t (ι Bₘ) (decEq s3 y p)))
                 (λ y → u₁ distr (u₂ distr s (λ z → case t (ι Bₘ) (decEq s3 z p)) y)
                                 (λ z → case t' (ι Bₘ) (decEq s3 (v₁ distr y z) p'))
                 )
    step₁ t t' constt p p' i = σ Bₘ (compositeS3 ℓs ℓp S P Aₘ s f s3 T Q Bₘ distr t p (~ i)) 
                                    (toPathP {A = λ i → Q (compositeS3 ℓs ℓp S P Aₘ s f s3 T Q Bₘ distr t p (~ i)) → T} 
                                             {x = const (ι Bₘ)}
                                             {y = λ y → u₁ distr (u₂ distr s (λ z → case t (ι Bₘ) (decEq s3 z p)) y) 
                                                           (λ z → case t' (ι Bₘ) (decEq s3 (v₁ distr y z) p'))
                                             }
                                             (transpFun {B = Q} _ _ (sym (compositeS3 ℓs ℓp S P Aₘ s f s3 T Q Bₘ distr t p)) (const (ι Bₘ)) 
                                              ∙ funExt (λ x → rec⊥* (transport constt (subst⁻ Q (sym (compositeS3 ℓs ℓp S P Aₘ s f s3 T Q Bₘ distr t p)) x)))
                                             )
                                             i
                                    )

    step₂ : (t t' : T) (p p' : P s)
          → σ Bₘ (u₁ distr s (λ y → case t (ι Bₘ) (decEq s3 y p)))
                 (λ y → u₁ distr (u₂ distr s (λ z → case t (ι Bₘ) (decEq s3 z p)) y)
                                 (λ z → case t' (ι Bₘ) (decEq s3 (v₁ distr y z) p'))
                 )
          ≡ u₁ distr s (λ y → σ Bₘ (case t (ι Bₘ) (decEq s3 y p)) (const (case t' (ι Bₘ) (decEq s3 y p'))))
    step₂ t t' p p' = sym (mul-B-shape₁ distr _ _ _)

    step₃Aux : (t t' : T) (p p' : P s) (pdist : ¬ (p ≡ p'))
               (y : P s)
             → σ Bₘ (case t (ι Bₘ) (decEq s3 y p)) (const (case t' (ι Bₘ) (decEq s3 y p')))
             ≡ case t (case t' (ι Bₘ) (decEq s3 y p')) (decEq s3 y p)
    step₃Aux t t' p p' pdist y with decEq s3 y p | decEq s3 y p'
    ... | (yes e) | (yes e') = rec⊥ (pdist (sym e ∙ e'))
    ... | (yes e) | (no e')  = unit-r (isMndContainer Bₘ) t
    ... | (no e)  | (yes e') = unit-l (isMndContainer Bₘ) t'
    ... | (no e)  | (no e')  = unit-r (isMndContainer Bₘ) (ι Bₘ)

    step₃ : (t t' : T) (p p' : P s) (pdist : ¬ (p ≡ p'))
          → u₁ distr s (λ y → σ Bₘ (case t (ι Bₘ) (decEq s3 y p)) (const (case t' (ι Bₘ) (decEq s3 y p'))))
          ≡ u₁ distr s (λ y → case t (case t' (ι Bₘ) (decEq s3 y p')) (decEq s3 y p))
    step₃ t t' p p' pdist i = u₁ distr s (λ y → step₃Aux t t' p p' pdist y i)

    mainLem : (t t' : T) (constt : ConstantShape _ _ _ Q t)
              (p p' : P s) (pdist : ¬ (p ≡ p')) 
            → t ≡ u₁ distr s (λ y → case t (case t' (ι Bₘ) (decEq s3 y p')) (decEq s3 y p))
    mainLem t t' constt p p' pdist = sym (unit-r (isMndContainer Bₘ) t) ∙ step₁ t t' constt p p' ∙ step₂ t t' p p' ∙ step₃ t t' p p' pdist

    noGoTheorem : (t t' : T) (tdist : ¬ (t ≡ t'))
                  (constt : ConstantShape _ _ _ Q t)
                  (constt' : ConstantShape _ _ _ Q t')
                  (p p' : P s) (pdist : ¬ (p ≡ p'))
                → ⊥
    noGoTheorem t t' tdist constt constt' p p' pdist = tdist (mainLem t t' constt p p' pdist 
                                                             ∙ aux 
                                                             ∙ sym (mainLem t' t constt' p' p (pdist ∘ sym))
                                                             )
      where
        aux : u₁ distr s (λ y → case t (case t' (ι Bₘ) (decEq s3 y p')) (decEq s3 y p))
            ≡ u₁ distr s (λ y → case t' (case t (ι Bₘ) (decEq s3 y p)) (decEq s3 y p'))
        aux i = u₁ distr s (λ y → decLem₃ (decEq s3) t t' (ι Bₘ) p p' y pdist i)

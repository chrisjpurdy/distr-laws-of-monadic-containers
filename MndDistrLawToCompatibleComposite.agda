{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import ContainersPlus
open import MndContainer as MC
open MC.MndContainer
open MC.IsMndContainer
open import MndContainerMorphism as MCM
open MCM.MndContainerMorphism
open MCM.IsMndContainerMorphism
open import MndDistributiveLaw as MDL
open import MndCompatibleComposite as MCC

open import Level renaming (suc to lsuc ; zero to lzero)
open import Function
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Data.Sigma renaming (fst to π₁ ; snd to π₂)

{-

  Most of the proof that a monadic container distributive law lets you
  construct a compatible composite monadic container.

  The assoc, pr-mul₁, pr-mul₁₂, and pr-mul₂₂ equations are pending 
  formalisation (we probably need to build up a set of helper functions
  to construct these heavily dependent proofs). The proofs of these 
  equations are in the appendix of the related paper "Distributive
  Laws of Monadic Containers".

-}

module MndDistrLawToCompatibleComposite (ℓs ℓp : Level) 
  (S : Set ℓs) (P : S → Set ℓp) (T : Set ℓs) (Q : T → Set ℓp)
  (Aₘ : MndContainer _ _ (S ◁ P)) (Bₘ : MndContainer _ _ (T ◁ Q)) 
  (distr : MndDistributiveLaw _ _ S P T Q Aₘ Bₘ) where

  open MCC.MndCompatibleComposite
  open MndDistributiveLaw distr

  -- Left unit proof steps
  unit-l-step1 : (t : T) (f : Q t → S) → _
  unit-l-step1 t f = contP-shape {P = Q} (unit-l (isMndContainer Bₘ) (u₁ (ι Aₘ) (λ x → t))) 
                                         (λ i q → σ Aₘ (u₂ (ι Aₘ) (λ x → t) (pr-unit-l (isMndContainer Bₘ) i q)) 
                                                       (λ p → f (v₂ (pr-unit-l (isMndContainer Bₘ) i q) p))
                                         )
  unit-l-step2 : (t : T) (f : Q t → S) → _
  unit-l-step2 t f = contP-shape {P = Q} (unit-ιA-shape₁ t) 
                                         (λ i q → σ Aₘ (unit-ιA-shape₂ t i q) 
                                                       (λ p → f (unit-ιA-pos₂ t i q p))
                                         )
  unit-l-step3 : (t : T) (f : Q t → S) → _
  unit-l-step3 t f = contP-shape {P = Q} refl (λ i q → unit-l (isMndContainer Aₘ) (f q) i)

  pr-unit-l-step1 : (t : T) (f : Q t → S) → PathP (λ i → ◇ Q P (unit-l-step1 t f i) → ◇ Q P (t , f)) 
                                                  (λ x → (v₂ (pr₂ Bₘ _ _ (π₁ x)) (pr₁ Aₘ _ _ (π₂ x)) , pr₂ Aₘ _ _ (π₂ x))) 
                                                  (λ x → (v₂ (π₁ x) (pr₁ Aₘ _ _ (π₂ x)) , pr₂ Aₘ _ _ (π₂ x)))
  pr-unit-l-step1 t f = contP-position {P = Q} {Q = P} 
                                       (unit-l (isMndContainer Bₘ) (u₁ (ι Aₘ) (λ x → t))) 
                                       (λ i q → σ Aₘ (u₂ (ι Aₘ) (λ x → t) (pr-unit-l (isMndContainer Bₘ) i q)) 
                                                     (λ p → f (v₂ (pr-unit-l (isMndContainer Bₘ) i q) p))
                                       ) 
                                       (λ i x → v₂ (pr-unit-l (isMndContainer Bₘ) i (π₁ x)) (pr₁ Aₘ _ _ (π₂ x))) 
                                       (λ i x → pr₂ Aₘ _ _ (π₂ x))
  pr-unit-l-step2 : (t : T) (f : Q t → S) → PathP (λ i → ◇ Q P (unit-l-step2 t f i) → ◇ Q P (t , f))
                                                  (λ x → (v₂ (π₁ x) (pr₁ Aₘ _ _ (π₂ x)) , pr₂ Aₘ _ _ (π₂ x))) 
                                                  (λ x → (π₁ x , pr₂ Aₘ _ _ (π₂ x)))
  pr-unit-l-step2 t f = contP-position {P = Q} {Q = P} 
                                       (unit-ιA-shape₁ t)
                                       (λ i q → σ Aₘ (unit-ιA-shape₂ t i q) 
                                                     (λ p → f (unit-ιA-pos₂ t i q p))
                                       ) 
                                       (λ i x → unit-ιA-pos₂ t i (π₁ x) (pr₁ Aₘ _ _ (π₂ x))) 
                                       (λ i x → pr₂ Aₘ _ _ (π₂ x))
  pr-unit-l-step3 : (t : T) (f : Q t → S) → PathP (λ i → ◇ Q P (unit-l-step3 t f i) → ◇ Q P (t , f))
                                                  (λ x → (π₁ x , pr₂ Aₘ _ _ (π₂ x))) 
                                                  (λ x → x)
  pr-unit-l-step3 t f = contP-position {P = Q} {Q = P} 
                                       refl
                                       (λ i q → unit-l (isMndContainer Aₘ) (f q) i)
                                       (λ i x → π₁ x)
                                       (λ i x → pr-unit-l (isMndContainer Aₘ) i (π₂ x))

  -- Right unit proof steps 
  unit-r-step1 : (t : T) (f : Q t → S) → _
  unit-r-step1 t f = contP-shape {P = Q} refl 
                                         (λ i q → unit-r (isMndContainer Aₘ) (u₂ (f (pr₁ Bₘ t (λ q₁ → u₁ (f q₁) (λ x → ι Bₘ)) q)) (λ x → ι Bₘ) (pr₂ Bₘ t (λ q₁ → u₁ (f q₁) (λ x → ι Bₘ)) q)) i)
  unit-r-step2 : (t : T) (f : Q t → S) → _
  unit-r-step2 t f = contP-shape {P = Q} (λ i → σ Bₘ t (λ q → unit-ιB-shape₁ (f q) i)) 
                                         (λ i q → unit-ιB-shape₂ _ i (pr₂ Bₘ _ _ q)) 
  unit-r-step3 : (t : T) (f : Q t → S) → _
  unit-r-step3 t f = contP-shape {P = Q} (unit-r (isMndContainer Bₘ) t)    
                                         (λ i q → f (pr-unit-r (isMndContainer Bₘ) i q))
  pr-unit-r-step1 : (t : T) (f : Q t → S) → PathP (λ i → ◇ Q P (unit-r-step1 t f i) → ◇ Q P (t , f)) 
                                                  (λ x → (pr₁ Bₘ _ _ (π₁ x) , v₁ (pr₂ Bₘ _ _ (π₁ x)) (pr₁ Aₘ _ _ (π₂ x)))) 
                                                  (λ x → (pr₁ Bₘ _ _ (π₁ x) , v₁ (pr₂ Bₘ _ _ (π₁ x)) (π₂ x)))
  pr-unit-r-step1 t f = contP-position {P = Q} {Q = P}
                                       refl
                                       (λ i q → unit-r (isMndContainer Aₘ) (u₂ (f (pr₁ Bₘ t (λ q₁ → u₁ (f q₁) (λ x → ι Bₘ)) q)) (λ x → ι Bₘ) (pr₂ Bₘ t (λ q₁ → u₁ (f q₁) (λ x → ι Bₘ)) q)) i)
                                       (λ i x → pr₁ Bₘ _ _ (π₁ x))
                                       (λ i x → v₁ (pr₂ Bₘ _ _ (π₁ x)) (pr-unit-r (isMndContainer Aₘ) i (π₂ x)))
  pr-unit-r-step2 : (t : T) (f : Q t → S) → PathP (λ i → ◇ Q P (unit-r-step2 t f i) → ◇ Q P (t , f)) 
                                                  (λ x → (pr₁ Bₘ _ _ (π₁ x) , v₁ (pr₂ Bₘ _ _ (π₁ x)) (π₂ x))) 
                                                  (λ x → (pr₁ Bₘ _ _ (π₁ x) , π₂ x))
  pr-unit-r-step2 t f = contP-position {P = Q} {Q = P}
                                       (λ i → σ Bₘ t (λ q → unit-ιB-shape₁ (f q) i)) 
                                       (λ i q → unit-ιB-shape₂ _ i (pr₂ Bₘ _ _ q))
                                       (λ i x → pr₁ Bₘ t (λ q → unit-ιB-shape₁ (f q) i) (π₁ x))
                                       (λ i x → unit-ιB-pos₁ _ i (pr₂ Bₘ _ _ (π₁ x)) (π₂ x))
  pr-unit-r-step3 : (t : T) (f : Q t → S) → PathP (λ i → ◇ Q P (unit-r-step3 t f i) → ◇ Q P (t , f)) 
                                                  (λ x → (pr₁ Bₘ _ _ (π₁ x) , π₂ x)) 
                                                  (λ x → x)
  pr-unit-r-step3 t f = contP-position {P = Q} {Q = P}
                                       (unit-r (isMndContainer Bₘ) t)    
                                       (λ i q → f (pr-unit-r (isMndContainer Bₘ) i q))
                                       (λ i x → pr-unit-r (isMndContainer Bₘ) i (π₁ x))
                                       (λ i x → π₂ x)

  -- Middle unit shape proof steps
  mu-step1 : (s : T) (f : Q s → S) →
             PathP (λ i → Σ T (λ v → Q v → S))
             (s , f)
             (σ Bₘ s (λ _ → ι Bₘ) ,
               λ q → σ Aₘ (ι Aₘ) (λ p → f (pr₁ Bₘ s (λ _ → ι Bₘ) q))
             ) 
  mu-step1 s f i = (unit-r (isMndContainer Bₘ) s (~ i) , λ q → unit-l (isMndContainer Aₘ) (f (pr-unit-r (isMndContainer Bₘ) (~ i) q)) (~ i)) 

  mu-step2 : (s : T) (f : Q s → S) →
             PathP (λ i → Σ T (λ v → Q v → S))
             (σ Bₘ s (λ _ → ι Bₘ) ,
               λ q → σ Aₘ (ι Aₘ) (λ p → f (pr₁ Bₘ s (λ _ → ι Bₘ) q))
             )
             (σ Bₘ s (λ q → u₁ (ι Aₘ) (λ x → ι Bₘ)) ,
               λ q → σ Aₘ (u₂ (ι Aₘ) (λ x → ι Bₘ) (pr₂ Bₘ s (λ q₁ → u₁ (ι Aₘ) (λ x → ι Bₘ)) q))
                          (λ p → f (pr₁ Bₘ s (λ q₁ → u₁ (ι Aₘ) (λ x → ι Bₘ)) q))
             )
  mu-step2 s f i = (σ Bₘ s (λ q → unit-ιA-shape₁ (ι Bₘ) (~ i)) , λ q → σ Aₘ (unit-ιA-shape₂ (ι Bₘ) (~ i) (pr₂ Bₘ _ _ q)) (λ _ → f (pr₁ Bₘ s (λ _ → unit-ιA-shape₁ (ι Bₘ) (~ i)) q)))

  mu-pos-step1 : (s : T) (f : Q s → S) →
                 PathP (λ i → ◇ Q P (mu-step1 s f i) → ◇ Q P (s , f))
                 (λ x → x)
                 (λ x → (pr₁ Bₘ _ _ (π₁ x) , pr₂ Aₘ _ _ (π₂ x)))
  mu-pos-step1 s f i (q , p) = (pr-unit-r (isMndContainer Bₘ) (~ i) q , pr-unit-l (isMndContainer Aₘ) (~ i) p)

  mu-pos-step2 : (s : T) (f : Q s → S) →
                 PathP (λ i → ◇ Q P (mu-step2 s f i) → ◇ Q P (s , f))
                 (λ x → (pr₁ Bₘ _ _ (π₁ x) , pr₂ Aₘ _ _ (π₂ x)))
                 (λ x → (pr₁ Bₘ _ _ (π₁ x) , pr₂ Aₘ _ _ (π₂ x)))
  mu-pos-step2 s f i (q , p) = (pr₁ Bₘ _ _ q , pr₂ Aₘ _ _ p)


  composite : MndCompatibleComposite _ _ T Q S P Bₘ Aₘ
  σᶜ composite (t , f) g = (
      σ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) , 
      λ q → σ Aₘ (u₂ (f (pr₁ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q)) 
                     (π₁ ∘ g ∘ (pr₁ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q ,_)) 
                     (pr₂ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q)
                 ) 
                 (λ p → π₂ (g (pr₁ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q , v₁ (pr₂ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q) p)) (v₂ (pr₂ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q) p))
    )
  prᶜ₁ composite (t , f) g (q , p) = (pr₁ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q 
                                     , v₁ (pr₂ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q) (pr₁ Aₘ _ _ p)
                                     )
  prᶜ₂ composite (t , f) g (q , p) = (v₂ (pr₂ Bₘ t (λ q → u₁ (f q) (π₁ ∘ g ∘ (q ,_))) q) (pr₁ Aₘ _ _ p) 
                                     , pr₂ Aₘ _ _ p
                                     )
  unit-l (isMCont composite) (t , f) = unit-l-step1 t f ∙ unit-l-step2 t f ∙ unit-l-step3 t f
  unit-r (isMCont composite) (t , f) = unit-r-step1 t f ∙ unit-r-step2 t f ∙ unit-r-step3 t f
  assoc (isMCont composite) (a , f) g h = {!   !}
  pr-unit-r (isMCont composite) {(t , f)} = compPathP' {B = (λ x → ◇ Q P x → ◇ Q P (t , f))} 
                                                       {p = unit-r-step1 t f} 
                                                       {q = unit-r-step2 t f ∙ unit-r-step3 t f}
                                                       (pr-unit-r-step1 t f)
                                                       (compPathP' {B = (λ x → ◇ Q P x → ◇ Q P (t , f))} 
                                                                   {p = unit-r-step2 t f} 
                                                                   {q = unit-r-step3 t f} 
                                                                   (pr-unit-r-step2 t f) 
                                                                   (pr-unit-r-step3 t f)
                                                       )
  pr-unit-l (isMCont composite) {(t , f)} = compPathP' {B = (λ x → ◇ Q P x → ◇ Q P (t , f))} 
                                                       {p = unit-l-step1 t f} 
                                                       {q = unit-l-step2 t f ∙ unit-l-step3 t f}
                                                       (pr-unit-l-step1 t f)
                                                       (compPathP' {B = (λ x → ◇ Q P x → ◇ Q P (t , f))} 
                                                                   {p = unit-l-step2 t f} 
                                                                   {q = unit-l-step3 t f} 
                                                                   (pr-unit-l-step2 t f) 
                                                                   (pr-unit-l-step3 t f)
                                                       )
  pr-mul₁ (isMCont composite) = {!   !}
  pr-mul₁₂ (isMCont composite) = {!   !}
  pr-mul₂₂ (isMCont composite) = {!   !}
  ι-pres (s-inj composite) = refl
  σ-pres (s-inj composite) s f i = (σ Bₘ s (λ q → unit-ιA-shape₁ (f q) (~ i)) , λ q → unit-r (isMndContainer Aₘ) (unit-ιA-shape₂ _ (~ i) (pr₂ Bₘ _ _ q)) (~ i))
  pr₁-pres (s-inj composite) s f i (q , p) = pr₁ Bₘ s (λ q' → unit-ιA-shape₁ (f q') (~ i)) q
  pr₂-pres (s-inj composite) s f i (q , p) = unit-ιA-pos₂ (f (pr₁ Bₘ s (λ q₁ → unit-ιA-shape₁ (f q₁) (~ i)) q)) (~ i) (pr₂ Bₘ _ _ q) (pr-unit-r (isMndContainer Aₘ) (~ i) p)
  ι-pres (t-inj composite) = refl
  σ-pres (t-inj composite) s f i = (unit-l (isMndContainer Bₘ) (unit-ιB-shape₁ s (~ i)) (~ i) , λ q → σ Aₘ (unit-ιB-shape₂ s (~ i) (pr-unit-l (isMndContainer Bₘ) (~ i) q)) (λ p → f (unit-ιB-pos₁ s (~ i) (pr-unit-l (isMndContainer Bₘ) (~ i) q) p)))
  pr₁-pres (t-inj composite) s f i (q , p) = unit-ιB-pos₁ s (~ i) (pr-unit-l (isMndContainer Bₘ) (~ i) q) (pr₁ Aₘ _ _ p)
  pr₂-pres (t-inj composite) s f i (q , p) = pr₂ Aₘ (unit-ιB-shape₂ s (~ i) (pr-unit-l (isMndContainer Bₘ) (~ i) q)) (λ p → f (unit-ιB-pos₁ s (~ i) (pr-unit-l (isMndContainer Bₘ) (~ i) q) p)) p
  middle-unit-shape composite s f = mu-step1 s f ∙ mu-step2 s f
  middle-unit-pos composite s f = compPathP' {B = (λ x → ◇ Q P x → ◇ Q P (s , f))}
                                              {p = mu-step1 s f}
                                              {q = mu-step2 s f}
                                              (mu-pos-step1 s f)
                                              (mu-pos-step2 s f)

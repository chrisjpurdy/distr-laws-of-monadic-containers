{-# OPTIONS --cubical #-}

{-
  Some examples of containers and helper functions to reason about them
-}

open import ContainersPlus

open import Level renaming (suc to lsuc ; zero to lzero)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma renaming (fst to π₁ ; snd to π₂)
open import Cubical.Data.Sum

data 𝟚 {ℓ} : Set ℓ where
  true : 𝟚 
  false : 𝟚
  
JustOrNothing : ∀ {s p} → 𝟚 {s} → Set p
JustOrNothing true  = ⊤
JustOrNothing {_} {p} false = ⊥* {p}

LOrR : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} → A ⊎ B → Set ℓ''
LOrR (inl a) = ⊤
LOrR (inr b) = ⊥*

Maybe : ∀ {s p} → Container s p 
Maybe = 𝟚 ◁ JustOrNothing

List : Container lzero lzero
List = ℕ ◁ Fin

State : ∀ {s} → (S : Set s) → Container s s
State S = (S → S) ◁ λ _ → S

record Monoid (ℓ : Level) (A : Set ℓ) : Set ℓ where
  field
    _⊕_ : A → A → A
    e : A
    ⊕-unit-l : (a : A) → e ⊕ a ≡ a
    ⊕-unit-r : (a : A) → a ⊕ e ≡ a
    ⊕-assoc  : (a b c : A) → a ⊕ (b ⊕ c) ≡ (a ⊕ b) ⊕ c
open Monoid

ℕ+-monoid : Monoid lzero ℕ
_⊕_ ℕ+-monoid = _+_
e ℕ+-monoid = 0
⊕-unit-l ℕ+-monoid n = refl
⊕-unit-r ℕ+-monoid = +-zero
⊕-assoc ℕ+-monoid = +-assoc

module MonadExamples where

  open import MndContainer as MC
  open MC.MndContainer
  open MC.IsMndContainer

  -- Examples of monadic containers

  ReaderM : ∀ {ℓs ℓp} (A : Set ℓp) → MndContainer ℓs ℓp (⊤ ◁ λ _ → A)
  ι (ReaderM A) = tt
  σ (ReaderM A) _ _ = tt
  pr₁ (ReaderM A) _ _ p = p
  pr₂ (ReaderM A) _ _ p = p
  unit-l (isMndContainer (ReaderM A)) tt = refl
  unit-r (isMndContainer (ReaderM A)) tt = refl
  assoc (isMndContainer (ReaderM A)) tt _ _ = refl
  pr-unit-r (isMndContainer (ReaderM A)) = refl
  pr-unit-l (isMndContainer (ReaderM A)) = refl
  pr-mul₁ (isMndContainer (ReaderM A)) = refl
  pr-mul₁₂ (isMndContainer (ReaderM A)) = refl
  pr-mul₂₂ (isMndContainer (ReaderM A)) = refl

  WriterM : {ℓ ℓ' : Level} (A : Set ℓ) (mon : Monoid ℓ A) → MndContainer ℓ ℓ' (A ◁ const ⊤)
  ι (WriterM A mon) = e mon
  σ (WriterM A mon) a b = (_⊕_ mon) a (b tt)
  pr₁ (WriterM A mon) _ _ tt = tt
  pr₂ (WriterM A mon) _ _ tt = tt
  unit-l (isMndContainer (WriterM A mon)) a = ⊕-unit-l mon a
  unit-r (isMndContainer (WriterM A mon)) a = ⊕-unit-r mon a
  assoc (isMndContainer (WriterM A mon)) a b c = ⊕-assoc mon a (b tt) (c tt tt)
  pr-unit-r (isMndContainer (WriterM A mon)) i tt = tt
  pr-unit-l (isMndContainer (WriterM A mon)) i tt = tt
  pr-mul₁ (isMndContainer (WriterM A mon)) i tt = tt
  pr-mul₁₂ (isMndContainer (WriterM A mon)) i tt = tt
  pr-mul₂₂ (isMndContainer (WriterM A mon)) i tt = tt

  StreamM : ∀ {ℓs} → MndContainer ℓs lzero (⊤ ◁ const ℕ)
  StreamM = ReaderM ℕ

  StateM : ∀ {ℓs} (S : Set ℓs) → MndContainer ℓs ℓs (State S)
  ι (StateM S) s = s
  σ (StateM S) f g s = g s (f s)
  pr₁ (StateM S) _ _ s = s
  pr₂ (StateM S) f _ s = f s
  unit-l (isMndContainer (StateM S)) f = refl
  unit-r (isMndContainer (StateM S)) f = refl
  assoc (isMndContainer (StateM S)) f g h = refl
  pr-unit-r (isMndContainer (StateM S)) = refl
  pr-unit-l (isMndContainer (StateM S)) = refl
  pr-mul₁ (isMndContainer (StateM S)) = refl
  pr-mul₁₂ (isMndContainer (StateM S)) = refl
  pr-mul₂₂ (isMndContainer (StateM S)) = refl

  MaybeM : ∀ {ℓs ℓp} → MndContainer ℓs ℓp Maybe
  ι MaybeM = true
  σ MaybeM true f = f tt
  σ MaybeM false f = false
  pr₁ MaybeM true _ _ = tt
  pr₂ MaybeM true _ p = p
  pr₂ MaybeM false _ ()
  unit-l (isMndContainer MaybeM) a = refl
  unit-r (isMndContainer MaybeM) true = refl
  unit-r (isMndContainer MaybeM) false = refl
  assoc (isMndContainer MaybeM) true b c = refl
  assoc (isMndContainer MaybeM) false b c = refl
  pr-unit-r (isMndContainer MaybeM) {true} i tt = tt
  pr-unit-l (isMndContainer MaybeM) {true} i p = p
  pr-mul₁ (isMndContainer MaybeM)  {true} {b} {c} i = λ _ → tt
  pr-mul₁₂ (isMndContainer MaybeM) {true} {b} {c} i p' = pr₁ MaybeM (b tt) (c tt) p'
  pr-mul₂₂ (isMndContainer MaybeM) {true} {b} {c} i p' = pr₂ MaybeM (b tt) (c tt) p'

  -- Note: MaybeM is also special case of CoproductM when E = ⊤

  CoproductM : ∀ {ℓs ℓs' ℓp} (E : Set ℓs) → MndContainer (ℓ-max ℓs ℓs') ℓp ((⊤ {ℓs'}) ⊎ E ◁ LOrR)
  ι (CoproductM E) = inl tt
  σ (CoproductM E) (inl tt) f = f tt
  σ (CoproductM E) (inr e) f = inr e
  pr₁ (CoproductM E) (inl tt) _ _ = tt
  pr₂ (CoproductM E) (inl tt) _ y = y
  unit-l (isMndContainer (CoproductM E)) _ = refl
  unit-r (isMndContainer (CoproductM E)) (inl tt) = refl
  unit-r (isMndContainer (CoproductM E)) (inr e) = refl
  assoc (isMndContainer (CoproductM E)) (inl tt) b c = refl
  assoc (isMndContainer (CoproductM E)) (inr e) b c = refl
  pr-unit-r (isMndContainer (CoproductM E)) {inl tt} i tt = tt
  pr-unit-l (isMndContainer (CoproductM E)) = refl
  pr-mul₁ (isMndContainer (CoproductM E)) {inl tt} = refl
  pr-mul₁ (isMndContainer (CoproductM E)) {inr e} i ()
  pr-mul₁₂ (isMndContainer (CoproductM E)) {inl tt} = refl
  pr-mul₁₂ (isMndContainer (CoproductM E)) {inr e} i ()
  pr-mul₂₂ (isMndContainer (CoproductM E)) {inl tt} = refl
  pr-mul₂₂ (isMndContainer (CoproductM E)) {inr e} i ()


module ComonadExamples where

  open import DirectedContainer as DC
  open DC.DirectedContainer

  -- Examples of directed containers

  WriterC : ∀ {ℓs ℓp} → (A : Set ℓs) → DirectedContainer ℓs ℓp (A ◁ (const (⊤ {ℓp})))
  o (WriterC A) _ = tt 
  _↓_ (WriterC A) a tt = a
  _⊕_ (WriterC A) tt tt = tt
  unitl-↓ (WriterC A) a = refl
  distr-↓-⊕ (WriterC A) a tt tt = refl
  unitl-⊕ (WriterC A) a tt = refl
  unitr-⊕ (WriterC A) a tt = refl
  assoc-⊕ (WriterC A) a tt tt i tt = tt

  ReaderC : ∀ {ℓs ℓp} (A : Set ℓp) (mon : Monoid ℓp A) → DirectedContainer ℓs ℓp ((⊤ {ℓs}) ◁ (const A))
  o (ReaderC A mon) tt = e mon 
  _↓_ (ReaderC A mon) tt a = tt
  _⊕_ (ReaderC A mon) = _⊕_ mon
  unitl-↓ (ReaderC A mon) tt = refl
  distr-↓-⊕ (ReaderC A mon) tt a a' = refl
  unitl-⊕ (ReaderC A mon) tt = ⊕-unit-l mon
  unitr-⊕ (ReaderC A mon) tt = ⊕-unit-r mon
  assoc-⊕ (ReaderC A mon) tt a a' i a'' = ⊕-assoc mon a a' a'' (~ i)

  StreamC : ∀ {ℓs} → DirectedContainer ℓs lzero ((⊤ {ℓs}) ◁ (const ℕ))
  StreamC = ReaderC ℕ ℕ+-monoid

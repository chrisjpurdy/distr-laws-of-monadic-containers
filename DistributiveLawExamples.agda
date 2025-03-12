{-# OPTIONS --cubical --allow-unsolved-metas #-}

{-
  Examples of various distribute laws, including uniqueness proofs for certain ones
-}

open import ContainersPlus
open import ContainerExamples

open import Level renaming (suc to lsuc ; zero to lzero)
open import Function 
open import Cubical.Foundations.Prelude hiding (_▷_)
open import Cubical.Data.Empty renaming (rec* to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma renaming (fst to π₁ ; snd to π₂)

module DistributiveLawExamples where

  open import MndContainer as MC
  open MC.MndContainer
  open MC.IsMndContainer
  open import MndDistributiveLaw as DL
  open DL.MndDistributiveLaw
  open MonadExamples

  MaybeDistr : ∀ {ℓs ℓp} (S : Set ℓs) (P : S → Set ℓp) (MC : MndContainer ℓs ℓp (S ▷ P)) →
               MndDistributiveLaw ℓs ℓp 𝟚 JustOrNothing S P MaybeM MC
  u₁ (MaybeDistr S P MC) true f = f tt
  u₁ (MaybeDistr S P MC) false f = MC .ι
  u₂ (MaybeDistr S P MC) true f _ = true
  u₂ (MaybeDistr S P MC) false f _ = false
  v₁ (MaybeDistr S P MC) {true} _ x = tt
  v₂ (MaybeDistr S P MC) {true} {f} p x = p
  unit-ιB-shape₁ (MaybeDistr S P MC) true = refl
  unit-ιB-shape₁ (MaybeDistr S P MC) false = refl
  unit-ιB-shape₂ (MaybeDistr S P MC) true = refl
  unit-ιB-shape₂ (MaybeDistr S P MC) false = refl
  unit-ιB-pos₁ (MaybeDistr S P MC) true i q tt = tt
  unit-ιB-pos₂ (MaybeDistr S P MC) true i q tt = q
  unit-ιA-shape₁ (MaybeDistr S P MC) _ = refl
  unit-ιA-shape₂ (MaybeDistr S P MC) _ = refl
  unit-ιA-pos₁ (MaybeDistr S P MC) s i q tt = tt
  unit-ιA-pos₂ (MaybeDistr S P MC) s i q tt = q
  mul-A-shape₁ (MaybeDistr S P MC) true f g = refl
  mul-A-shape₁ (MaybeDistr S P MC) false f g = refl
  mul-A-shape₂ (MaybeDistr S P MC) true f g = refl
  mul-A-shape₂ (MaybeDistr S P MC) false f g = refl
  mul-A-pos₁ (MaybeDistr S P MC) true f g = refl
  mul-A-pos₁ (MaybeDistr {ℓs} {ℓp} S P MC) false f g i q ()
  mul-A-pos₂₁ (MaybeDistr S P MC) true f g = refl
  mul-A-pos₂₁ (MaybeDistr {ℓs} {ℓp} S P MC) false f g i q ()
  mul-A-pos₂₂ (MaybeDistr S P MC) true f g = refl
  mul-A-pos₂₂ (MaybeDistr S P MC) false f g i q ()
  mul-B-shape₁ (MaybeDistr S P MC) true f g = refl
  mul-B-shape₁ (MaybeDistr S P MC) false f g i = unit-r (isMndContainer MC) (MC .ι) (~ i)
  mul-B-shape₂ (MaybeDistr S P MC) true f g = refl
  mul-B-shape₂ (MaybeDistr S P MC) false f g i = λ _ → false
  mul-B-pos₁ (MaybeDistr S P MC) true f g i q tt = tt 
  mul-B-pos₁ (MaybeDistr S P MC) false f g i q ()
  mul-B-pos₂₁ (MaybeDistr S P MC) true f g i q tt = (MC .pr₁) (f tt) (g tt) q
  mul-B-pos₂₁ (MaybeDistr S P MC) false f g i q ()
  mul-B-pos₂₂ (MaybeDistr S P MC) true f g i q tt = (MC .pr₂) (f tt) (g tt) q
  mul-B-pos₂₂ (MaybeDistr S P MC) false f g i q ()

  lemF : ∀ {ℓ ℓ'} {A : Set ℓ} (f g : ⊥* {ℓ'} → A) → f ≡ g
  lemF f g = sym (isContrΠ⊥* .snd f) ∙ isContrΠ⊥* .snd g

  module MaybeDistrUnique {ℓs ℓp} (S : Set ℓs) (P : S → Set ℓp) (MC : MndContainer ℓs ℓp (S ▷ P))
                          (l : MndDistributiveLaw ℓs ℓp 𝟚 JustOrNothing S P MaybeM MC) where

    L₀ = MaybeDistr S P MC

    u1 : (s : 𝟚) (f : JustOrNothing s → S) → u₁ L₀ s f ≡ u₁ l s f
    u1 true f i = hcomp (λ j → λ { (i = i0) → f tt
                                 ; (i = i1) → u₁ l true (λ x → f (⊤-singleton x (~ j)))
                                 }) 
                        (unit-ιA-shape₁ l (f tt) (~ i))
    u1 false f i = hcomp (λ j → λ { (i = i0) → ι MC
                                  ; (i = i1) → u₁ l false (lemF (const (ι MC)) f j) 
                                  })
                         (unit-ιB-shape₁ l false (~ i))

    u2 : (s : 𝟚) (f : JustOrNothing s → S) →
         PathP (λ i → P (u1 s f i) → 𝟚) (u₂ L₀ s f) (u₂ l s f)
    u2 true f i = comp (λ j → P (compPath-filler (λ i' → unit-ιA-shape₁ l (f tt) (~ i')) 
                                                 (λ i' → u₁ l true (λ x → f (⊤-singleton x (~ i')))) j i
                                ) → 𝟚 {ℓs})
                       (λ j → λ { (i = i0) → λ p → true ;
                                  (i = i1) → λ p → u₂ l true (λ x → f (⊤-singleton x (~ j))) p })
                       (λ p → unit-ιA-shape₂ l (f tt) (~ i) p)
    u2 false f = compPathP' {B = (λ x → P x → 𝟚)}
                            {x' = λ x → unit-ιB-shape₂ l false (~ i0) x}
                            {y' = λ p → unit-ιB-shape₂ l false (~ i1) p}
                            {z' = λ p → u₂ l false (lemF (const (ι MC)) f i1) p}
                            (λ i p → unit-ιB-shape₂ l false (~ i) p) 
                            (λ i p → u₂ l false (lemF (const (ι MC)) f i) p)

    v1 : (s : 𝟚) (f : JustOrNothing s → S) →
         PathP (λ i → (p : P (u1 s f i)) → JustOrNothing (u2 s f i p) → JustOrNothing s)
               (λ p q → v₁ L₀ {s} {f} p q) 
               (λ p q → v₁ l {s} {f} p q)
    v1 true f i = comp (λ j → (p : P (compPath-filler (λ k → unit-ιA-shape₁ l (f tt) (~ k)) 
                                                      (λ k → u₁ l true (λ x → f (⊤-singleton x (~ k)))) j i
                                     )) → 
                              JustOrNothing {ℓs} {ℓp} (compPathP'-filler {B = (λ x → P x → 𝟚)}
                                                                         (λ k p' → unit-ιA-shape₂ l (f tt) (~ k) p') 
                                                                         (λ k p' → u₂ l true (λ x → f (⊤-singleton x (~ k))) p') j i p
                                            ) → 
                              ⊤ {ℓp}
                       )
                       (λ j → λ { (i = i0) → λ p q → tt ;
                                  (i = i1) → λ p q → ⊤-singleton (v₁ l p q) (~ j)
                                })
                       (λ p q → tt)
    v1 false f = toPathP (funExt λ p → funExt (λ q → ⊥-rec (subst JustOrNothing (lem p) q)))
      where
        lem : (p : P (u₁ l false f)) → u₂ l false f p ≡ false
        lem p = funExt⁻ (sym (fromPathP (u2 false f))) p

    v2 : (s : 𝟚) (f : JustOrNothing s → S) →
         PathP (λ i → (p : P (u1 s f i)) (q : JustOrNothing (u2 s f i p)) → P (f (v1 s f i p q)))
               (λ p q → v₂ L₀ {s} {f} p q) 
               (λ p q → v₂ l {s} {f} p q)
    v2 true f i =    
        comp (λ j → (p : P (compPath-filler (λ k → unit-ιA-shape₁ l (f tt) (~ k)) 
                                            (λ k → u₁ l true (λ x → f (⊤-singleton x (~ k)))) j i
                           )) → 
                              (q : JustOrNothing {ℓs} {ℓp} (compPathP'-filler {B = (λ x → P x → 𝟚)}
                                                                              (λ k p' → unit-ιA-shape₂ l (f tt) (~ k) p') 
                                                                              (λ k p' → u₂ l true (λ x → f (⊤-singleton x (~ k))) p') j i p
                                                           )) → 
                              P (f (fill (λ k' → (p : P (compPath-filler (λ k → unit-ιA-shape₁ l (f tt) (~ k)) 
                                                                         (λ k → u₁ l true (λ x → f (⊤-singleton x (~ k)))) k' i
                                                        )) → 
                                                 JustOrNothing {ℓs} {ℓp} (compPathP'-filler {B = (λ x → P x → 𝟚)}
                                                                                            (λ k p' → unit-ιA-shape₂ l (f tt) (~ k) p') 
                                                                                            (λ k p' → u₂ l true (λ x → f (⊤-singleton x (~ k))) p') k' i p
                                                                         ) → 
                                                 ⊤ {ℓp}
                                         )
                                         (λ k' → λ { (i = i0) → λ p q → tt
                                                   ; (i = i1) → λ p q → ⊤-singleton (v₁ l p q) (~ k')
                                                   })
                                         (inS (λ p q → tt))
                                         j p q
                                ))
               )
               (λ j → λ { (i = i0) → λ p q → p
                        ; (i = i1) → λ p q → v₂ l {true} {λ x → f (⊤-singleton x (~ j))} p q
                        })
               (λ p q → unit-ιA-pos₂ l (f tt) (~ i) p q)
    
    v2 false f = toPathP (funExt λ p → funExt (λ q → ⊥-rec (subst JustOrNothing (lem p) q)))
      where
        lem : (p : P (u₁ l false f)) → u₂ l false f p ≡ false
        lem p = funExt⁻ (sym (fromPathP (u2 false f))) p


  ReaderDistr : ∀ {ℓs ℓp} (A : Set ℓp) (S : Set ℓs) (P : S → Set ℓp)
    → (MC : MndContainer ℓs ℓp (S ▷ P))
    → MndDistributiveLaw ℓs ℓp S P (⊤ {ℓs}) (const A) MC (ReaderM A)
  u₁ (ReaderDistr A S P MC) s _ = tt
  u₂ (ReaderDistr A S P MC) s _ a = s
  v₁ (ReaderDistr A S P MC) a p = p
  v₂ (ReaderDistr A S P MC) a p = a
  unit-ιB-shape₂ (ReaderDistr A S P MC) s = refl
  unit-ιB-shape₁ (ReaderDistr A S P MC) s = refl
  unit-ιB-pos₁ (ReaderDistr A S P MC) s = refl
  unit-ιB-pos₂ (ReaderDistr A S P MC) s i a p = a
  unit-ιA-shape₂ (ReaderDistr A S P MC) tt = refl
  unit-ιA-shape₁ (ReaderDistr A S P MC) tt = refl
  unit-ιA-pos₁ (ReaderDistr A S P MC) tt = refl
  unit-ιA-pos₂ (ReaderDistr A S P MC) tt = refl
  mul-A-shape₁ (ReaderDistr A S P MC) s f g = refl
  mul-A-shape₂ (ReaderDistr A S P MC) s f g = refl
  mul-A-pos₁ (ReaderDistr A S P MC) s f g = refl
  mul-A-pos₂₁ (ReaderDistr A S P MC) s f g = refl
  mul-A-pos₂₂ (ReaderDistr A S P MC) s f g = refl
  mul-B-shape₁ (ReaderDistr A S P MC) s f g = refl
  mul-B-shape₂ (ReaderDistr A S P MC) s f g = refl
  mul-B-pos₁  (ReaderDistr A S P MC) s f g = refl
  mul-B-pos₂₁ (ReaderDistr A S P MC) s f g = refl
  mul-B-pos₂₂ (ReaderDistr A S P MC) s f g = refl

  module ReaderDistrUnique {ℓs ℓp} (A : Set ℓp) (S : Set ℓs) (P : S → Set ℓp) (MC : MndContainer ℓs ℓp (S ▷ P))
                           (L : MndDistributiveLaw ℓs ℓp S P (⊤ {ℓs}) (const A) MC (ReaderM A)) where

    L₀ = ReaderDistr A S P MC

    lem⊤ : (s : S) (f : P s → ⊤ {ℓs}) → f ≡ const tt
    lem⊤ s f i p = ⊤-singleton (f p) i

    u1 : (s : S) (f : P s → ⊤ {ℓs}) → u₁ L₀ s f ≡ u₁ L s f
    u1 s f i = ⊤-singleton (u₁ L s f) (~ i)

    u2 : (s : S) (f : P s → ⊤ {ℓs}) (a : A) → u₂ L₀ s f a ≡ u₂ L s f a
    u2 s f a i = hcomp (λ j → λ { (i = i0) → s
                                ; (i = i1) → u₂ L s (lem⊤ s f (~ j)) a }) (unit-ιB-shape₂ L s (~ i) a)

    v1 : (s : S) (f : P s → ⊤ {ℓs}) (a : A) →
         PathP (λ i → P (u2 s f a i) → P s)
               (v₁ L₀ {s} {f} a)
               (v₁ L {s} {f} a)
    v1 s f a i p = compPathP' {B = (λ x → P x → P s)} side2 side1 i p
      where
        side1 : PathP (λ i → P (u₂ L s (lem⊤ s f (~ i)) a) → P s)
                      (v₁ L {s} {const tt} a)
                      (v₁ L {s} {f} a)
        side1 i p = v₁ L {s} {lem⊤ s f (~ i)} a p

        side2 : PathP (λ i → P (unit-ιB-shape₂ L s (~ i) a) → P s)
                      (λ p → p)
                      (v₁ L {s} {const tt} a)
        side2 i p = unit-ιB-pos₁ L s (~ i) a p

    v2 : (s : S) (f : P s → ⊤ {ℓs}) (a : A) →
         PathP (λ i → P (u2 s f a i) → A)
               (v₂ L₀ {s} {f} a)
               (v₂ L {s} {f} a)
    v2 s f a i p = compPathP' {B = (λ x → P x → A)} side2 side1 i p
      where
        side1 : PathP (λ i → P (u₂ L s (lem⊤ s f (~ i)) a) → A)
                      (v₂ L {s} {const tt} a)
                      (v₂ L {s} {f} a)
        side1 i p = v₂ L {s} {lem⊤ s f (~ i)} a p

        side2 : PathP (λ i → P (unit-ιB-shape₂ L s (~ i) a) → A)
                      (λ _ → a)
                      (v₂ L {s} {const tt} a)
        side2 i p = unit-ιB-pos₂ L s (~ i) a p
  
  -- An example of a distributive law, this one is not unique for specific S ▷ P
  WriterDistr : ∀ {ℓs ℓp} (A S : Set ℓs) (P : S → Set ℓp) →
                  (mon : Monoid ℓs A) → (MC : MndContainer ℓs ℓp (S ▷ P)) →
                  MndDistributiveLaw ℓs ℓp A (const ⊤) S P (WriterM A mon) MC
  u₁ (WriterDistr A S P mon MC) a s = s tt
  u₂ (WriterDistr A S P mon MC) a s _ = a
  v₁ (WriterDistr A S P mon MC) _ tt = tt
  v₂ (WriterDistr A S P mon MC) p tt = p
  unit-ιB-shape₁ (WriterDistr A S P mon MC) a = refl
  unit-ιB-shape₂ (WriterDistr A S P mon MC) a = refl
  unit-ιB-pos₁ (WriterDistr A S P mon MC) a i p tt = tt
  unit-ιB-pos₂ (WriterDistr A S P mon MC) a i p tt = p
  unit-ιA-shape₁ (WriterDistr A S P mon MC) s = refl
  unit-ιA-shape₂ (WriterDistr A S P mon MC) s = refl
  unit-ιA-pos₁ (WriterDistr A S P mon MC) s i p tt = tt
  unit-ιA-pos₂ (WriterDistr A S P mon MC) s i p tt = p
  mul-A-shape₁ (WriterDistr A S P mon MC) a f g = refl
  mul-A-shape₂ (WriterDistr A S P mon MC) a f g = refl
  mul-A-pos₁ (WriterDistr A S P mon MC) a f g i p tt = tt
  mul-A-pos₂₁ (WriterDistr A S P mon MC) a f g i p tt = tt
  mul-A-pos₂₂ (WriterDistr A S P mon MC) a f g i p tt = p
  mul-B-shape₁ (WriterDistr A S P mon MC) a f g = refl
  mul-B-shape₂ (WriterDistr A S P mon MC) a f g = refl
  mul-B-pos₁ (WriterDistr A S P mon MC) a f g i p tt = tt
  mul-B-pos₂₁ (WriterDistr A S P mon MC) a f g i p tt = pr₁ MC (f tt) (g tt) p
  mul-B-pos₂₂ (WriterDistr A S P mon MC) a f g i p tt = pr₂ MC (f tt) (g tt) p

  module MixedDistributiveLawExamples where

    open import DirectedContainer as DC
    open DC.DirectedContainer
    open import MndDirectedDistributiveLaw as MDDL
    open MDDL.MndDirectedDistributiveLaw
    open import DirectedMndDistributiveLaw
    open ComonadExamples

    WriterCReaderMDistr : ∀ {ℓs ℓp} (A : Set ℓs) (B : Set ℓp) → 
      MndDirectedDistributiveLaw ℓs ℓp A (const (⊤ {ℓp})) (⊤ {ℓs}) (const B) (WriterC A) (ReaderM B)
    u₁ (WriterCReaderMDistr A B) a f = tt
    u₂ (WriterCReaderMDistr A B) a f b = a
    v₁ (WriterCReaderMDistr A B) b tt = tt
    v₂ (WriterCReaderMDistr A B) b tt = b
    unit-oA-shape (WriterCReaderMDistr A B) a f i = ⊤-singleton (f tt) (~ i)
    unit-oA-pos₁ (WriterCReaderMDistr A B) a f i b = tt
    unit-oA-pos₂ (WriterCReaderMDistr A B) a f i b = b
    mul-A-shape₁ (WriterCReaderMDistr A B) a f = refl
    mul-A-shape₂ (WriterCReaderMDistr A B) a f = refl
    mul-A-shape₃ (WriterCReaderMDistr A B) a f i b tt = a
    mul-A-pos₁ (WriterCReaderMDistr A B) s f i b tt tt = tt
    mul-A-pos₂ (WriterCReaderMDistr A B) s f i b tt tt = b
    unit-ιB-shape₁ (WriterCReaderMDistr A B) a = refl
    unit-ιB-shape₂ (WriterCReaderMDistr A B) a = refl
    unit-ιB-pos₁ (WriterCReaderMDistr A B) a i b tt = tt
    unit-ιB-pos₂ (WriterCReaderMDistr A B) a i b tt = b
    mul-B-shape₁ (WriterCReaderMDistr A B) a f g = refl
    mul-B-shape₂ (WriterCReaderMDistr A B) a f g = refl
    mul-B-pos₁ (WriterCReaderMDistr A B) a f g i b tt = tt
    mul-B-pos₂₁ (WriterCReaderMDistr A B) a f g i b tt = b
    mul-B-pos₂₂ (WriterCReaderMDistr A B) a f g i b tt = b
    
    module WriterCReaderMDistrUnique {ℓs ℓp : Level} (A : Set ℓs) (B : Set ℓp)
      (L : MndDirectedDistributiveLaw ℓs ℓp A (const (⊤ {ℓp})) (⊤ {ℓs}) (const B) (WriterC A) (ReaderM B)) where

      L₀ = WriterCReaderMDistr A B

      lem⊤ : (a : A) (f : ⊤ {ℓp} → ⊤ {ℓs}) → f ≡ const tt
      lem⊤ a f i p = ⊤-singleton (f p) i

      u1 : (a : A) (f : ⊤ {ℓp} → ⊤ {ℓs}) → u₁ L₀ a f ≡ u₁ L a f
      u1 a f i = ⊤-singleton (u₁ L a f) (~ i)

      u2 : (a : A) (f : ⊤ {ℓp} → ⊤ {ℓs}) (b : B) → u₂ L₀ a f b ≡ u₂ L a f b
      u2 a f b i = hcomp (λ j → λ { (i = i0) → a
                                  ; (i = i1) → u₂ L a (lem⊤ a f (~ j)) b }) (unit-ιB-shape₂ L a (~ i) b)

      v1 : (a : A) (f : ⊤ {ℓp} → ⊤ {ℓs}) (b : B) (x : ⊤ {ℓp}) → v₁ L₀ {a} {f} b x ≡ v₁ L {a} {f} b x
      v1 a f b tt i = hcomp (λ j → λ { (i = i0) → tt
                                     ; (i = i1) → v₁ L {a} {lem⊤ a f (~ j)} b tt }) (unit-ιB-pos₁ L a (~ i) b tt)

      v2 : (a : A) (f : ⊤ {ℓp} → ⊤ {ℓs}) (b : B) (x : ⊤ {ℓp}) → v₂ L₀ {a} {f} b x ≡ v₂ L {a} {f} b x
      v2 a f b tt i = hcomp (λ j → λ { (i = i0) → b
                                     ; (i = i1) → v₂ L {a} {lem⊤ a f (~ j)} b tt }) (unit-ιB-pos₂ L a (~ i) b tt)

    record MonoidFuncAction {ℓa ℓb : Level} (A : Set ℓa) (B : Set ℓb)
                       (monA : Monoid ℓa A) (monB : Monoid ℓb B) :
                       Set (lsuc (ℓa ⊔ ℓb)) where
      open Monoid monA renaming (e to eᴬ ; _⊕_ to _⊕ᴬ_)
      open Monoid monB renaming (e to eᴮ ; _⊕_ to _⊕ᴮ_)
      field
        χ : (A → B) → A → A
        eᴬ-pres : (f : A → B) → χ f eᴬ ≡ eᴬ
        ⊕ᴬ-pres : (f : A → B) (a a' : A) →
                 χ f (a ⊕ᴬ a') ≡ χ f a ⊕ᴬ χ (λ x → f (χ f a ⊕ᴬ x)) a' 
        eᴮ-pres : (a : A) → χ (const eᴮ) a ≡ a
        ⊕ᴮ-pres : (f g : A → B) (a : A) → χ (λ x → f x ⊕ᴮ g x) a ≡ χ f (χ (λ x → g (χ f x)) a)
    open MonoidFuncAction
    open Monoid

    ReaderCWriterMDistr : ∀ {ℓs ℓp} (A : Set ℓp) (B : Set ℓs) →
                            (monA : Monoid ℓp A) (monB : Monoid ℓs B) → 
                            (t : MonoidFuncAction A B monA monB) →
                            MndDirectedDistributiveLaw ℓs ℓp ⊤ (const A) B (const ⊤) (ReaderC A monA) (WriterM B monB)
    u₁ (ReaderCWriterMDistr {ℓs} {ℓp} A B monA monB t) tt f = f (o (ReaderC {ℓs} {ℓp} A monA) tt) 
    u₂ (ReaderCWriterMDistr A B monA monB t) tt f tt = tt
    v₁ (ReaderCWriterMDistr A B monA monB t) {tt} {f} tt a = χ t f a
    v₂ (ReaderCWriterMDistr A B monA monB t) {tt} {f} tt a = tt
    unit-oA-shape (ReaderCWriterMDistr A B monA monB t) tt f = refl
    unit-oA-pos₁ (ReaderCWriterMDistr A B monA monB t) tt f i tt = eᴬ-pres t f i
    unit-oA-pos₂ (ReaderCWriterMDistr A B monA monB t) tt f i tt = tt
    mul-A-shape₁ (ReaderCWriterMDistr A B monA monB t) tt f i = f (⊕-unit-l monA (e monA) (~ i))
    mul-A-shape₂ (ReaderCWriterMDistr A B monA monB t) tt f i tt = tt
    mul-A-shape₃ (ReaderCWriterMDistr A B monA monB t) tt f i tt a = tt
    mul-A-pos₁ (ReaderCWriterMDistr A B monA monB t) tt f i tt a a' = (⊕ᴬ-pres t f a a' ∙ sym lem) i
      where
        lem : (monA ⊕ χ t (λ p → f ((monA ⊕ p) (e monA))) a) (χ t (λ p' → f ((monA ⊕ χ t (λ p → f ((monA ⊕ p) (e monA))) a) p')) a')
              ≡ (monA ⊕ χ t f a) (χ t (λ x → f ((monA ⊕ χ t f a) x)) a')
        lem i = (monA ⊕ χ t (λ p → f (⊕-unit-r monA p i)) a) (χ t (λ x → f ((monA ⊕ χ t (λ p → f (⊕-unit-r monA p i)) a) x)) a')
    mul-A-pos₂ (ReaderCWriterMDistr A B monA monB t) tt f i tt a a' = tt
    unit-ιB-shape₁ (ReaderCWriterMDistr A B monA monB t) tt = refl
    unit-ιB-shape₂ (ReaderCWriterMDistr A B monA monB t) tt i tt = tt
    unit-ιB-pos₁ (ReaderCWriterMDistr A B monA monB t) tt i tt a = eᴮ-pres t a i
    unit-ιB-pos₂ (ReaderCWriterMDistr A B monA monB t) tt i tt a = tt
    mul-B-shape₁ (ReaderCWriterMDistr A B monA monB t) tt f g i = (monB ⊕ f (e monA)) (g (eᴬ-pres t f (~ i)) tt)
    mul-B-shape₂ (ReaderCWriterMDistr A B monA monB t) tt f g i tt = tt
    mul-B-pos₁ (ReaderCWriterMDistr A B monA monB t) tt f g i tt a = ⊕ᴮ-pres t f (λ x → g x tt) a i
    mul-B-pos₂₁ (ReaderCWriterMDistr A B monA monB t) tt f g i tt a = tt
    mul-B-pos₂₂ (ReaderCWriterMDistr A B monA monB t) tt f g i tt a = tt

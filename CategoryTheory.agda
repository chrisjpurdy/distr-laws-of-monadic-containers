{-# OPTIONS --cubical #-}

open import Level renaming (suc to lsuc)
open import Function
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation

record Functor (ℓ ℓ' : Level) : Set (lsuc (ℓ ⊔ ℓ')) where
  field
    F-obj : Set ℓ → Set ℓ'
    F-mor : {X Y : Set ℓ} → (X → Y) → F-obj X → F-obj Y
    F-id : (X : Set ℓ) → F-mor (id {A = X}) ≡ id {A = F-obj X}
    F-comp : {X Y Z : Set ℓ} (g : Y → Z) (f : X → Y) → F-mor (g ∘ f) ≡ F-mor g ∘ F-mor f
open Functor

Idᶠ : (ℓ : Level) → Functor ℓ ℓ
F-obj (Idᶠ ℓ) X = X
F-mor (Idᶠ ℓ) f = f
F-id (Idᶠ ℓ) X = refl
F-comp (Idᶠ ℓ) g f = refl

_∘ᶠ_ : {ℓ ℓ' ℓ'' : Level} → Functor ℓ' ℓ'' → Functor ℓ ℓ' → Functor ℓ ℓ''
F-obj (G ∘ᶠ F) X = F-obj G (F-obj F X)
F-mor (G ∘ᶠ F) f = F-mor G (F-mor F f)
F-id (G ∘ᶠ F) X = cong (F-mor G) (F-id F X) ∙ (F-id G (F-obj F X))
F-comp (G ∘ᶠ F) g f = cong (F-mor G) (F-comp F g f) ∙ (F-comp G (F-mor F g) (F-mor F f))

record _⇒_ {ℓ ℓ' : Level} (F G : Functor ℓ ℓ') : Set (lsuc (ℓ ⊔ ℓ')) where
  open Functor F renaming (F-obj to F₀ ; F-mor to F₁)
  open Functor G renaming (F-obj to G₀ ; F-mor to G₁)
  field
    α : (X : Set ℓ) → F₀ X → G₀ X
    nat : (X Y : Set ℓ) (f : X → Y) → ∥ (α Y ∘ F₁ f ≡ G₁ f ∘ α X) ∥₁
open _⇒_

Idⁿ : {ℓ ℓ' : Level} (F : Functor ℓ ℓ') → F ⇒ F
α (Idⁿ F) X x = x
nat (Idⁿ F) X Y f = ∣ refl ∣₁

_∘ⁿ_ : {ℓ ℓ' : Level} {H G F : Functor ℓ ℓ'}
     → G ⇒ H → F ⇒ G → F ⇒ H
α   (β ∘ⁿ γ) X = α β X ∘ α γ X
nat (β ∘ⁿ γ) X Y f = rec2 isPropPropTrunc (λ nγ nβ → ∣ cong (α β Y ∘_) nγ ∙ cong (_∘ α γ X) nβ ∣₁) (nat γ X Y f) (nat β X Y f)

_∙ⁿ_ : {ℓ ℓ' ℓ'' : Level} {G G' : Functor ℓ' ℓ''} {F F' : Functor ℓ ℓ'}
     → G ⇒ G' → F ⇒ F' → (G ∘ᶠ F) ⇒ (G' ∘ᶠ F')
α (_∙ⁿ_ {_} {_} {_} {G} {G'} {F} {F'} β γ) X = F-mor G' (α γ X) ∘ α β (F-obj F X)
nat (_∙ⁿ_ {_} {_} {_} {G} {G'} {F} {F'} β γ) X Y f = rec2 isPropPropTrunc (λ nβ nγ → ∣ cong (F-mor G' (α γ Y) ∘_) nβ 
                                                                         ∙ cong (_∘ α β (F-obj F X)) (sym (F-comp G' (α γ Y) (F-mor F f)) 
                                                                                                      ∙ cong (F-mor G') nγ ∙ F-comp G' (F-mor F' f) (α γ X)
                                                                                 )
                                                                       ∣₁
                                                            ) (nat β (F-obj F X) (F-obj F Y) (F-mor F f)) (nat γ X Y f)

record Monad (ℓ ℓ' : Level) (T : Functor ℓ ℓ) : Set (lsuc (ℓ ⊔ ℓ')) where
  open Functor T renaming (F-obj to T₀ ; F-mor to T₁)
  field  
    η : Idᶠ ℓ ⇒ T
    μ : (T ∘ᶠ T) ⇒ T 
    μ-unit-l : α (μ ∘ⁿ (η ∙ⁿ (Idⁿ T))) ≡ α (Idⁿ T)
    μ-unit-r : α (μ ∘ⁿ ((Idⁿ T) ∙ⁿ η)) ≡ α (Idⁿ T)
    μ-assoc : α (μ ∘ⁿ ((Idⁿ T) ∙ⁿ μ)) ≡ α (μ ∘ⁿ (μ ∙ⁿ (Idⁿ T)))

record _≅ᶠ_ {ℓ ℓ' : Level} (F G : Functor ℓ ℓ') : Set (lsuc (ℓ ⊔ ℓ')) where
  field
    to≅ : F ⇒ G
    from≅ : G ⇒ F
    inv≅-1 : α (from≅ ∘ⁿ to≅) ≡ α (Idⁿ F)
    inv≅-2 : α (to≅ ∘ⁿ from≅) ≡ α (Idⁿ G)

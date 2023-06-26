{-# OPTIONS --safe #-}

module C1-TypeTheory where

open import Agda.Primitive using (_⊔_)
open import Relation.Binary.PropositionalEquality

-- Pi type.
--
-- Normally there is no explicit Pi type in Agda, as a dependent function can
-- be constructed in its type signature. However this chapter uses this
-- definition for demonstration purpose.
Π : ∀ {a b} → (A : Set a) → (B : A → Set b) → Set (a ⊔ b)
Π x y = ∀ (v : x) → y v

-- `id`: the identity function.
id : Π Set (λ A → (A → A))
id A = λ a → a

-- `swap` switches the order of the arguments of a two-argument function.
swap : Π Set (λ A → Π Set (λ B → Π Set (λ C → (A → B → C) → (B → A → C))))
swap A B C f = λ b a → f a b

-- Product type.
record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
        pr₁′ : A
        pr₂′ : B
open _×_ public

-- Recursor for A × B.
×-rec : {A B : Set} → Π (Set) (λ C → (A → B → C) → (A × B → C))
×-rec C g = λ (a , b) → g a b

-- Projections defined with recursor.

pr₁ : ∀ {A B} → A × B → A
pr₁ {A} = ×-rec A (λ a b → a)

pr₂ : ∀ {A B} → A × B → B
pr₂ {_} {B} = ×-rec B (λ a b → b)

-- Unit type.
data 𝟙 : Set where
    ⋆ : 𝟙

-- Recursor for 𝟙.
𝟙-rec : Π Set (λ C → C → (𝟙 → C))
𝟙-rec C c = λ _ → c

-- Proposition uniqueness principle.
uppt : ∀ {A B} → Π (A × B) (λ x → (pr₁ x , pr₂ x) ≡ x)
uppt ab = refl

×-ind : ∀ {A B} → Π (A × B → Set) (λ c → Π A (λ a → Π B (λ b → c (a , b))) → Π (A × B) c)
×-ind ab→s f = λ (a , b) → f a b

-- Sigma type.
--record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
--    constructor _,_
--    field
--        pr₁ : A
--        pr₂ : B pr₁
--open Σ public
 
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

-- Sigma type.
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
        pr₁′ : A
        pr₂′ : B pr₁′
open Σ public

-- Product type section.

-- Product type.
_×_ : (A : Set) → (B : Set) → Set
A × B = Σ A (λ _ → B)

-- Recursor for A × B.
×-rec : {A B : Set} → Π (Set) (λ C → (A → B → C) → (A × B → C))
×-rec C g = λ (a , b) → g a b

-- Projections with explicit types.

pr₁ : {A : Set} {B : A → Set} → Σ A B → A
pr₁ (a , b) = a

pr₂ : {A : Set} {B : A → Set} → (p : Σ A B) → B (pr₁ p)
pr₂ (a , b) = b

-- Unit type.
data 𝟙 : Set where
    ⋆ : 𝟙

-- Recursor for unit type.
𝟙-rec : Π Set (λ C → C → (𝟙 → C))
𝟙-rec C c = λ _ → c

-- Proposition uniqueness principle for product type.
uppt : ∀ {A B} → Π (A × B) (λ x → (pr₁ x , pr₂ x) ≡ x)
uppt ab = refl

-- Induction for product type.
×-ind : ∀ {A B} → Π (A × B → Set) (λ c → Π A (λ a → Π B (λ b → c (a , b))) → Π (A × B) c)
×-ind ab→s f = λ (a , b) → f a b

-- Induction for unit type.
𝟙-ind : Π (𝟙 → Set) (λ c → c ⋆ → Π 𝟙 c)
𝟙-ind 𝟙→s c ⋆ = c

-- Propositional unniqueness principle for unit type.
upun : Π 𝟙 (λ x → x ≡ ⋆)
upun ⋆ = refl

-- Dependent pair type section.

-- Recursor for Sigma type.
Σ-rec : {A : Set} {B : A → Set} → Π Set (λ C → Π A (λ x → B x → C) → Σ A B → C)
Σ-rec C g = λ (a , b) → g a b

-- Induction for Sigma type.
Σ-ind : {A : Set} {B : A → Set} → Π (Σ A B → Set) (λ C → (Π A (λ a → Π (B a) (λ b → C (a , b)))) → Π (Σ A B) C)
Σ-ind C f = λ (a , b) → f a b

-- Type-theoretic axiom of choice.
ac : {A B : Set} {R : A → B → Set} → (Π A (λ x → Σ B (R x))) → Σ (A → B) (λ f → Π A (λ x → R x (f x)))
ac {A} {B} {R} f = ((λ x → pr₁ (f x)) , (λ x → pr₂ (f x)))
 
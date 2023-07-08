{-# OPTIONS --without-K --exact-split --safe #-}

-- This isn't really a part of the HoTT book, and is actually quite redundant
-- considering chapter 1 in Foundations. However this chapter focuses on proofs
-- with Martin-Löf type theory's constructs.
--
-- This file also has limited comments. For explanations on MLTT, see C1 in
-- 1-Foundations.
module C1-MartinLöf where

open import Agda.Primitive

variable
    ℓ : Level

data 𝟙 : Set where
    ⋆ : 𝟙

𝟙-induction : ∀ {ℓ} (A : 𝟙 → Set ℓ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : ∀ {ℓ} (B : Set ℓ) → B → (𝟙 → B)
𝟙-recursion B b ⋆ = b

!𝟙 : ∀ {ℓ} {X : Set ℓ} → X → 𝟙
!𝟙 x = ⋆

!𝟙' : ∀ {ℓ} (X : Set ℓ) → X → 𝟙
!𝟙' X x = ⋆

data 𝟘 : Set where

𝟘-induction : ∀ {ℓ} (A : 𝟘 → Set ℓ) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : ∀ {ℓ} (A : Set ℓ) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : ∀ {ℓ} {A : Set ℓ} → 𝟘 → A
!𝟘 {ℓ} {A} = 𝟘-recursion A

is-empty : ∀ {ℓ} → Set ℓ → Set ℓ
is-empty A = A → 𝟘

¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ = is-empty

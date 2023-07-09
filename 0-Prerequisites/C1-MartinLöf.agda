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

data 𝟙 : Set₀ where
    ⋆ : 𝟙

𝟙-induction : ∀ {ℓ} (A : 𝟙 → Set ℓ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : ∀ {ℓ} (B : Set ℓ) → B → (𝟙 → B)
𝟙-recursion B b ⋆ = b

!𝟙 : ∀ {ℓ} {X : Set ℓ} → X → 𝟙
!𝟙 x = ⋆

!𝟙' : ∀ {ℓ} (X : Set ℓ) → X → 𝟙
!𝟙' X x = ⋆

data 𝟘 : Set₀ where

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

data ℕ : Set₀ where
    zero : ℕ
    succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : ∀ {ℓ} (A : ℕ → Set ℓ) → A 0 → ((n : ℕ) → A n → A (succ n)) → ((n : ℕ) → A n)
ℕ-induction A a f zero = a
ℕ-induction A a f (succ n) = f n (ℕ-induction A a f n)

ℕ-recursion : ∀ {ℓ} (A : Set ℓ) → A → (ℕ → A → A) → (ℕ → A)
ℕ-recursion A = ℕ-induction (λ _ → A)

ℕ-iteration : ∀ {ℓ} (A : Set ℓ) → A → (A → A) → ℕ → A
ℕ-iteration A a₁ f = ℕ-recursion A a₁ (λ _ a₂ → f a₂)

_+_ _*_ : ℕ → ℕ → ℕ
_+_ x = ℕ-iteration ℕ x succ
_*_ x = ℕ-iteration ℕ 0 (x +_)

infixl 20 _+_
infixl 21 _*_

_≤_ _≥_ : ℕ → ℕ → Set₀

0 ≤ y = 𝟙
succ x ≤ 0 = 𝟘
succ x ≤ succ y = x ≤ y

x ≥ 0 = 𝟙
0 ≥ succ y = 𝟘
succ x ≥ succ y = x ≥ y

infix 10 _≤_
infix 10 _≥_

data _⨃_ {ℓ₁ ℓ₂} (X : Set ℓ₁) (Y : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    inl : X → X ⨃ Y
    inr : Y → X ⨃ Y

⨃-induction : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : Set ℓ₂} (A : X ⨃ Y → Set ℓ₃)
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → ((z : X ⨃ Y) → A z)
⨃-induction A f g (inl x) = f x
⨃-induction A f g (inr y) = g y

⨃-recursion : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : Set ℓ₂} {A : Set ℓ₃}
            → (X → A) → (Y → A) → (X ⨃ Y → A)
⨃-recursion {A = A} = ⨃-induction (λ _ → A)

𝟚 : Set₀
𝟚 = 𝟙 ⨃ 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : ∀ {ℓ} (A : 𝟚 → Set ℓ) → A ₀ → A ₁ → ((n : 𝟚) → A n)
𝟚-induction A a₀ a₁ (inl ⋆) = a₀
𝟚-induction A a₀ a₁ (inr ⋆) = a₁

𝟚-induction' : ∀ {ℓ} (A : 𝟚 → Set ℓ) → A ₀ → A ₁ → ((n : 𝟚) → A n)
𝟚-induction' A a₀ a₁ =
    ⨃-induction A
    (𝟙-induction (λ x → A (inl x)) a₀)
    (𝟙-induction (λ x → A (inr x)) a₁)

record Σ {ℓ₁ ℓ₂} (X : Set ℓ₁) (Y : X → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    field
        fst : X
        snd : Y fst
open Σ public

Σ-induction : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : X → Set ℓ₂} {A : Σ X Y → Set ℓ₃}
            → ((x : X) (y : Y x) → A (x , y))
            → ((s : Σ X Y) → A s)
Σ-induction f (x , y) = f x y

curry : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : X → Set ℓ₂} {A : Σ X Y → Set ℓ₃}
      → ((s : Σ X Y) → A s)
      → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)

_×_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
X × Y = Σ X (λ _ → Y)



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

id : ∀ {ℓ} {X : Set ℓ} → X → X
id x = x

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : Set ℓ₁} {Y : Set ℓ₂} {Z : Y → Set ℓ₃}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → ((x : X) → Z (f x))
(f ∘ g) x = f (g x)

data Id {ℓ} (X : Set ℓ) : X → X → Set ℓ where
    refl : (x : X) → Id X x x

_≡_ : ∀ {ℓ} {X : Set ℓ} → X → X → Set ℓ
x ≡ y = Id _ x y

infix 4 _≡_

J : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (A : (x y : X) → x ≡ y → Set ℓ₂)
  → ((x : X) → A x x (refl x))
  → ((x y : X) (p : x ≡ y) → A x y p)
J A f x x (refl x) = f x

H : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (x : X) (B : (y : X) → x ≡ y → Set ℓ₂)
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p
H x B b y (refl x) = b

J' : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (A : (x y : X) → x ≡ y → Set ℓ₂)
  → ((x : X) → A x x (refl x))
  → ((x y : X) (p : x ≡ y) → A x y p)
J' A f x = H x (A x) (f x)

Js-agreement : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (A : (x y : X) → x ≡ y → Set ℓ₂)
             → (f : (x : X) → A x x (refl x))
             → (x y : X) → (p : x ≡ y)
             → J A f x y p ≡ J' A f x y p
Js-agreement A f x y (refl x) = refl (f x)

transport : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (A : X → Set ℓ₂) {x y : X}
          → x ≡ y
          → (A x → A y)
transport A (refl x) a = a

transport-J : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (A : X → Set ℓ₂) {x y : X}
            → x ≡ y
            → (A x → A y)
transport-J A {x} {y} = J (λ x y p → A x → A y) (λ _ → id) x y

nondep-H : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (x : X) (A : X → Set ℓ₂)
         → A x
         → ((y : X) → x ≡ y → A y)
nondep-H x A = H x (λ y p → A y)

transport-H : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (A : X → Set ℓ₂) {x y : X}
            → x ≡ y
            → (A x → A y)
transport-H A {x} {y} p a = nondep-H x A a y p

transports-agreement : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (A : X → Set ℓ₂) {x y : X} (p : x ≡ y)
                     → (transport-H A p ≡ transport A p)
                     × (transport-J A p ≡ transport A p)
transports-agreement A (refl x) = refl (transport A (refl x))
                                , refl (transport A (refl x))

lhs : ∀ {ℓ} {X : Set ℓ} {x y : X} → x ≡ y → X
lhs {x = x} p = x

rhs : ∀ {ℓ} {X : Set ℓ} {x y : X} → x ≡ y → X
rhs {y = y} p = y

_∙_ : ∀ {ℓ} {X : Set ℓ} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q = transport (x ≡_) q p

_≡⟨_⟩_ : ∀ {ℓ} {X : Set ℓ} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

_∎ : ∀ {ℓ} {X : Set ℓ} (x : X) → x ≡ x
x ∎ = refl x

_⁻¹ : ∀ {ℓ} {X : Set ℓ} {x y : X} → x ≡ y → y ≡ x
_⁻¹ {x = x} p = transport (_≡ x) p (refl x)

_∙'_ : ∀ {ℓ} {X : Set ℓ} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
_∙'_ {z = z} p q = transport (_≡ z) (p ⁻¹) q

∙-agreement : ∀ {ℓ} {X : Set ℓ} {x y z : X} → (p : x ≡ y) → (q : y ≡ z)
            → p ∙ q ≡ p ∙' q
∙-agreement (refl x) (refl x) = refl (refl x)

rdnel : ∀ {ℓ} {X : Set ℓ} {x y : X} (p : x ≡ y) → p ∙ refl y ≡ p
rdnel p = refl p

rdner : ∀ {ℓ} {X : Set ℓ} {y z : X} (q : y ≡ z) → refl y ∙' q ≡ q
rdner q = refl q

ap : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {Y : Set ℓ₂} (f : X → Y) {x₁ x₂ : X}
   → x₁ ≡ x₂ → f x₁ ≡ f x₂
ap f (refl x) = refl (f x)

_~_ : ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {A : X → Set ℓ₂}
    → ((x : X) → A x) → ((x : X) → A x)
    → Set (ℓ₁ ⊔ ℓ₂)
f ~ g  = ∀ x → f x ≡ g x

¬¬ ¬¬¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬¬ A = ¬ (¬ A)
¬¬¬ A = ¬ (¬¬ A)

dni : ∀ {ℓ} (A : Set ℓ) → A → ¬¬ A
dni A a u = u a

contrapositive : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → (¬ B → ¬ A)
contrapositive f ¬b a = ¬b (f a)

tno : ∀ {ℓ} (A : Set ℓ) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

_⇔_ : ∀ {ℓ₁ ℓ₂} → (A : Set ℓ₁) → (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A ⇔ B = (A → B) × (B → A)

lr-implication : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → {B : Set ℓ₂} → A ⇔ B → (A → B)
lr-implication = fst

rl-implication : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → {B : Set ℓ₂} → A ⇔ B → (B → A)
rl-implication = snd

absurdity³-is-absurdity : ∀ {ℓ} {A : Set ℓ} → ¬¬¬ A ⇔ ¬ A
absurdity³-is-absurdity {A = A} = tno A , dni (¬ A)

_≢_ : ∀ {ℓ} {X : Set ℓ} → X → X → Set ℓ
x ≢ y = ¬ (x ≡ y)

≢-sym : ∀ {ℓ} {X : Set ℓ} {x y : X} → x ≢ y → y ≢ x
≢-sym x≢y x≡y = x≢y (x≡y ⁻¹)

Id→Fun : ∀ {ℓ} {X Y : Set ℓ} → X ≡ Y → (X → Y)
Id→Fun = transport id

Id→Fun' : ∀ {ℓ} {X Y : Set ℓ} → X ≡ Y → (X → Y)
Id→Fun' (refl X) = id

Id→Funs-agree : ∀ {ℓ} {X Y : Set ℓ} → (p : X ≡ Y) → Id→Fun p ≡ Id→Fun' p
Id→Funs-agree (refl X) = refl id

𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 𝟙≡𝟘 = Id→Fun 𝟙≡𝟘 ⋆

₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ ₁≢₀ = 𝟙-is-not-𝟘 (ap f ₁≢₀)
    where
        f : 𝟚 → Set₀
        f ₀ = 𝟘
        f ₁ = 𝟙

decidable : ∀ {ℓ} → Set ℓ → Set ℓ
decidable A = A ⨃ ¬ A

has-decidable-equality : ∀ {ℓ} → Set ℓ → Set ℓ
has-decidable-equality X = (x y : X) → decidable (x ≡ y)

𝟚-has-decidable-equality : has-decidable-equality 𝟚
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ n≢₀ = !𝟘 (n≢₀ (refl ₀))
not-zero-is-one ₁ n≢₀ = refl ₁


 
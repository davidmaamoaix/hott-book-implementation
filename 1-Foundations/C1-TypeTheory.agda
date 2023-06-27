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

-- The coproduct type.
data _+_ (A B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

-- Recursor for coproduct type.
+-rec : {A B : Set} → Π Set (λ C → (A → C) → (B → C) → (A + B → C))
+-rec C f₁ f₂ (inl a) = f₁ a
+-rec C f₁ f₂ (inr b) = f₂ b

-- Induction for coproduct type.
+-ind : {A B : Set} → Π (A + B → Set) (λ C → (Π A (λ a → C (inl a))) → (Π B (λ b → C (inr b))) → Π (A + B) C)
+-ind C f₁ f₂ (inl a) = f₁ a
+-ind C f₁ f₂ (inr b) = f₂ b

-- The empty type.
data 𝟘 : Set where

-- Recursor for empty type.
𝟘-rec : Π Set (λ C → 𝟘 → C)
𝟘-rec C ()

-- Induction for empty type.
𝟘-ind : Π (𝟘 → Set) (λ C → Π 𝟘 C)
𝟘-ind f ()

-- The boolean type.
-- ngl i hate using single character as type name
data 𝟚 : Set where
    0₂ : 𝟚
    1₂ : 𝟚

-- Recursor for boolean type.
𝟚-rec : ∀ {a} → Π (Set a) (λ C → C → C → 𝟚 → C)
𝟚-rec C a b 0₂ = a
𝟚-rec C a b 1₂ = b

-- Induction for boolean type.
𝟚-ind : ∀ {a} → Π (𝟚 → Set a) (λ C → C 0₂ → C 1₂ → Π 𝟚 C)
𝟚-ind C f₁ f₂ 0₂ = f₁
𝟚-ind C f₁ f₂ 1₂ = f₂

-- Alternative definition of coproduct with recursor for boolean type.

_+′_ : ∀ {l} → (A B : Set l) → Set l
_+′_ {l} A B = Σ 𝟚 (𝟚-rec (Set l) A B)

+′-inl : ∀ {l} {A B : Set l} → A → A +′ B
+′-inl a = (0₂ , a)

+′-inr : ∀ {l} {A B : Set l} → B → A +′ B
+′-inr b = (1₂ , b)

-- Alternative definition of product with recursor for boolean type.

_×′_ : ∀ {l} → (A B : Set l) → Set l
_×′_ {l} A B = Π 𝟚 (𝟚-rec (Set l) A B)

×′-pr₁ : ∀ {l} {A B : Set l} → A ×′ B → A
×′-pr₁ f = f 0₂

×′-pr₂ : ∀ {l} {A B : Set l} → A ×′ B → B
×′-pr₂ f = f 1₂

-- Natural numbers.
data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

-- Doubles a number.
double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

-- Adds two numbers.
_++_ : ℕ → ℕ → ℕ
_++_ zero n = n
_++_ (succ m) n = succ (m ++ n)

-- Recursor for natural numbers.
ℕ-rec : Π Set (λ C → C → (ℕ → C → C) → ℕ → C)
ℕ-rec C c₀ cₛ zero = c₀
ℕ-rec C c₀ cₛ (succ n) = cₛ n (ℕ-rec C c₀ cₛ n)

-- Induction for natural numbers.
ℕ-ind : Π (ℕ → Set) (λ C → C zero → (Π ℕ (λ n → C n → C (succ n))) → Π ℕ C)
ℕ-ind C c₀ cₛ zero = c₀
ℕ-ind C c₀ cₛ (succ n) = cₛ n (ℕ-ind C c₀ cₛ n)

-- Alternative definitions for arithmetics with recursors.

double′ : ℕ → ℕ
double′ = ℕ-rec ℕ zero (λ _ f → succ (succ f))

++′ : ℕ → ℕ → ℕ
++′ = ℕ-rec (ℕ → ℕ) (λ n → n) (λ _ g m → succ (g m))

-- Association rule for natural number addition.

ap-succ : Π ℕ (λ m → Π ℕ (λ n → m ≡ n → succ m ≡ succ n))
ap-succ m n refl = refl

goal : ℕ → Set
goal i = Π ℕ (λ j → Π ℕ (λ k → i ++ (j ++ k) ≡ (i ++ j) ++ k))

assoc₀ : Π ℕ (λ j → Π ℕ (λ k → zero ++ (j ++ k) ≡ (zero ++ j) ++ k))
assoc₀ j k = refl

assocₛ : Π ℕ (λ i → (Π ℕ (λ j → Π ℕ (λ k → i ++ (j ++ k) ≡ (i ++ j) ++ k))) → Π ℕ (λ j → Π ℕ (λ k → succ i ++ (j ++ k) ≡ (succ i ++ j) ++ k)))
assocₛ i h j k = ap-succ (i ++ (j ++ k)) ((i ++ j) ++ k) (h j k)

assoc : Π ℕ (λ i → Π ℕ (λ j → Π ℕ (λ k → i ++ (j ++ k) ≡ (i ++ j) ++ k)))
assoc = ℕ-ind goal assoc₀ assocₛ

-- Path induction.
p-ind : {A : Set} → Π (Π A (λ x → Π A (λ y → (x ≡ y) → Set))) (λ C → (Π A (λ x → C x x refl)) → Π A (λ x → Π A (λ y → Π (x ≡ y) (λ p → C x y p))))
p-ind C c a b refl = c a

-- Based path induction.
p-ind′ : {A : Set} → Π A (λ a → Π (Π A (λ x → a ≡ x → Set)) (λ C → C a refl → Π A (λ x → Π (a ≡ x) (λ p → C x p))))
p-ind′ a C c b refl = c

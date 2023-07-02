{-# OPTIONS --safe --cubical #-}

module C2-HomotopyTypeTheory where

open import Data.Product
open import Data.Nat
open import Agda.Primitive using (Level; lsuc)
open import Cubical.Foundations.Prelude using
    (_≡_; refl; J; JRefl; cong; _≡⟨⟩_; step-≡; _∎)

private
    variable
        u : Level
        A B : Set u
        w x y z : A

-- Identity function.
id : x → x
id x = x

-- Lemma 2.1.1: Symmetry of path.

sym : x ≡ y → y ≡ x
sym {x = x} = J (λ y₁ p → y₁ ≡ x) refl

symRefl : sym {x = x} refl ≡ refl
symRefl {x = x} = JRefl (λ y₁ p → y₁ ≡ x) refl

-- Lemma 2.1.2: Transitivity of path.

_∙_ : x ≡ y → y ≡ z → x ≡ z
_∙_ {u} {A} {x} {y} {z} = J (λ y₁ p → y₁ ≡ z → x ≡ z) id

infixr 30 _∙_

∙-refl : {x y : A} → (_∙_ {u} {A} {x} {x} {y}) refl ≡ λ q → q
∙-refl {x = x} = JRefl (λ y₁ p → x ≡ y₁ → x ≡ y₁) id

refl∙refl : refl {x = x} ∙ refl ≡ refl
refl∙refl = cong (λ f → f refl) ∙-refl

-- Lemma 2.1.4: Higher Groupoid Structure.

-- (i)

∙refl : (p : x ≡ y) → p ∙ refl ≡ p
∙refl = J (λ y₁ p → (p ∙ refl) ≡ p) (cong (λ p → p refl) ∙-refl)

refl∙ : (p : x ≡ y) → refl ∙ p ≡ p
refl∙ = J (λ y₁ p → (refl ∙ p) ≡ p) (cong (λ p → p refl) ∙-refl)

-- (ii)

∙sym : (p : x ≡ y) → p ∙ sym p ≡ refl
∙sym = J (λ y₁ p → p ∙ sym p ≡ refl)
    (
        refl ∙ sym refl
    ≡⟨ cong (λ p → refl ∙ p) symRefl ⟩
        refl ∙ refl
    ≡⟨ refl∙refl ⟩
        refl
    ∎
    )

sym∙ : (p : x ≡ y) → sym p ∙ p ≡ refl
sym∙ = J (λ y₁ p → sym p ∙ p ≡ refl)
    (
        sym refl ∙ refl
    ≡⟨ cong (λ p → p ∙ refl) symRefl ⟩
        refl ∙ refl
    ≡⟨ refl∙refl ⟩
        refl
    )

-- (iii)

symsym : (p : x ≡ y) → sym (sym p) ≡ p
symsym = J (λ y₁ p → sym (sym p) ≡ p)
    (
        sym (sym refl)
    ≡⟨ cong sym symRefl ⟩
        sym refl
    ≡⟨ symRefl ⟩
        refl
    ∎
    )

-- (iv)

assoc : (p : w ≡ x) → (q : x ≡ y) → (r : y ≡ z) → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc {y = y} {z = z} = J
    (λ x₁ p → (q : x₁ ≡ y) → (r : y ≡ z) → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r)
    (λ q r →
        refl ∙ q ∙ r
    ≡⟨ cong (λ f → f (q ∙ r)) ∙-refl ⟩
        q ∙ r
    ≡⟨ sym (cong (λ o → o ∙ r) (refl∙ q)) ⟩
        (refl ∙ q) ∙ r
    ∎
    )


-- Theorem 2.1.6.

_∙ᵣ_ : {p q : x ≡ y} (α : p ≡ q) → (r : y ≡ z) → p ∙ r ≡ q ∙ r
_∙ᵣ_ {p = p} {q = q} α = J (λ z r → p ∙ r ≡ q ∙ r) (cong (λ p → p ∙ refl) α)

_∙ₗ_ : (r : x ≡ y) → {p q : y ≡ z} (β : p ≡ q) → r ∙ p ≡ r ∙ q
_∙ₗ_ r {p} {q} = J (λ q β → r ∙ p ≡ r ∙ q) refl

_⋆_ : {p q : x ≡ y} (α : p ≡ q) → {r s : y ≡ z} (β : r ≡ s) → p ∙ r ≡ q ∙ s
_⋆_ {q = q} α {r = r} β = (α ∙ᵣ r) ∙ (q ∙ₗ β)

-- TODO: Eckmann-Hilton argument.

-- Loop space of a pointed type.
Ω : Σ Set id → Σ Set id
Ω (A , a) = ((a ≡ a) , refl)

-- Iterated loop space.
Ωⁿ : ℕ → Σ Set id → Σ Set id
Ωⁿ zero tup = tup
Ωⁿ (suc n) tup = Ωⁿ n (Ω tup)



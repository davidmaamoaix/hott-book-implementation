{-# OPTIONS --safe --cubical #-}

module C2-HomotopyTypeTheory where

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

-- Lemma 2.1.4

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
 
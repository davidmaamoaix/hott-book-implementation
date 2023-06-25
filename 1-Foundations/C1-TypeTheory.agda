{-# OPTIONS --safe #-}

module C1-TypeTheory where

open import Agda.Primitive using (_⊔_)
open import Data.Nat hiding (_⊔_)

-- pi type
Π : ∀ {a b} → (A : Set a) → (B : A → Set b) → Set (a ⊔ b)
Π x y = ∀ (v : x) → y v

-- `id`: the identity function
id : Π Set (λ A → A → A)
id A a = a

-- `swap` switches the order of the arguments of a two-argument function
swap : Π Set (λ A → Π Set (λ B → Π Set (λ C → (A → B → C) → (B → A → C))))
swap A B C f b a = f a b

-- sigma type
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
        pr₁ : A
        pr₂ : B pr₁
open Σ public

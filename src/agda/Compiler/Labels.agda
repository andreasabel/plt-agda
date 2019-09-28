module Compiler.Labels where

open import Library
open import Compiler.JumpFreeInstructions using (MT)

-- Labels are numbers bounded by the number of available labels.
-- They are like de Bruijn indices.

-- A label represents the code after it,
-- starting in scope Γ.

-- Labels are typed by the Machine state type at label definition point.

LabelType = MT
Labels = List LabelType

-- Kripke structure: a world is a list of labels.
-- A future is an extension of this list.
-- We use more generally sublists (_⊆_).

□ : (F : Labels → Set) → Labels → Set
□ F Λ = ∀ {Λ'} (ρ : Λ ⊆ Λ') → F Λ'

_→̇_ : (F G : Labels → Set) → Labels → Set
F →̇ G = λ Λ → F Λ → G Λ

-- Kripke function space

-- _□→_ : (F G : Labels → Set) → Labels → Set
-- (F □→ G) = □ (F →̇ G)

-- Comonad structure

-- Counit:
-- _ ⊆-refl : ∀{F Λ} (k : □ F Λ) → F Λ

-- Cojoin (duplicate):
_∙_ : ∀{F Λ} (k : □ F Λ) → □ (□ F) Λ
k ∙ ρ = λ ρ' → k (⊆-trans ρ ρ')


module Environment where

open import Library
open import Value
open import WellTypedSyntax

-- Results of evaluating a statement

data Res (t : Type) : Set where
  ret : (v : Val t) → Res t
  cont : Res t

-- Environments.

-- An environment entry can be undefined,
-- but cannot be of type void.

Entry` : Ty → Set
Entry` t = Maybe (Val` t)

-- An environment is a list of frames.

Frame : Block → Set
Frame = List.All Entry`

Env : Cxt → Set
Env = List⁺.All Frame

Entry : Type → Set
Entry void = ⊤
Entry (` t) = Entry` t

push : ∀{t} (v : Entry t) {Γ} (γ : Env Γ) → Env (Γ ▷ t)
push {void} _ γ       = γ
push {` t}  v (δ ∷ γ) = (v ∷ δ) ∷ γ

_▷ᵛ_ : ∀{Γ t} (γ : Env Γ) (v : Val t) → Env (Γ ▷ t)
_▷ᵛ_ {t = ` t } γ v = push (just v) γ
_▷ᵛ_ {t = void} γ v = γ

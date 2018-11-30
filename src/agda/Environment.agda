
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

Entry : Ty → Set
Entry t = Maybe (Val` t)

-- An environment is a list of frames.

Frame : Block → Set
Frame = List.All Entry

Env : Cxt → Set
Env = List⁺.All Frame

push : ∀{t} (v : Entry t) {Γ} (γ : Env Γ) → Env (Γ ▷ just t)
push v (δ ∷ γ) = (v ∷ δ) ∷ γ

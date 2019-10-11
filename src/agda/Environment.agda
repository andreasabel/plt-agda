
module Environment where

open import Library
open import Value public
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

_▷ᵛ_ : ∀{Δ t} (γ : Frame Δ) (v : Val t) → Frame (Δ ▷ᵇ t)
_▷ᵛ_ {t = ` t } γ v = just v ∷ γ
_▷ᵛ_ {t = void} γ v = γ

_▷ᵛˢ_ : ∀{Δ Δ'} (γ : Frame Δ) (vs : Vals Δ') → Frame (Δ' ++ Δ)
γ ▷ᵛˢ vs = List.All.map just vs List.All.++ γ

Env : Cxt → Set
Env = List⁺.All Frame

Entry : Type → Set
Entry void = ⊤
Entry (` t) = Entry` t

push` : ∀{t} (v : Entry` t) {Γ} (γ : Env Γ) → Env (Γ ▷ ` t)
push` v (δ ∷ γ) = (v ∷ δ) ∷ γ

push : ∀{t} (v : Entry t) {Γ} (γ : Env Γ) → Env (Γ ▷ t)
push {void} _ = id
push {` t}  v = push` v

-- _▷ᵛ_ : ∀{Γ t} (γ : Env Γ) (v : Val t) → Env (Γ ▷ t)
-- _▷ᵛ_ {t = ` t } γ v = push (just v) γ
-- _▷ᵛ_ {t = void} γ v = γ

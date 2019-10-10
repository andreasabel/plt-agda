

module Compiler.BB.CompilerCorrectness where

open import Library

open import WellTypedSyntax
open import Evaluation

open import Compiler.JumpFreeInstructions
open import Compiler.JFSemantics
open import Compiler.BasicBlocks
open import Compiler.BB.BBSemantics

module _ {Σ : Sig} {P : Prg Σ Σ} {M : Meths Σ Σ} {rt : Type} {rv : Val rt} where

  open BBTypes Σ rt

    -- compileStm : ∀ {Γ mt Φ}
    --   → Stm Σ rt Γ mt
    --   → CompRes (Γ ▷ mt , Φ)
    --   ⇒ CompRes (Γ , Φ)

  corrExp : ∀ {Γ t} {e : Exp Σ Γ t} {v : Val t} {γ γ' : Env Γ} {Φ} {φ : Frame Φ}
    → P , γ ⊢ e ⇓ᵉ v , γ'
    → ∀ {Λ k ƛ} (let cr = compileExp {rt = rt} e {Λ} k)
    → CREval M ƛ rv k  (γ , φ ▷ᵛ v)
    → CREval M ƛ rv cr (γ , φ)
  corrExp evConst (ev□Block {□bb = □bb} sem) with □bb ⊆-refl
  ... | bb = ev□Block {!rt!}
  corrExp evConst (ev□Goto sem) = ev□Block (evExec (evStackI evConst) (evGoto sem))
  corrExp (evVar x) sem = {!!}
  corrExp (evApp x x₁ x₂ x₃) sem = {!!}
  corrExp (evBuiltin x x₁) sem = {!!}
  corrExp (evOp ev ev₁ x) sem = {!!}
  corrExp (evAss ev x) sem = {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

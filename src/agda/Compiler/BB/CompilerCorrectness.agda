

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

  -- corrE : ∀ {t} {Γ} {x : Var Γ t} {v : Val (` t)} {γ : Env Γ} {Φ}
  --            {φ : Frame Φ} {Λ} {k} {ƛ : LS Σ rt Λ}
  --   → γ ⊢ x ⇓ˣ v
  --   → CREval M ƛ rv k                            (γ , just v ∷ φ)
  --   → CREval M ƛ rv (crExec (storeI (load x)) k) (γ , φ)
  -- corrE evX (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB ({!evStoreI (evLoad evX)!} ∷ᵒ-ev evJF) evCtrl)
  -- corrE evX (ev□Goto  evB               ) = ev□Block (evBB (evStoreI (evLoad evX) ∷ []) (evGoto evB))

    -- compileStm : ∀ {Γ mt Φ}
    --   → Stm Σ rt Γ mt
    --   → CompRes (Γ ▷ mt , Φ)
    --   ⇒ CompRes (Γ , Φ)
  corrEVar : ∀ {t} {Γ} {x : Var Γ t} {v : Val (` t)} {γ : Env Γ} {Φ}
             {φ : Frame Φ} {Λ} {k} {ƛ : LS Σ rt Λ}
    → γ ⊢ x ⇓ˣ v
    → CREval M ƛ rv k                            (γ , just v ∷ φ)
    → CREval M ƛ rv (crExec (storeI (load x)) k) (γ , φ)
  corrEVar evX (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evStoreI (evLoad evX) ∷ᵒ-ev evJF) evCtrl)
  corrEVar evX (ev□Goto  evB               ) = ev□Block (evBB (evStoreI (evLoad evX) ∷ []) (evGoto evB))

  corrArithOp : ∀ {Γ t} {op : ArithOp t} {v v₁ v₂ : Val` t} {γ : Env Γ} {Φ} {φ : Frame Φ} {Λ} {k} {ƛ : LS Σ rt Λ}
    → v₁ ⟨ op ⟩ v₂ ⇓ᵃ v
    → CREval M ƛ rv k (γ , just v ∷ φ)
    → CREval M ƛ rv (crExec (stackI (arith op)) k) (γ , just v₂ ∷ just v₁ ∷ φ)
  corrArithOp evO (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB ((evStackI (evArith evO)) ∷ᵒ-ev evJF) evCtrl)
  corrArithOp evO (ev□Goto ev)                  = ev□Block (evBB ((evStackI (evArith evO)) ∷ []) (evGoto ev))

  corrExp : ∀ {Γ t} {e : Exp Σ Γ t} {v : Val t} {γ γ' : Env Γ} {Φ} {φ : Frame Φ}
    → P , γ ⊢ e ⇓ᵉ v , γ'
    → ∀ {Λ k ƛ} (let cr = compileExp {rt = rt} e {Λ} k)
    → CREval M ƛ rv k  (γ' , φ ▷ᵛ v)
    → CREval M ƛ rv cr (γ , φ)

  corrExp evConst     (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evStackI evConst ∷ᵒ-ev evJF) evCtrl)
  corrExp evConst     (ev□Goto ev                 ) = ev□Block (evBB (evStackI evConst ∷ []) (evGoto ev))
  corrExp (evVar evX) (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evStoreI (evLoad evX) ∷ᵒ-ev evJF) evCtrl)
  corrExp (evVar evX) (ev□Goto ev                 ) = ev□Block (evBB (evStoreI (evLoad evX) ∷ []) (evGoto ev))
  corrExp (evVar evX) sem = {!corrEVar evX sem!}
  corrExp (evApp evF evEs evBody evRt) sem = {!!}
  corrExp (evBuiltin evEs evBu) (ev□Block (evBB evJF evCtrl)) = {!!}
  corrExp (evBuiltin evEs evBu) (ev□Goto ev) = {!ev□Block (evBB (? ∷ []) (evGoto ev))!}
  corrExp (evOp evE₁ evE₂ (evArith evO)) sem = corrExp evE₁ (corrExp evE₂ (corrArithOp evO sem))
  corrExp (evOp evE₁ evE₂ (evCmp   evO)) sem = {!!}
  corrExp (evOp evE₁ evE₂ (evLogic evO)) sem = {!!}
  corrExp (evAss ev x) sem = {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

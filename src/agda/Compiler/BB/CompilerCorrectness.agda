

module Compiler.BB.CompilerCorrectness where

open import Library

open import WellTypedSyntax
open import Evaluation

open import Compiler.JumpFreeInstructions
open import Compiler.JFSemantics
open import Compiler.BasicBlocks
open import Compiler.BB.BBSemantics

corrReturnVal : ∀ (rt : Type) {rv v : Val rt} {Φ} {φ : Frame Φ}
  → ResVal rt (ret v) rv
  → ReturnVal rt rv (φ ▷ᵛ v)
corrReturnVal (` t) ret = refl
corrReturnVal void  ret = _

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

  mutual

    corrExps : ∀ {Γ Δ} {es : Exps Σ Γ Δ} {vs : Vals Δ} {γ γ' : Env Γ} {Φ} {φ : Frame Φ}
      → P , γ ⊢ es ⇓ᵉˢ vs , γ'
      → ∀ {Λ k ƛ} (let cr = compileExps {rt = rt} es {Λ} k)
      → CREval M ƛ rv k  (γ' , φ ▷ᵛˢ vs)
      → CREval M ƛ rv cr (γ , φ)
    corrExps evNil             = id
    corrExps (evSnoc evEs evE) = corrExps evEs ∘ corrExp evE

    corrExp : ∀ {Γ t} {e : Exp Σ Γ t} {v : Val t} {γ γ' : Env Γ} {Φ} {φ : Frame Φ}
      → P , γ ⊢ e ⇓ᵉ v , γ'
      → ∀ {Λ k ƛ} (let cr = compileExp {rt = rt} e {Λ} k)
      → CREval M ƛ rv k  (γ' , φ ▷ᵛ v)
      → CREval M ƛ rv cr (γ , φ)

    corrExp evConst     (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evStackI evConst ∷ᵒ-ev evJF) evCtrl)
    corrExp evConst     (ev□Goto ev                 ) = ev□Block (evBB (evStackI evConst ∷ []) (evGoto ev))
    corrExp (evVar evX) (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evStoreI (evLoad evX) ∷ᵒ-ev evJF) evCtrl)
    corrExp (evVar evX) (ev□Goto ev                 ) = ev□Block (evBB (evStoreI (evLoad evX) ∷ []) (evGoto ev))
    -- corrExp (evVar evX) sem = {!corrEVar evX sem!}
    corrExp (evApp evF evEs evBody evRt) sem = corrExps evEs (corrCall evF evBody evRt sem)
    corrExp (evBuiltin evEs evBu) (ev□Block (evBB evJF evCtrl)) = corrExps evEs (ev□Block (evBB (evCallI (evBuiltin evBu) ∷ᵒ-ev evJF) evCtrl))
    corrExp (evBuiltin evEs evBu) (ev□Goto ev)                  = corrExps evEs (ev□Block (evBB (evCallI (evBuiltin evBu) ∷ []) (evGoto ev)))
    corrExp (evOp evE₁ evE₂ (evArith evO)) sem = corrExp evE₁ (corrExp evE₂ (corrArithOp evO sem))
    corrExp (evOp evE₁ evE₂ (evCmp   evO)) sem = {!!}
    corrExp (evOp evE₁ evE₂ (evLogic evO)) sem = {!!}
    corrExp (evAss evE assX) (ev□Block (evBB evJF evCtrl)) = corrExp evE (ev□Block (evBB (evStoreI (evStore assX) ∷ᵒ-ev (evStoreI (evLoad (lookupUpdated assX)) ∷ᵒ-ev evJF)) evCtrl))
    corrExp (evAss evE assX) (ev□Goto ev)                  = corrExp evE (ev□Block (evBB (evStoreI (evStore assX) ∷      evStoreI (evLoad (lookupUpdated assX)) ∷ []) (evGoto ev)))

    corrCall : ∀ {Γ t Δ Δ'} {f : funType Δ t ∈ Σ} {v : Val t} {γ : Env Γ}  {Φ} {φ : Frame Φ}
      {ss : Stms Σ t [] Δ Δ'} {vs : Vals Δ} {δ′ : Frame Δ'} {r : Res t}
      → (evF    : f ↦ Δ' , ss ∈ P)
      → (evBody : P , List.All.map just vs ∷ [] ⊢ ss ⇓ˢˢ r , (δ′ ∷ []))
      → (evRt   : r ≡return v)
      → ∀ {Λ k} {ƛ : LS Σ rt Λ}
      → CREval M ƛ rv k                           (γ , φ ▷ᵛ v)
      → CREval M ƛ rv (crExec (callI (call f)) k) (γ , φ ▷ᵛˢ vs)
    corrCall evF evBody evRt ev = {!!}

    corrStms : ∀ {Γ Δ Δ'} {ss : Stms Σ rt Γ Δ Δ'} {γ γ'} {r : Res rt} {Φ} {φ : Frame Φ}
      → (evRt : r ≡return rv)
      → (evSS : P , γ ⊢ ss ⇓ˢˢ r , γ')
      → ∀ {Λ k ƛ} (let cr = compileStms {rt = rt} ss {Λ} k)
      → CREval M ƛ rv k  (γ' , φ)
      → CREval M ƛ rv cr (γ , φ)
    corrStms evRt evNil ev = ev
    corrStms evRt (evCont evS evSS) ev = corrStm {!cont!} evS (corrStms evRt evSS ev)
    corrStms evRt (evRet evR) ev = {!x!}

    corrStm : ∀ {Γ t} {s : Stm Σ rt Γ t} {γ γ'} {r : Res rt} {Φ} {φ : Frame Φ}
      → (evRt : r ≡return rv)
      → (evS  : P , γ ⊢ s ⇓ˢ r , γ')
      → ∀ {Λ k ƛ} (let cr = compileStm {rt = rt} s {Λ} k)
      → CREval M ƛ rv k  (γ' , φ)
      → CREval M ƛ rv cr (γ , φ)
    corrStm evRt (evReturn evE) = corrComment ∘ corrExp evE ∘ corrReturn (corrReturnVal _ evRt)
    corrStm evRt (evExp evE)    = corrComment ∘ corrExp evE ∘ corrPop
    corrStm evRt evDecl         = corrComment ∘ corrDecl
    corrStm evRt (evInit evE)   = corrComment ∘ corrExp evE ∘ corrInit
    corrStm evRt (evBlock evSS) ev = {!!}
    corrStm evRt (evWhileDone evF) ev = corrComment {!!}
    corrStm evRt (evWhileStep evT evS evS') ev = corrComment {!!}
    corrStm evRt (evWhileRet evT evS) ev = corrComment {!!}
    corrStm evRt (evIfThen evT evS) ev = corrComment {!!}
    corrStm evRt (evIfElse evF evS) ev = corrComment {!!}

    corrReturn : ∀ {Γ} {v : Val rt} {γ : Env Γ} {Φ} {φ : Frame Φ} {Λ k} {ƛ : LS Σ rt Λ}
      → (evRt : ReturnVal rt rv (φ ▷ᵛ v))
      → CREval M ƛ rv k                               (γ , φ)
      → CREval M ƛ rv (crBB (λ ρ → mkBB [] bbReturn)) (γ , (φ ▷ᵛ v))
    corrReturn evRt (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB [] (evReturn evRt))
    corrReturn evRt (ev□Goto ev)                  = ev□Block (evBB [] (evReturn evRt))

    corrDecl : ∀ {t Γ x} {γ : Env Γ} {Φ} {φ : Frame Φ} {Λ k} {ƛ : LS Σ rt Λ}
      → CREval M ƛ rv k (push nothing γ , φ)
      → CREval M ƛ rv (crExec (scopeI (decl {t = t} x)) k) (γ , φ)
    corrDecl (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evScopeI evDecl ∷ᵒ-ev evJF) evCtrl)
    corrDecl (ev□Goto ev)                  = ev□Block (evBB (evScopeI evDecl ∷ []) (evGoto ev))

    -- corrDecl : ∀ {t Γ Δ x} {γ : Env Γ} {δ : Frame Δ} {Φ} {φ : Frame Φ} {Λ k} {ƛ : LS Σ rt Λ}
    --   → CREval M ƛ rv k ((nothing ∷ δ) ∷ γ , φ)
    --   → CREval M ƛ rv (crExec (scopeI (decl {t = t} x)) k) (δ ∷ γ , φ)
    -- corrDecl (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evScopeI evDecl ∷ᵒ-ev evJF) evCtrl)
    -- corrDecl (ev□Goto ev) = ev□Block (evBB ((evScopeI evDecl) ∷ []) (evGoto ev))

    corrStoreVZero : ∀ {x t Γ} {v₀ : Entry (` t)} {v : Val` t} {γ : Env Γ} {Φ} {φ : Frame Φ} {Λ k} {ƛ : LS Σ rt Λ}
      → CREval M ƛ rv k (push (just v) γ , φ)
      → CREval M ƛ rv (crExec (storeI (store (vzero x))) k) (push v₀ γ , just v ∷ φ)
    corrStoreVZero {x} (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evStoreI (evStore (updateTop x)) ∷ᵒ-ev evJF) evCtrl)
    corrStoreVZero {x} (ev□Goto ev)                  = ev□Block (evBB (evStoreI (evStore (updateTop x)) ∷ []) (evGoto ev))

    corrInit : ∀ {t Γ x} {v : Val` t} {γ : Env Γ} {Φ} {φ : Frame Φ} {Λ k} {ƛ : LS Σ rt Λ}
      → CREval M ƛ rv k (push (just v) γ , φ)
      → CREval M ƛ rv (crExec (scopeI (decl x)) (crExec (storeI (store (vzero x))) k)) (γ , just v ∷ φ)
    corrInit {γ = γ} ev = corrDecl (corrStoreVZero {v₀ = nothing} {γ = γ} ev)

    corrPop : ∀ {t Γ} {v : Val t} {γ : Env Γ} {Φ} {φ : Frame Φ} {Λ k} {ƛ : LS Σ rt Λ}
      → CREval M ƛ rv k (γ , φ)
      → CREval M ƛ rv (crExec (stackI (pop {t = t})) k) (γ , (φ ▷ᵛ v))
    corrPop {t = ` t}  (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evStackI evPop     ∷ᵒ-ev evJF) evCtrl)
    corrPop {t = void} (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evStackI evPopVoid ∷ᵒ-ev evJF) evCtrl)
    corrPop {t = ` t}  (ev□Goto ev)                  = ev□Block (evBB (evStackI evPop     ∷ []) (evGoto ev))
    corrPop {t = void} (ev□Goto ev)                  = ev□Block (evBB (evStackI evPopVoid ∷ []) (evGoto ev))

    corrComment : ∀ {Γ t} {s : Stm Σ rt Γ t} {γ} {Φ} {φ : Frame Φ}
      → ∀ {Λ k ƛ} (let cr = commentStm {rt = rt} s {Λ} k)
      → CREval M ƛ rv k  (γ , φ)
      → CREval M ƛ rv cr (γ , φ)
    corrComment (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evComment ∷ᵒ-ev evJF) evCtrl)
    corrComment (ev□Goto ev)                  = ev□Block (evBB (evComment ∷ []) (evGoto ev))

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

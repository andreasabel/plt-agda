

module Compiler.BB.CompilerCorrectness where

open import Library

open import WellTypedSyntax
open import Evaluation

open import Compiler.JumpFreeInstructions
open import Compiler.JFSemantics
open import Compiler.BasicBlocks
open import Compiler.BB.BBSemantics

corrReturnVal' : ∀ (rt : Type) {rv v : Val rt} {Φ} {φ : Frame Φ}
  → ResVal rt (ret v) rv
  → ReturnVal rt rv (φ ▷ᵛ v)
corrReturnVal' (` t) ret = refl
corrReturnVal' void  ret = _

corrReturnVal : ∀ (rt : Type) {v : Val rt} {Φ} {φ : Frame Φ}
  → ReturnVal rt v (φ ▷ᵛ v)
corrReturnVal (` t) = refl
corrReturnVal void  = _

data ReturnRes rt : ∀ (r : Res rt) {Φ} (φ : Frame Φ) → Set where

  ret  : ∀{Φ} {φ : Frame (Φ ▷ᵇ rt)} {v : Val rt}
       → ReturnVal rt v φ
       → ReturnRes rt (ret v) φ

  cont : ∀{Φ} {φ : Frame Φ}
       → ReturnRes rt cont φ

-- corrReturnRes : ∀ (rt : Type) {rv v : Res rt} {Φ} {φ : Frame Φ}
--   → ResRes rt r rv
--   → ReturnRes rt r φ
-- corrReturnRes (` t) ret = refl
-- corrReturnRes void  ret = _


-- TODO: Need an assumption that the program P has been compiled correctly
-- to the methods M

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

    corrCond : ∀ {Γ} {e : Exp` Σ Γ bool} {b : Bool} {γ γ' : Env Γ} {Φ} {φ : Frame Φ}
      → P , γ ⊢ e ⇓ᵉ b , γ'
      → ∀ {Λ kᵗ kᶠ ƛ} (let cr = compileCond {rt = rt} e {Λ} kᵗ kᶠ)
      → (evᵗ : CREval M ƛ rv kᵗ (γ' , φ))
      → (evᶠ : CREval M ƛ rv kᶠ (γ' , φ))
      → CREval M ƛ rv cr (γ , φ)
    corrCond {b = false} evConst evᵗ evᶠ = evᶠ
    corrCond {b = true} evConst evᵗ evᶠ = evᵗ
    corrCond (evOp evE evE₁ x) evᵗ evᶠ = {!!}

    corrCond evE@(evVar _)       evᵗ evᶠ = corrExp evE (corrBranchBool _ evᵗ evᶠ)
    corrCond evE@(evApp _ _ _ _) evᵗ evᶠ = {!!}
    corrCond evE@(evAss _ _)     evᵗ evᶠ = {!!}

    corrBranchBool : ∀ (b : Bool) {Γ}  {γ : Env Γ} {Φ} {φ : Frame Φ}
      → ∀ {Λ kᵗ kᶠ} {ƛ : LS Σ rt Λ}
      → (evᵗ : CREval M ƛ rv kᵗ (γ , φ))
      → (evᶠ : CREval M ƛ rv kᶠ (γ , φ))
      → CREval M ƛ rv (crIfElse (eqBool true) kᵗ kᶠ) (γ , just b ∷ φ)
    corrBranchBool false (ev□Block _) (ev□Block ev) = ev□Block (evBB [] (evIfFalse evEqBoolFalse {!aux ev !}))
    corrBranchBool false (ev□Goto  _) (ev□Block ev) = ev□Block (evBB [] (evIfFalse evEqBoolFalse {!!}))
    corrBranchBool false evᵗ (ev□Goto ev) = {!ev□Block (evBB ? (evGoto ev))!}
    corrBranchBool true (ev□Block ev) evᶠ = {!!}
    corrBranchBool true (ev□Goto ev) evᶠ = {!!}

    -- TODO: prove some kind of monotonicity for BBEval

    --   → BBEval M
    --      (ƛ'' ⊆-refl ++LS ƛ)
    --      rv
    --      (γ , φ)
    --      (□bb ⊆-refl)
    --   → BBEval M
    --      (WithBBs.bbs (joinBBs (η ∙ ƛ' ∙ □l) (η₁ ∙ ƛ'' ∙ □bb)) ⊆-refl ++LS ƛ)
    --      rv
    --      (γ , φ)
    --      (proj₂ (WithBBs.res (joinBBs (η ∙ ƛ' ∙ □l) (η₁ ∙ ƛ'' ∙ □bb)) ⊆-refl))

    corrCall : ∀ {Γ t Δ Δ'} {f : funType Δ t ∈ Σ} {v : Val t} {γ : Env Γ}  {Φ} {φ : Frame Φ}
      {ss : Stms Σ t [] Δ Δ'} {vs : Vals Δ} {δ′ : Frame Δ'} {r : Res t}
      → (evF    : f ↦ Δ' , ss ∈ P)
      → (evBody : P , List.All.map just vs ∷ [] ⊢ ss ⇓ˢˢ r , (δ′ ∷ []))
      → (evRt   : r ≡return v)
      → ∀ {Λ k} {ƛ : LS Σ rt Λ}
      → CREval M ƛ rv k                           (γ , φ ▷ᵛ v)
      → CREval M ƛ rv (crExec (callI (call f)) k) (γ , φ ▷ᵛˢ vs)
    corrCall evF evBody evRt (ev□Block ev) = {!!}
    corrCall evF evBody evRt (ev□Goto ev) = ev□Block (evBB (evCallI (evCall (evFun {!!})) ∷ []) (evGoto ev))
       -- Goal:
       -- BBEval M (Meth.blocks (List.All.lookup M f)) v
       --      (List.All.map just vs ∷ [] , []) (Meth.entry (List.All.lookup M f))

    corrStms : ∀ {Γ Δ Δ'} {ss : Stms Σ rt Γ Δ Δ'} {γ γ'} {r : Res rt} {Φ} {φ : Frame Φ}
      → (evSS : P , γ ⊢ ss ⇓ˢˢ r , γ')
      → ∀ {Λ k ƛ} (let cr = compileStms {rt = rt} ss {Λ} k)
      → CREval? M ƛ rv k  (γ' , φ) r
      → CREval M ƛ rv cr (γ , φ)
    corrStms evNil             (cont ev) = ev
    corrStms (evCont evS evSS) ev        = corrStm evS (cont (corrStms evSS ev))
    corrStms (evRet evR)       ret       = corrStm evR ret

    corrStm : ∀ {Γ t} {s : Stm Σ rt Γ t} {γ γ'} {r : Res rt} {Φ} {φ : Frame Φ}
      → (evS  : P , γ ⊢ s ⇓ˢ r , γ')
      → ∀ {Λ k ƛ} (let cr = compileStm {rt = rt} s {Λ} k)
      → CREval? M ƛ rv k (γ' , φ) r
      → CREval  M ƛ rv cr (γ , φ)
    corrStm (evReturn evE)      ret       = corrComment (corrExp evE (corrReturn (corrReturnVal _)))
    corrStm (evExp evE)         (cont ev) = corrComment (corrExp evE (corrPop ev))
    corrStm evDecl              (cont ev) = corrComment {! corrDecl ev !}
    corrStm (evInit evE)        (cont ev) = corrComment (corrExp evE (corrInit ev))
    corrStm (evBlock evSS)      ev        = corrNewBlock (corrStms evSS (corrPopBlock <$> ev))
    corrStm (evWhileDone evF)   (cont ev) = corrComment {!!}
    corrStm (evWhileStep evT evS evS') ev = corrComment {!!}
    corrStm (evWhileRet evT evS)      ret = corrComment {!!}
    corrStm (evIfThen evT evS)  ev        = corrComment {!!}
    corrStm (evIfElse evF evS)  ev        = corrComment {!!}

    corrReturn : ∀ {Γ} {v : Val rt} {γ : Env Γ} {Φ} {φ : Frame Φ} {Λ} {ƛ : LS Σ rt Λ}
      → (evRt : ReturnVal rt rv (φ ▷ᵛ v))
      → CREval M ƛ rv (crBB (λ ρ → mkBB [] bbReturn)) (γ , (φ ▷ᵛ v))
    corrReturn evRt = ev□Block (evBB [] (evReturn evRt))

    corrNewBlock : ∀ {Γ} {γ : Env Γ} {Φ} {φ : Frame Φ} {Λ k} {ƛ : LS Σ rt Λ}
      → CREval M ƛ rv k ([] ∷ γ , φ)
      → CREval M ƛ rv (crExec (scopeI newBlock) k) (γ , φ)
    corrNewBlock (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evScopeI evNewBlock ∷ᵒ-ev evJF) evCtrl)
    corrNewBlock (ev□Goto ev)                  = ev□Block (evBB (evScopeI evNewBlock ∷ []) (evGoto ev))

    corrPopBlock : ∀ {Γ Δ} {γ : Env Γ} {δ : Frame Δ} {Φ} {φ : Frame Φ} {Λ k} {ƛ : LS Σ rt Λ}
      → CREval M ƛ rv k (γ , φ)
      → CREval M ƛ rv (crExec (scopeI popBlock) k) (δ ∷ γ , φ)
    corrPopBlock (ev□Block (evBB evJF evCtrl)) = ev□Block (evBB (evScopeI evPopBlock ∷ᵒ-ev evJF) evCtrl)
    corrPopBlock (ev□Goto ev)                  = ev□Block (evBB (evScopeI evPopBlock ∷ []) (evGoto ev))

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

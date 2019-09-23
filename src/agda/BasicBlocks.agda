module BasicBlocks where

open import Library
open import Library.AllExt

open import WellTypedSyntax
open import Value
open import FlowChart

module _ (Σ : Sig) (rt : Type) where

  -- Basic blocks are flow charts without label definition

  data BB (Λ : Labels) : (Ξ : MT) → Set where
    -- Ends:
    bbGoto   : ∀{Ξ} (l : Ξ ∈ Λ) → BB Λ Ξ             -- goto join point (same Ξ)
    bbReturn : ∀{Γ Φ}           → BB Λ (Γ , Φ ▷ᵇ rt) -- return from function (stack is destroyed)
    -- Branching:
    bbIfElse : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (bb bb' : BB Λ (Γ , Φ')) → BB Λ (Γ , Φ)
    -- Cons-like: Instruction
    bbExec     : ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') (bb : BB Λ Ξ') → BB Λ Ξ

  BB′ = λ Ξ Λ → BB Λ Ξ

  -- Flatten out label definitions from a flow chart

  record Flat Λ Ξ : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : □ (λ Λ′ → AllExt (BB Λ′) ext) Ext
      bb    : □ (λ Λ′ → BB Λ′ Ξ) Ext

  flat : ∀{Λ Ξ} → FC Σ rt Λ Ξ → Flat Λ Ξ

  flat (fcGoto l) = ⊆-refl ∙ (λ τ → AllExt-id) ∙ λ τ → bbGoto (⊆-lookup τ l)
  flat fcReturn   = ⊆-refl ∙ (λ τ → AllExt-id) ∙ λ τ → bbReturn

  flat (fcExec j fc)
    with η ∙ bbs ∙ bb ← flat fc = η ∙ bbs ∙ (bbExec j ∘ bb)

  flat (fcFix fc)
    with η ∙ bbs ∙ bb ← flat fc
      = ⊆-trans (⊆-skip _ ⊆-refl) η
      ∙ (λ τ → AllExt-comp (bb τ ∷ AllExt-id) (bbs τ))
      ∙ (λ τ → bbGoto (⊆-lookup (⊆-trans η τ) here!))

  flat (fcIfElse c fc₁ fc₂)
    with η₁ ∙ bbs₁ ∙ bb₁ ← flat fc₁
       | η₂ ∙ bbs₂ ∙ bb₂ ← flat fc₂
      = η ∙ bbs ∙ bs
    where
    rpo   = ⊆-pushoutˡ η₁ η₂
    Λ     = RawPushout.upperBound rpo
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo
    η     = ⊆-trans η₁ ξ₁
    bs    : □ (λ Λ′ → BB Λ′ _) _
    bs  τ = bbIfElse c (bb₁ (⊆-trans ξ₁ τ)) (bb₂ (⊆-trans ξ₂ τ))
    bbs   : □ (λ Λ′ → AllExt (BB Λ′) η) Λ
    bbs τ = AllExt-join (bbs₁ (⊆-trans ξ₁ τ)) (bbs₂ (⊆-trans ξ₂ τ))

  flat (fcLet fc₁ fc₂)
    with η₁ ∙ bbs₁ ∙ bb₁ ← flat fc₁
       | η₂ ∙ bbs₂ ∙ bb₂ ← flat fc₂
      = ⊆-trans (⊆-skip _ ⊆-refl) η
      ∙ (λ τ → AllExt-comp ((bb₁ (⊆-trans ξ₁′ τ)) ∷ AllExt-id) (bbs τ))
      ∙ λ τ → bb₂ (⊆-trans ξ₂ τ)
    where
    rpo   = ⊆-pushoutˡ (refl ∷ η₁) η₂
    Λ     = RawPushout.upperBound rpo
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo
    η     = ⊆-trans (refl ∷ η₁) ξ₁
    ξ₁′   = ⊆-trans (⊆-skip _ ⊆-refl) ξ₁
    bbs   : □ (λ Λ′ → AllExt (BB Λ′) η) Λ
    bbs τ = AllExt-join (lift (bbs₁ (⊆-trans ξ₁′ τ))) (bbs₂ (⊆-trans ξ₂ τ))

  -- Compilation of C-- to basic blocks

  BBs : ∀ {Λ Λ'} (ξ : Λ ⊆ Λ') → Set
  BBs {Λ} {Λ′} ξ = (□ λ Λ″ → AllExt (BB Λ″) ξ) Λ′

  data BBOrGoto (Ξ : MT) (Λ : Labels) : Set where
    block : (bb : □ (BB′ Ξ) Λ) → BBOrGoto Ξ Λ
    goto  : (l  : Ξ ∈ Λ)  → BBOrGoto Ξ Λ

  gotoToBB : ∀{Ξ Λ} → BBOrGoto Ξ Λ → □ (BB′ Ξ) Λ
  gotoToBB (block bb) = bb
  gotoToBB (goto l)   = λ ρ → bbGoto (⊆-lookup ρ l)

  record CompRes (Ξ : MT) (Λ : Labels) : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : BBs ext
      res   : BBOrGoto Ξ Λ

  bbRes : ∀{Ξ Λ} → BBOrGoto Ξ Λ → CompRes Ξ Λ
  bbRes res = _ ∙ (λ ρ → AllExt-id) ∙ res

  mutual

    compileStm : ∀ {Γ mt}
        (s : Stm Σ rt Γ mt) {Λ Φ}
        (k : BBOrGoto (Γ ▷ mt , Φ) Λ)
        → CompRes (Γ , Φ) Λ
        -- → ∃₂ λ Λₜ (ξ : Λ ⊆ Λₜ) → BBs (Γ , Φ) ξ
    compileStm s k = {!!}

    compileCond : ∀{Γ}
      (e : Exp` Σ Γ bool) {Λ Φ}
      (kᵗ kᶠ : BBOrGoto (Γ , Φ) Λ)
      → CompRes (Γ , Φ) Λ
    compileCond (eConst false) kᵗ kᶠ = bbRes kᶠ
    compileCond (eConst true ) kᵗ kᶠ = bbRes kᵗ
    compileCond (eOp op e e') kᵗ kᶠ = {!!}
    compileCond e@(eVar _  )  kᵗ kᶠ = compileExp e (block (λ ρ → bbIfElse (eqBool true) (gotoToBB kᵗ ρ) (gotoToBB kᶠ ρ)))
    compileCond e@(eApp _ _)  kᵗ kᶠ = compileExp e (block (λ ρ → bbIfElse (eqBool true) (gotoToBB kᵗ ρ) (gotoToBB kᶠ ρ)))
    compileCond e@(eAss _ _)  kᵗ kᶠ = compileExp e (block (λ ρ → bbIfElse (eqBool true) (gotoToBB kᵗ ρ) (gotoToBB kᶠ ρ)))
    compileCond (eIncrDecr p (incr ()) x) kᵗ kᶠ
    compileCond (eIncrDecr p (decr ()) x) kᵗ kᶠ

    -- Compiling composite conditionals.

    compileBoolOp : ∀{Γ t}
      (op   : Op t bool)
      (e e' : Exp` Σ Γ t) {Λ Φ}
      (kt kf : BBOrGoto (Γ , Φ) Λ)  -- kt: true, kf: false
      → CompRes (Γ , Φ) Λ

    compileBoolOp (logic and) e e' kt kf = {!!}
    compileBoolOp (logic or)  e e' kt kf = {!!}
    compileBoolOp (cmp   op)  e e' kt kf =
      compileExp e  $ block $ λ ρ  →
      compileExp e' $ block $ λ ρ' →
      bbIfElse (cmp op) (gotoToBB kt (⊆-trans ρ ρ'))
                        (gotoToBB kf (⊆-trans ρ ρ'))
    compileBoolOp (arith (plus ()))
    compileBoolOp (arith (minus ()))
    compileBoolOp (arith (times ()))
    compileBoolOp (arith (div ()))


    -- Compiling expressions.

    compileExp : ∀{Γ t}
      (e : Exp Σ Γ t)          {Λ Φ}
      (k : BBOrGoto (Γ , Φ ▷ᵇ t) Λ)
      → CompRes (Γ , Φ) Λ
    compileExp e k = {!!}

{-

  -- Compilation of C-- to basic blocks

  BBs : ∀ (Ξ : MT) {Λ Λ'} (ξ : Λ ⊆ Λ') → Set
  BBs Ξ {Λ} {Λ′} ξ = (□ λ Λ″ → AllExt (BB Λ″) (⊆-skip Ξ ξ)) Λ′

  record CompRes (Ξ : MT) (Λ : Labels) : Set where
    constructor _,_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : BBs Ξ ext

  mutual

    compileStm : ∀ {Γ mt}
        (s : Stm Σ rt Γ mt) {Λ Φ}
        (lᵏ : (Γ ▷ mt , Φ) ∈ Λ)
        → CompRes (Γ , Φ) Λ
        -- → ∃₂ λ Λₜ (ξ : Λ ⊆ Λₜ) → BBs (Γ , Φ) ξ
    compileStm s lᵏ = {!!}

    compileCond : ∀{Γ}
      (e : Exp` Σ Γ bool) {Λ Φ}
      (lᵗ lᶠ : (Γ , Φ) ∈ Λ)
      → CompRes (Γ , Φ) Λ
    compileCond (eConst false) lᵗ lᶠ = ⊆-refl , λ ρ → bbGoto (⊆-lookup ρ lᶠ) ∷ AllExt-id
    compileCond (eConst true) lᵗ lᶠ  = ⊆-refl , λ ρ → bbGoto (⊆-lookup ρ lᵗ) ∷ AllExt-id
    compileCond (eOp op e e') lᵗ lᶠ = {!!}
    compileCond e@(eVar _) lᵗ lᶠ = {!!}
    compileCond e@(eApp _ _) lᵗ lᶠ = {!!}
    compileCond e@(eAss _ _) lᵗ lᶠ = {!!}
    compileCond (eIncrDecr p (incr ()) x) lᵗ lᶠ
    compileCond (eIncrDecr p (decr ()) x) lᵗ lᶠ

-- -}
-- -}
-- -}
-- -}

-- Expressing control constructs in terms of labels and jumps.


open import Library
open import WellTypedSyntax

module FlowChart (Σ : Sig) where

-- As a first step, we use let and fix to deal with labels.
-- Flow charts are like statement lists.

-- Labels are numbers bounded by the number of available lables.
-- They are like de Bruijn indices.

NLabels = ℕ
Label   = Fin

module _ (Ret Cond Eff : Cxt → Set) where

  data FC (n : NLabels) : (Γ Γ' : Cxt) → Set where
    -- Ends:
    fcGoto   : ∀{Γ} (l : Label n) → FC n Γ Γ  -- goto join point
    fcReturn : ∀{Γ Γ'} (r : Ret Γ) → FC n Γ Γ'      -- return from function
    -- Branching:
    fcIfElse : ∀{Γ} (c : Cond Γ) (fc fc' : FC n Γ Γ) → FC n Γ Γ
    -- Label definition
    fcLet    : ∀{Γ} (fc : FC n Γ Γ) (fc' : FC (suc n) Γ Γ) → FC n Γ Γ
    fcFix    : ∀{Γ} (fc : FC (suc n) Γ Γ) → FC n Γ Γ
    -- Cons-like:
    -- Scope
    fcNewBlock : ∀{Γ Γ'} (fc : FC n ([] ∷⁺ Γ) Γ') → FC n Γ Γ'
    fcPopBlock : ∀{Γ Γ' Δ} (fc : FC n Γ Γ') → FC n (Δ ∷⁺ Γ) Γ'
    fcDecl     : ∀{Γ Γ'} {t : Ty} (fc : FC n (Γ ▷ just t) Γ') → FC n Γ Γ'
    -- Instruction
    fcExec     : ∀{Γ Γ'} (e : Eff Γ) (fc : FC n Γ Γ') → FC n Γ Γ'

  module CompileStm where
   mutual
    compileStm : ∀{rt Γ Γ' mt}
      (s : Stm Σ rt Γ mt) {n}
      (k : ∀{n'} (ρ : n ≤ n') → FC n (Γ ▷ mt) Γ')
      → FC n Γ Γ'
    compileStm (sReturn e) k = fcReturn {!compileRet e!}
    compileStm (sExp e) k = fcExec {!compileEff e!} (k ≤-refl)
    compileStm (sInit e) k = fcDecl {!compileAss e!}
    compileStm (sBlock ss) k = fcNewBlock (compileStms ss λ ρ → fcPopBlock (k ρ))
    compileStm (sWhile e s) k = {!!}
    compileStm (sIfElse e s s') k = {!fcLet (k ≤-refl)!}

    compileStms : ∀{rt Γ Δ Δ' Γ'}
      (ss : Stms Σ rt Γ Δ Δ') {n}
      (k : ∀{n'} (ρ : n ≤ n') → FC n (Δ' ∷ Γ) Γ')
      → FC n (Δ ∷ Γ) Γ'
    compileStms []       k = k ≤-refl
    compileStms (s ∷ ss) k = compileStm s (λ ρ → compileStms ss λ ρ' → k {!≤-trans ρ ρ'!})

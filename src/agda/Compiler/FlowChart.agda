-- Expressing control constructs in terms of labels and jumps.

module Compiler.FlowChart where

open import Library renaming (⊆-lookup to weakLabel; ⊆-refl to !)
open import WellTypedSyntax
open import Value

open import Compiler.JumpFreeInstructions public
open import Compiler.Labels               public

-- As a first step, we use let and fix to deal with labels.
-- Flow charts are like statement lists.

-- Within a method, the return type rt is fixed.

module _ (Σ : Sig) (rt : Type) where

    -- Control: labels, branching, and sequencing.
    -- Ξ is machine state type when starting to run fc

    data FC (Λ : Labels) : (Ξ : MT) → Set where
      -- Ends:
      fcGoto   : ∀{Ξ} (l : Ξ ∈ Λ) → FC Λ Ξ           -- goto join point (same Ξ)
      fcReturn : ∀{Γ Φ}           → FC Λ (Γ , Φ ▷ᵇ rt) -- return from function (stack is destroyed)
      -- Branching:
      fcIfElse : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (fc fc' : FC Λ (Γ , Φ')) → FC Λ (Γ , Φ)
      -- Label definition
      fcLet    : ∀{Ξ Ξ'} (fc  : FC Λ Ξ') (fc' : FC (Ξ' ∷ Λ) Ξ) → FC Λ Ξ
      fcFix    : ∀{Ξ} (fc : FC (Ξ ∷ Λ) Ξ) → FC Λ Ξ
      -- Cons-like: Instruction
      fcExec     : ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') (fc : FC Λ Ξ') → FC Λ Ξ

    -- JVM-like instructions as pattern-synonyms.

    -- fcAdm : ∀{Γ Γ' Φ}(adm : ScopeI Γ Γ') (fc : FC Λ (Γ', Φ)) → FC Λ (Γ , Φ)
    pattern fcAdm j fc = fcExec (scopeI j) fc

    -- fcNewBlock : ∀{Γ}   (fc : FC Λ ([] ∷⁺ Γ)) → FC Λ Γ
    pattern fcNewBlock fc = fcAdm newBlock fc

    -- fcPopBlock : ∀{Γ Δ} (fc : FC Λ Γ) → FC Λ (Δ ∷⁺ Γ)
    pattern fcPopBlock fc = fcAdm popBlock fc

    -- fcDecl     : ∀{Γ t} (fc : FC Λ (Γ ▷ just t)) → FC Λ Γ
    pattern fcDecl x fc = fcAdm (decl x) fc

    pattern fcStackI j fc = fcExec (stackI j) fc
    pattern fcConst  v fc = fcStackI (const v) fc
    pattern fcPop      fc = fcStackI pop fc
    pattern fcDup      fc = fcStackI dup fc
    pattern fcArith op fc = fcStackI (arith op) fc

    pattern fcAdd   t  fc = fcArith (plus  t) fc
    pattern fcSub   t  fc = fcArith (minus t) fc

    pattern fcStoreI j fc = fcExec (storeI j) fc
    pattern fcAssign x fc = fcStoreI (store x) fc
    pattern fcLoad   x fc = fcStoreI (load x) fc
    pattern fcIncDec b x fc = fcStoreI (incDec b x) fc

    pattern fcCall    f fc = fcExec (callI (call    f)) fc
    pattern fcBuiltin f fc = fcExec (callI (builtin f)) fc

-- -}
-- -}
-- -}

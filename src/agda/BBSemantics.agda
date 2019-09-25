{-# OPTIONS --allow-unsolved-metas #-}

open import Library renaming (⊆-lookup to weakLabel) -- ; ⊆-refl to !)
open import WellTypedSyntax
open import Value
open import Environment
open import FlowChart
open import BasicBlocks
open import Evaluation
open import FCSemantics using (MS; ReturnVal; JFEval)

module BBSemantics where

module _ (Σ : Sig) (rt : Type) where

  -- "Label semantics": mapping each label to its basic block

  LS : Labels → Set
  LS Λ = List.All (BB Σ rt Λ) Λ

  -- Big-step semantics of flow charts.  TODO: finish.

  mutual

    data BBEval {Λ : Labels} (ƛ : LS Λ) (v : Val rt) : {Ξ : MT} (ξ : MS Ξ) → BB Σ rt Λ Ξ → Set where

      evReturn : ∀ {Γ Φ} {γ : Env Γ} {φ : Frame (Φ ▷ᵇ rt)}
           → ReturnVal rt v φ
           → BBEval ƛ v (γ , φ) bbReturn

      -- Goto l amounts to fetching the flowchart corresponding to l from ƛ and continue there.

      evGoto : ∀{Ξ l}{ξ : MS Ξ}
           → BBEval ƛ v ξ (List.All.lookup ƛ l)
           → BBEval ƛ v ξ (bbGoto l)

      evIfTrue : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {bbᵗ bbᶠ : BB Σ rt Λ (Γ , Φ′)}

           → BBEval ƛ v (γ , φ′) bbᵗ
           → BBEval ƛ v (γ , φ ) (bbIfElse c bbᵗ bbᶠ)

      -- Single jump-free instruction.

      evExec : ∀{Ξ Ξ'} {ξ ξ'} {jf : JF Σ Ξ Ξ'} {bb : BB Σ rt Λ Ξ'}

           → JFEval ξ ξ' jf
           → BBEval ƛ v ξ' bb
           → BBEval ƛ v ξ (bbExec jf bb)

-- -}
-- -}
-- -}
-- -}
-- -}

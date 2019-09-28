
module Compiler.BB.BBSemantics where

open import Library
open import WellTypedSyntax
open import Value
open import Environment
open import Evaluation

open import Compiler.BasicBlocks
open import Compiler.JFSemantics

-- "Label semantics": mapping each label to its basic block

LS : (Σ : Sig) (rt : Type) (Λ : Labels) → Set
LS Σ rt Λ = List.All (BB Σ rt Λ) Λ

module _ {Σ : Sig} {rt : Type} where

  -- Big-step semantics of flow charts.

  module _ {Λ : Labels} (ƛ : LS Σ rt Λ) (v : Val rt) where

    data BBEval : {Ξ : MT} (ξ : MS Ξ) → BB Σ rt Λ Ξ → Set where

      -- Single jump-free instruction.

      evExec : ∀{Ξ Ξ'} {ξ ξ'} {jf : JF Σ Ξ Ξ'} {bb : BB Σ rt Λ Ξ'}

           → JFEval jf ξ ξ'
           → BBEval ξ' bb
           → BBEval ξ (bbExec jf bb)

      -- Return.

      evReturn : ∀ {Γ Φ} {γ : Env Γ} {φ : Frame (Φ ▷ᵇ rt)}
           → ReturnVal rt v φ
           → BBEval (γ , φ) bbReturn

      -- Goto l amounts to fetching the flowchart corresponding to l from ƛ and continue there.

      evGoto : ∀{Ξ l}{ξ : MS Ξ}
           → BBEval ξ (List.All.lookup ƛ l)
           → BBEval ξ (bbGoto l)

      -- Unary conditionals.

      evIfTrue : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {lᵗ : (Γ , Φ′) ∈ Λ} {bbᶠ : BB Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ true
           → BBEval (γ , φ′) (List.All.lookup ƛ lᵗ)
           → BBEval (γ , φ ) (bbIf c lᵗ bbᶠ)

      evIfFalse : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {lᵗ : (Γ , Φ′) ∈ Λ} {bbᶠ : BB Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ false
           → BBEval (γ , φ′) bbᶠ
           → BBEval (γ , φ ) (bbIf c lᵗ bbᶠ)

      -- Binary conditionals.

      evIfElseTrue : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {bbᵗ bbᶠ : BB Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ true
           → BBEval (γ , φ′) bbᵗ
           → BBEval (γ , φ ) (bbIfElse c bbᵗ bbᶠ)

      evIfElseFalse : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {bbᵗ bbᶠ : BB Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ false
           → BBEval (γ , φ′) bbᶠ
           → BBEval (γ , φ ) (bbIfElse c bbᵗ bbᶠ)

-- -}
-- -}
-- -}
-- -}
-- -}

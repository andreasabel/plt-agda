{-# OPTIONS --allow-unsolved-metas #-}

module Compiler.FC.FCSemantics where

open import Library
open import WellTypedSyntax
open import Value
open import Environment
open import Evaluation

open import Compiler.FlowChart
open import Compiler.JFSemantics

module _ {Σ : Sig} {rt : Type} where

  -- To implement jumps, we associate to each label the flowchart following this label.
  -- "Label semantics" LS.

  data LS : Labels → Set where
    [] : LS []
    _∷_ : ∀{Λ Ξ} (fc : FC Σ rt Λ Ξ) (ƛ : LS Λ) → LS (Ξ ∷ Λ)

  -- -- Not the same:
  -- LS : Labels → Set
  -- LS Λ = List.All (FC Σ rt Λ) Λ

  -- Big-step semantics of flow charts.

  mutual

    data FCEval {Λ : Labels} (ƛ : LS Λ) (v : Val rt) : {Ξ : MT} (ξ : MS Ξ) → FC Σ rt Λ Ξ → Set where

      -- Single jump-free instruction.

      evExec : ∀{Ξ Ξ'} {jf : JF Σ Ξ Ξ'} {fc} {ξ ξ'}
           → JFEval {!!} jf ξ ξ'
           → FCEval ƛ v ξ' fc
           → FCEval ƛ v ξ (fcExec jf fc)

      -- Return.

      evReturn : ∀ {Γ Φ} {γ : Env Γ} {s : Frame (Φ ▷ᵇ rt)}
           → ReturnVal rt v s
           → FCEval ƛ v (γ , s) fcReturn

      -- Goto l amounts to fetching the flowchart corresponding to l from ƛ and continue there.

      evGoto : ∀{Ξ l}{ξ : MS Ξ}
           -- → FCEval ƛ v ξ (lookupLS ƛ l)
           → FCGoto v ξ ƛ l
           → FCEval ƛ v ξ (fcGoto l)

      -- Binary conditionals.

      evIfElseTrue : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {fcᵗ fcᶠ : FC Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ true
           → FCEval ƛ v (γ , φ′) fcᵗ
           → FCEval ƛ v (γ , φ ) (fcIfElse c fcᵗ fcᶠ)

      evIfElseFalse : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {fcᵗ fcᶠ : FC Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ false
           → FCEval ƛ v (γ , φ′) fcᶠ
           → FCEval ƛ v (γ , φ ) (fcIfElse c fcᵗ fcᶠ)

      -- let and fix define labels.
      -- We associate them to the corresponding fc in ƛ.

      evLet : ∀{Ξ Ξ'}{ξ : MS Ξ}{fc : FC Σ rt Λ Ξ'} {fc'}
           → FCEval (fc ∷ ƛ) v ξ fc'
           → FCEval ƛ v ξ (fcLet fc fc')

      evFix : ∀{Ξ} {ξ : MS Ξ} {fc}
           → FCEval (fcFix fc ∷ ƛ) v ξ fc
           → FCEval ƛ v ξ (fcFix fc)

    -- Due to scoping invariants, FCGoto l can remove newer label bindings from ƛ.
    -- (Observation by Alexander Fuhs.)  Thus, weakening of FCs is not needed.

    data FCGoto (v : Val rt) {Ξ : MT} (ξ : MS Ξ) : {Λ : Labels} (ƛ : LS Λ) (l : Ξ ∈ Λ) → Set where

      gotoHere : ∀{Λ}{ƛ : LS Λ}{fc : FC Σ rt Λ Ξ}
        → FCEval ƛ v ξ fc
        → FCGoto v ξ (fc ∷ ƛ) here!

      gotoThere : ∀{Λ}{ƛ : LS Λ}{Ξ′}{fc : FC Σ rt Λ Ξ′}{l : Ξ ∈ Λ}
        → FCGoto v ξ ƛ l
        → FCGoto v ξ (fc ∷ ƛ) (there l)

{-

  -- Looking up a label in the label semantics gives us a flowchart.
  -- (Need weakening of flow-charts here because of de Bruijn indices.
  -- After a translation to de Bruijn levels, no weakening would be needed.)

  lookupLS' : ∀ {Λ Λ' Ξ} (ƛ : LS Λ) (l : Ξ ∈ Λ) (w : Λ ⊆ Λ') → FC Σ rt Λ' Ξ
  lookupLS' (fc ∷ ƛ) (here refl) w = {!wkFC w fc!}   -- need weakening for FC
  lookupLS' (fc ∷ ƛ) (there l) w = lookupLS' ƛ l (⊆-trans ⊆-wk1 w)

  lookupLS : ∀ {Λ Ξ} (ƛ : LS Λ) (l : Ξ ∈ Λ) → FC Σ rt Λ Ξ
  lookupLS ƛ l = lookupLS' ƛ l ⊆-refl


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

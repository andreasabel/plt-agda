{-# OPTIONS --allow-unsolved-metas #-}

module Compiler.FC.FCSemantics where

open import Library renaming (⊆-lookup to weakLabel) -- ; ⊆-refl to !)
open import WellTypedSyntax
open import Value
open import Environment
open import Evaluation

open import Compiler.FlowChart

-- Machine state

MS : MT → Set
MS (Γ , Φ) = Env Γ × Frame Φ

-- ReturnVal rt v s holds if rt is void or v is on top of the stack s.

ReturnVal : ∀ rt {Φ} (v : Val rt) (s : Frame (Φ ▷ᵇ rt)) → Set
ReturnVal (` t) v (just v' ∷ _) = v ≡ v'
ReturnVal (` t) v (nothing ∷ _) = ⊥
ReturnVal void _ _ = ⊤

--

-- variable
--   Σ : Sig
--   rt : Type

module _ {Σ : Sig} {rt : Type} where

  data StackIEval : ∀ {Φ Φ'} (φ : Frame Φ) (φ' : Frame Φ') (j : StackI Φ Φ') → Set where

    evConst : ∀{Φ t} {φ : Frame Φ} {v : Val` t}
      → StackIEval φ (just v ∷ φ) (const v)

    evDup : ∀{Φ t} {φ : Frame Φ} {v : Entry` t}
      → StackIEval (v ∷ φ) (v ∷ v ∷ φ) dup

    evPopVoid : ∀ {Φ} {φ : Frame Φ}
      → StackIEval φ φ (pop {t = void})

    evPop : ∀ {Φ t} {φ : Frame Φ} {v : Entry` t}
      → StackIEval (v ∷ φ) φ (pop {t = ` t})

    evArith : ∀{Φ t} {φ : Frame Φ} {v₁ v₂ v : Entry` t} {op : ArithOp t}
      -- → v₁ ⟨ op ⟩ v₂ ⇓ᵃ v -- TODO: what about undefined stack entries?
      → StackIEval (v₂ ∷ v₁ ∷ φ) (v ∷ φ) (arith op)

    -- TODO

  -- Small step operational semantics of jump-free instructions.
  -- A jf instruction relates two machine states (before and after the instruction).

  data JFEval : ∀ {Ξ Ξ'} (ξ : MS Ξ) (ξ' : MS Ξ') → JF Σ Ξ Ξ' → Set where

    evStackI : ∀{Γ Φ Φ'} (j : StackI Φ Φ') {γ : Env Γ} {φ : Frame Φ} {φ' : Frame Φ'}
      → StackIEval φ φ' j
      → JFEval (γ , φ) (γ , φ') (stackI j)



    -- TODO

  -- To implement jumps, we associate to each label the flowchart following this label.
  -- "Label semantics" LS.

  data LS : Labels → Set where
    [] : LS []
    _∷_ : ∀{Λ Ξ} (fc : FC Σ rt Λ Ξ) (ƛ : LS Λ) → LS (Ξ ∷ Λ)

  -- -- Not the same:
  -- LS : Labels → Set
  -- LS Λ = List.All (FC Σ rt Λ) Λ

  -- Looking up a label in the label semantics gives us a flowchart.
  -- (Need weakening of flow-charts here because of de Bruijn indices.
  -- After a translation to de Bruijn levels, no weakening would be needed.)

  lookupLS' : ∀ {Λ Λ' Ξ} (ƛ : LS Λ) (l : Ξ ∈ Λ) (w : Λ ⊆ Λ') → FC Σ rt Λ' Ξ
  lookupLS' (fc ∷ ƛ) (here refl) w = {!wkFC w fc!}   -- need weakening for FC
  lookupLS' (fc ∷ ƛ) (there l) w = lookupLS' ƛ l (⊆-trans (⊆-skip _ ⊆-refl) w)

  lookupLS : ∀ {Λ Ξ} (ƛ : LS Λ) (l : Ξ ∈ Λ) → FC Σ rt Λ Ξ
  lookupLS ƛ l = lookupLS' ƛ l ⊆-refl

  -- Big-step semantics of flow charts.  TODO: finish.

  mutual

    data FCEval {Λ : Labels} (ƛ : LS Λ) (v : Val rt) : {Ξ : MT} (ξ : MS Ξ) → FC Σ rt Λ Ξ → Set where

      evReturn : ∀ {Γ Φ} {γ : Env Γ} {s : Frame (Φ ▷ᵇ rt)}
           → ReturnVal rt v s
           → FCEval ƛ v (γ , s) fcReturn

      -- Goto l amounts to fetching the flowchart corresponding to l from ƛ and continue there.

      evGoto : ∀{Ξ l}{ξ : MS Ξ}
           -- → FCEval ƛ v ξ (lookupLS ƛ l)
           → FCGoto v ξ ƛ l
           → FCEval ƛ v ξ (fcGoto l)

      -- let and fix define labels.
      -- We associate them to the corresponding fc in ƛ.

      evLet : ∀{Ξ Ξ'}{ξ : MS Ξ}{fc : FC Σ rt Λ Ξ'} {fc'}
           → FCEval (fc ∷ ƛ) v ξ fc'
           → FCEval ƛ v ξ (fcLet fc fc')

      evFix : ∀{Ξ} {ξ : MS Ξ} {fc}
           → FCEval (fcFix fc ∷ ƛ) v ξ fc
           → FCEval ƛ v ξ (fcFix fc)

      -- Single jump-free instruction.

      evExec : ∀{Ξ Ξ'} {ξ ξ'} {jf : JF Σ Ξ Ξ'} {fc}
           → JFEval ξ ξ' jf
           → FCEval ƛ v ξ' fc
           → FCEval ƛ v ξ (fcExec jf fc)

    -- Due to scoping invariants, FCGoto l can remove newer label bindings from ƛ.
    -- (Observation by Alexander Fuhs.)  Thus, weakening of FCs is not needed.

    data FCGoto (v : Val rt) {Ξ : MT} (ξ : MS Ξ) : {Λ : Labels} (ƛ : LS Λ) (l : Ξ ∈ Λ) → Set where

      gotoHere : ∀{Λ}{ƛ : LS Λ}{fc : FC Σ rt Λ Ξ}
        → FCEval ƛ v ξ fc
        → FCGoto v ξ (fc ∷ ƛ) here!

      gotoThere : ∀{Λ}{ƛ : LS Λ}{Ξ′}{fc : FC Σ rt Λ Ξ′}{l : Ξ ∈ Λ}
        → FCGoto v ξ ƛ l
        → FCGoto v ξ (fc ∷ ƛ) (there l)



{- The following approach fails due to an UNIVERSE CONFLICT

module _ (Σ : Sig) (rt : Type) where

  LS : Labels → Set₁
  LS = List.All λ Ξ → MS Ξ → Val rt → Set

  data FCEval {Λ : Labels} {Ξ : MT} (ƛ : LS Λ) (ξ : MS Ξ) (v : Val rt) : FC Σ rt Λ Ξ → Set where

    evGoto : ∀{l R}
--          → List.All.lookup ƛ l ξ v
         → l ↦ R ∈ ƛ
         → R ξ v
         → FCEval (R ∷ ƛ) ξ v (fcGoto (here refl))

--     evGoto : ∀{l R}
-- --          → List.All.lookup ƛ l ξ v
--          → l ↦ R ∈ ƛ
--          → R ξ v
--          → FCEval ƛ ξ v (fcGoto l)

    evFix : ∀{fc}
          → FCEval ((λ ξ v → FCEval ƛ ξ v (fcFix fc)) ∷ ƛ) ξ v fc
          → FCEval ƛ ξ v (fcFix fc)

  -- data FCEval : ∀{Λ : Labels} {Ξ : MT} → FC Σ rt Λ Ξ → LS Λ → MS Ξ → Val rt → Set where

  --   evFix : ∀ ƛ ξ v fc
  --         → FCEval fc ((FCEval (fcFix fc) ƛ) ∷ ƛ) ξ v
  --         → FCEval (fcFix fc) ƛ ξ v

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

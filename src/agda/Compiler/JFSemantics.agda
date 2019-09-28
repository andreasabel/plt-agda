module Compiler.JFSemantics where

open import Library
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

-- Semantics of stack instructions

data StackIEval : ∀ {Φ Φ'} (j : StackI Φ Φ') (φ : Frame Φ) (φ' : Frame Φ') → Set where

  evConst : ∀{Φ t} {φ : Frame Φ} {v : Val` t}
    → StackIEval (const v) φ (just v ∷ φ)

  evDup : ∀{Φ t} {φ : Frame Φ} {v : Entry` t}
    → StackIEval dup (v ∷ φ) (v ∷ v ∷ φ)

  evPopVoid : ∀ {Φ} {φ : Frame Φ}
    → StackIEval (pop {t = void}) φ φ

  evPop : ∀ {Φ t} {φ : Frame Φ} {v : Entry` t}
    → StackIEval (pop {t = ` t}) (v ∷ φ) φ

  evArith : ∀{Φ t} {φ : Frame Φ} {v₁ v₂ v : Val` t} {op : ArithOp t}
    → v₁ ⟨ op ⟩ v₂ ⇓ᵃ v
    → StackIEval (arith op) (just v₂ ∷ just v₁ ∷ φ) (just v ∷ φ)

-- Semantics of store instructions

data StoreIEval {Γ} : ∀ {Φ Φ'} (j : StoreI Γ Φ Φ') (ξ : MS (Γ , Φ)) (ξ' : MS (Γ , Φ')) → Set where

  evStore : ∀ {Φ t x} {φ : Frame Φ} {γ γ'} {v : Val` t}
    → γ ⊢ x ≔ v ⇓ γ'
    → StoreIEval (store x) (γ , just v ∷ φ) (γ' , φ)

  evLoad : ∀ {Φ t x} {φ : Frame Φ} {γ} {v : Val` t}
    → γ ⊢ x ⇓ˣ v
    → StoreIEval (load x) (γ , φ) (γ , just v ∷ φ)

  evIncDec : ∀ {Φ b x} {φ : Frame Φ} {γ γ'}
    → γ ⊢ x ±=1 b ⇓ γ'
    → StoreIEval (incDec b x) (γ , φ) (γ' , φ)

-- Semantics of scope administration

data ScopeIEval : ∀{Γ Γ′} (adm : AdmScope Γ Γ′) (γ : Env Γ) (γ′ : Env Γ′) → Set where

  evNewBlock : ∀{Γ} {γ : Env Γ}
    → ScopeIEval newBlock γ ([] ∷ γ)

  evPopBlock : ∀{Γ Δ} {γ : Env Γ} {δ : Frame Δ}
    → ScopeIEval popBlock (δ ∷ γ) γ

  evDecl : ∀{Γ Δ t x} {γ : Env Γ} {δ : Frame Δ}
    → ScopeIEval (decl {t = t} x) (δ ∷ γ) ((nothing ∷ δ) ∷ γ)

-- Semantics of conditions

data CondEval : ∀ {Φ Φ'} (c : Cond Φ Φ') (φ : Frame Φ) (φ' : Frame Φ') (b : Bool) → Set where

  evEqBoolTrue : ∀ {Φ} {φ : Frame Φ} {b : Bool}
    → CondEval (eqBool b) (just b ∷ φ) φ true

  evEqBoolFalse : ∀ {Φ} {φ : Frame Φ} {b : Bool}
    → CondEval (eqBool (not b)) (just b ∷ φ) φ false

  evCmp : ∀ {Φ t} {op : CmpOp t} {φ : Frame Φ} {v₁ v₂ : Val` t} {b : Bool}
    → v₁ ⟨ op ⟩ v₂ ⇓ᶜ b
    → CondEval (cmp op) (just v₂ ∷ just v₁ ∷ φ) φ b

  evCmpZero : ∀ {Φ} {op : CmpOp int} {φ : Frame Φ} {v : Val` int} {b : Bool}
    → v ⟨ op ⟩ (+ 0) ⇓ᶜ b
    → CondEval (cmpZero op) (just v ∷ φ) φ b


module _ {Σ : Sig} where

  --

  data CallIEval : ∀ {Φ Φ'} (j : CallI Σ Φ Φ') (φ : Frame Φ) (φ' : Frame Φ') → Set where

    -- evCall :
    --   → CallIEval (call f)

    -- evBuiltin :
    --   → δ ⊢ b ⇓ᵇ v
    --   → CallIEval (builtin b) (δ ++⁺ φ) (φ ▷ᵛ v)

  -- Small step operational semantics of jump-free instructions.
  -- A jf instruction relates two machine states (before and after the instruction).

  data JFEval : ∀ {Ξ Ξ'} (j : JF Σ Ξ Ξ') (ξ : MS Ξ) (ξ' : MS Ξ') → Set where

    evCallI : ∀{Γ Φ Φ'} {j : CallI Σ Φ Φ'} {γ : Env Γ} {φ : Frame Φ} {φ' : Frame Φ'}
      → CallIEval j φ φ'
      → JFEval (callI j) (γ , φ) (γ , φ')

    evStackI : ∀{Γ Φ Φ'} {j : StackI Φ Φ'} {γ : Env Γ} {φ : Frame Φ} {φ' : Frame Φ'}
      → StackIEval j φ φ'
      → JFEval (stackI j) (γ , φ) (γ , φ')

    evStoreI : ∀{Γ Φ Φ'} {j : StoreI Γ Φ Φ'} {ξ ξ'}
      → StoreIEval j ξ ξ'
      → JFEval (storeI j) ξ ξ'

    evScopeI : ∀{Γ Γ′ Φ} {adm : AdmScope Γ Γ′} {γ : Env Γ} {γ′ : Env Γ′} {φ : Frame Φ}
      → ScopeIEval adm γ γ′
      → JFEval (scopeI adm) (γ , φ) (γ′ , φ)

    evComment : ∀{Ξ} {ξ : MS Ξ} {rem}
      → JFEval (comment rem) ξ ξ

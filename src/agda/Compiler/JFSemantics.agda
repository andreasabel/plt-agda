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

-- A judgement for evaluating function calls

FunEvalT : Sig → Set₁
FunEvalT Σ = ∀ {Δ t} (δ : Frame Δ) (f : funType Δ t ∈ Σ) (v : Val t) → Set

module JFEvaluation {Σ : Sig} (_⊢_⇓ᶠ_ : FunEvalT Σ) where

  -- Evaluation of function calls, treating them as black box.

  data CallIEval : ∀ {Φ Φ'} (j : CallI Σ Φ Φ') (φ : Frame Φ) (φ' : Frame Φ') → Set where

    evCall : ∀ {Δ t} {f : (funType Δ t) ∈ Σ} {δ : Frame Δ} {v : Val t} {Φ} {φ : Frame Φ}
      → δ ⊢ f ⇓ᶠ v
      → CallIEval (call f) (δ List.All.++ φ) (φ ▷ᵛ v)

    evBuiltin : ∀ {Δ t} {b : Builtin (funType Δ t)} {δ : Vals Δ} {v : Val t} {Φ} {φ : Frame Φ}
      → δ ⊢ b ⇓ᵇ v
      → CallIEval (builtin b) (List.All.map just δ List.All.++ φ) (φ ▷ᵛ v)

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


  data JFsEval : ∀ {Ξ Ξ'} (j : JFs Σ Ξ Ξ') (ξ : MS Ξ) (ξ' : MS Ξ') → Set where

    [] : ∀{Ξ} {ξ : MS Ξ}
      → JFsEval [] ξ ξ

    _∷_ : ∀ {Ξ₁ Ξ₂ Ξ₃} {j : JF Σ Ξ₁ Ξ₂} {jfs : JFs Σ Ξ₂ Ξ₃} {ξ₁ : MS Ξ₁} {ξ₂ : MS Ξ₂} {ξ₃ : MS Ξ₃}
      → JFEval j ξ₁ ξ₂
      → JFsEval jfs ξ₂ ξ₃
      → JFsEval (j ∷ jfs) ξ₁ ξ₃

module _ {Σ : Sig} {_⊢_⇓ᶠ_ : FunEvalT Σ} (open JFEvaluation _⊢_⇓ᶠ_) where

  -- Evaluation of concatenation of JFs

  _++-ev_ :  ∀ {Ξ₁ Ξ₂ Ξ₃} {jfs : JFs Σ Ξ₁ Ξ₂} {jfs' : JFs Σ Ξ₂ Ξ₃} {ξ₁ : MS Ξ₁} {ξ₂ : MS Ξ₂} {ξ₃ : MS Ξ₃}
      → JFsEval jfs               ξ₁ ξ₂
      → JFsEval jfs'              ξ₂ ξ₃
      → JFsEval (jfs Seq.++ jfs') ξ₁ ξ₃
  []       ++-ev es' = es'
  (e ∷ es) ++-ev es' = e ∷ (es ++-ev es')


  -- Evaluation of stack operation before pop

  evStackIPop : ∀ {Γ t} {γ : Env Γ} {v : Entry` t} {Φ Φ'} {φ : Frame Φ} {φ' : Frame Φ'}
                  {j : StackI Φ (t ∷ Φ')}
    → StackIEval j               φ  (v ∷ φ')
    → JFsEval (stackIPop j) (γ , φ) (γ , φ')
  evStackIPop evConst     = []
  evStackIPop evDup       = []
  evStackIPop (evArith _) = evStackI evPop     ∷ evStackI evPop ∷ []
  evStackIPop evPop       = evStackI evPop     ∷ evStackI evPop ∷ []
  evStackIPop evPopVoid   = evStackI evPopVoid ∷ evStackI evPop ∷ []

  -- Evaluation of store operation before pop

  evStoreIPop : ∀ {Γ t} {γ γ' : Env Γ} {v} {Φ Φ'} {φ : Frame Φ} {φ' : Frame Φ'}
                  {j : StoreI Γ Φ (t ∷ Φ')}
    → StoreIEval j          (γ , φ) (γ' , v ∷ φ')
    → JFsEval (storeIPop j) (γ , φ) (γ' , φ')
  evStoreIPop (evStore x) = evStoreI (evStore x) ∷ evStackI evPop ∷ []
  evStoreIPop (evLoad  x) = []

  -- Correctness of optimizing sequencing

  _∷ᵒ-ev_ : ∀ {Ξ₁ Ξ₂ Ξ₃} {j : JF Σ Ξ₁ Ξ₂} {jfs : JFs Σ Ξ₂ Ξ₃} {ξ₁ : MS Ξ₁} {ξ₂ : MS Ξ₂} {ξ₃ : MS Ξ₃}
      → JFEval j ξ₁ ξ₂
      → JFsEval jfs ξ₂ ξ₃
      → JFsEval (j ∷ᵒ jfs) ξ₁ ξ₃
  -- No optimization:
  e ∷ᵒ-ev []                            = e ∷ []
  e ∷ᵒ-ev es@(evCallI  _           ∷ _) = e ∷ es
  e ∷ᵒ-ev es@(evStoreI _           ∷ _) = e ∷ es
  e ∷ᵒ-ev es@(evScopeI _           ∷ _) = e ∷ es
  e ∷ᵒ-ev es@(evStackI evConst     ∷ _) = e ∷ es
  e ∷ᵒ-ev es@(evStackI evDup       ∷ _) = e ∷ es
  e ∷ᵒ-ev es@(evStackI (evArith _) ∷ _) = e ∷ es
  -- Pop void:
  e ∷ᵒ-ev (evStackI evPopVoid     ∷ es) = e ∷ es
  -- Pop
  evStackI e ∷ᵒ-ev (evStackI evPop ∷ es) = evStackIPop e ++-ev es
  evStoreI e ∷ᵒ-ev (evStackI evPop ∷ es) = evStoreIPop e ++-ev es
  evComment  ∷ᵒ-ev (evStackI evPop ∷ es) = evStackI evPop ∷ evComment ∷ es
  -- Comment floating and merging:
  e@(evScopeI _) ∷ᵒ-ev   (evComment ∷ es) = evComment ∷ e ∷ es
  evComment      ∷ᵒ-ev   (evComment ∷ es) = evComment ∷ es
  -- No optimization (pop):
  e@(evCallI  _) ∷ᵒ-ev es@(evStackI evPop ∷ _) = e ∷ es
  e@(evScopeI _) ∷ᵒ-ev es@(evStackI evPop ∷ _) = e ∷ es
  -- No optimization (comment):
  e@(evCallI  _) ∷ᵒ-ev es@(evComment      ∷ _) = e ∷ es
  e@(evStackI _) ∷ᵒ-ev es@(evComment      ∷ _) = e ∷ es
  e@(evStoreI _) ∷ᵒ-ev es@(evComment      ∷ _) = e ∷ es

open JFEvaluation public

{-

  -- Smart constructors

  corr : ∀ {Γ t} {x : Var Γ t} {γ : Env Γ}{v : Val` t} {Φ} {φ : Frame Φ} {Ξ} {ξ : MS Ξ}
    → ∀ jfs
    → γ ⊢ x ⇓ˣ v
    → JFsEval jfs                      (γ , just v ∷ φ) ξ
    → JFsEval (storeI (load x) ∷ᵒ jfs) (γ , φ)          ξ
  corr []                  evX evJFs = evStoreI (evLoad evX) ∷ evJFs
  corr (callI     j ∷ jfs) evX evJFs = evStoreI (evLoad evX) ∷ evJFs
  corr (stackI    j ∷ jfs) evX evJFs = {!j!}
  corr (storeI    j ∷ jfs) evX evJFs = evStoreI (evLoad evX) ∷ evJFs
  corr (scopeI  adm ∷ jfs) evX evJFs = evStoreI (evLoad evX) ∷ evJFs
  corr (comment rem ∷ jfs) evX evJFs = evStoreI (evLoad evX) ∷ evJFs

-- -}
-- -}

module Compiler.JumpFreeInstructions where

open import Library -- renaming (⊆-lookup to weakLabel; ⊆-refl to !)
open import WellTypedSyntax
open import Value

-- Stack type
ST = Block

-- Machine state type
MT = Cxt × ST

-- Stack-only instructions

data StackI : (Φ Φ' : ST) → Set where
  const : ∀{Φ t} (v : Val` t) → StackI Φ (t ∷ Φ)
  dup   : ∀{Φ t} → StackI (t ∷ Φ) (t ∷ t ∷ Φ)
  pop   : ∀{Φ t} → StackI (Φ ▷ᵇ t) Φ
  arith : ∀{Φ t} (op : ArithOp t) → StackI (t ∷ t ∷ Φ) (t ∷ Φ)
  -- dcmp  : ∀{Φ} → StackI (double ∷ double ∷ Φ) (int ∷ Φ)

-- Store-manipulating instructions

data IncDec : Set where
  inc dec : IncDec

data StoreI (Γ : Cxt) : (Φ Φ' : ST) → Set where
  store  : ∀{Φ t} (x : Var Γ t) → StoreI Γ (t ∷ Φ) Φ
  load   : ∀{Φ t} (x : Var Γ t) → StoreI Γ Φ (t ∷ Φ)
  incDec : ∀{Φ} (b : IncDec) (x : Var Γ int) → StoreI Γ Φ Φ

-- Scope-manipulating instructions:
-- Create and destroy local variables.

data AdmScope : (Γ Γ' : Cxt) → Set where
  newBlock : ∀{Γ}              → AdmScope Γ        ([] ∷⁺ Γ)
  popBlock : ∀{Γ Δ}            → AdmScope (Δ ∷⁺ Γ) Γ
  decl     : ∀{Γ t} (x : Name) → AdmScope Γ        (Γ ▷ ` t)

-- Conditions for jumps

data Cond : (Φ Φ' : ST) → Set where
  cmp     : ∀{Φ t} (cmp : CmpOp t)   → Cond (t ∷ t ∷ Φ) Φ
  cmpZero : ∀{Φ}   (cmp : CmpOp int) → Cond (int ∷ Φ)   Φ
  eqBool  : ∀{Φ}   (b : Bool)        → Cond (bool ∷ Φ)  Φ

-- The following definitions are relative to a signature Σ of function symbols.

module _ (Σ : Sig) where

  -- Function calls

  data CallI : (Ξ Ξ' : MT) → Set where
    call    : ∀{Γ Φ Δ rt} (f : funType Δ rt ∈ Σ)       → CallI (Γ , Δ ++ Φ) (Γ , Φ ▷ᵇ rt)
    builtin : ∀{Γ Φ Δ rt} (b : Builtin (funType Δ rt)) → CallI (Γ , Δ ++ Φ) (Γ , Φ ▷ᵇ rt)

  -- Single jump-free instruction

  data JF : (Ξ Ξ' : MT) → Set where
    stackI  : ∀{Γ Φ Φ'} (j   : StackI   Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    storeI  : ∀{Γ Φ Φ'} (j   : StoreI Γ Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    scopeI  : ∀{Γ Γ' Φ} (adm : AdmScope Γ Γ') → JF (Γ , Φ) (Γ' , Φ)
    callI   : ∀{Ξ Ξ'}   (j   : CallI Ξ Ξ')    → JF Ξ Ξ'
    comment : ∀{Ξ}      (rem : List String)   → JF Ξ Ξ


-- Negating conditions

negCond : ∀{Φ Φ'} → Cond Φ Φ' → Cond Φ Φ'
negCond (cmp     op) = cmp     (negCmpOp op)
negCond (cmpZero op) = cmpZero (negCmpOp op)
negCond (eqBool  b)  = eqBool  (not b)

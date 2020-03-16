module Compiler.JumpFreeInstructions where

open import Library -- renaming (⊆-lookup to weakLabel; ⊆-refl to !)
open import WellTypedSyntax
open import Value

open Yoneda

-- Stack type
ST = Block

-- Machine state type
MT = Cxt × ST

-- Stack-only instructions

data StackI : (Φ Φ' : ST) → Set where
  const : ∀{Φ t} (v : Val` t)     → StackI Φ           (t ∷ Φ)
  dup   : ∀{Φ t}                  → StackI (t ∷ Φ)     (t ∷ t ∷ Φ)
  pop   : ∀{Φ t}                  → StackI (Φ ▷ᵇ t)    Φ
  arith : ∀{Φ t} (op : ArithOp t) → StackI (t ∷ t ∷ Φ) (t ∷ Φ)

StackIs = Seq StackI
StackK  = Yonedaʳ StackIs

-- Store-manipulating instructions

IncDec = IncrDecr int
pattern inc = incr int
pattern dec = decr int

data StoreI (Γ : Cxt) : (Φ Φ' : ST) → Set where
  store  : ∀{Φ t}            (x : Var Γ t)   → StoreI Γ (t ∷ Φ) Φ
  load   : ∀{Φ t}            (x : Var Γ t)   → StoreI Γ Φ       (t ∷ Φ)
  incDec : ∀{Φ} (b : IncDec) (x : Var Γ int) → StoreI Γ Φ       Φ

StoreIs = λ Γ → Seq (StoreI Γ)
StoreK  = λ Γ → Yonedaʳ (StoreIs Γ)

-- Scope-manipulating instructions:
-- Create and destroy local variables.

data AdmScope : (Γ Γ' : Cxt) → Set where
  newBlock : ∀{Γ}              → AdmScope Γ        ([] ∷⁺ Γ)
  popBlock : ∀{Γ Δ}            → AdmScope (Δ ∷⁺ Γ) Γ
  decl     : ∀{Γ t} (x : Name) → AdmScope Γ        (Γ ▷ ` t)

AdmScopes = Seq AdmScope

-- Conditions for jumps

data Cond : (Φ Φ' : ST) → Set where
  cmp     : ∀{Φ t} (cmp : CmpOp t)   → Cond (t ∷ t ∷ Φ) Φ
  cmpZero : ∀{Φ}   (cmp : CmpOp int) → Cond (int ∷ Φ)   Φ
  eqBool  : ∀{Φ}   (b : Bool)        → Cond (bool ∷ Φ)  Φ

-- The following definitions are relative to a signature Σ of function symbols.

module _ (Σ : Sig) where

  -- Function calls

  data CallI : (Φ Φ' : ST) → Set where
    call    : ∀{Φ Δ rt} (f : (funType Δ rt) ∈ Σ)     → CallI (Δ ++ Φ) (Φ ▷ᵇ rt)
    builtin : ∀{Φ Δ rt} (b : Builtin (funType Δ rt)) → CallI (Δ ++ Φ) (Φ ▷ᵇ rt)

  -- Single jump-free instruction

  data JF : (Ξ Ξ' : MT) → Set where
    callI   : ∀{Γ Φ Φ'} (j   : CallI    Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    stackI  : ∀{Γ Φ Φ'} (j   : StackI   Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    storeI  : ∀{Γ Φ Φ'} (j   : StoreI Γ Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    scopeI  : ∀{Γ Γ' Φ} (adm : AdmScope Γ Γ') → JF (Γ , Φ) (Γ' , Φ)
    comment : ∀{Ξ}      (rem : List String)   → JF Ξ Ξ

  -- data JFs : (Ξ Ξ' : MT) → Set where
  --   []  : ∀{Ξ} → JFs Ξ Ξ
  --   _∷_ : ∀{Ξ Ξ′ Ξ″} (j : JF Ξ Ξ′) (js : JFs Ξ′ Ξ″) → JFs Ξ Ξ″

  JFs = Seq JF
  JFK = Yonedaʳ JFs


-- Negating conditions

negCond : ∀{Φ Φ'} → Cond Φ Φ' → Cond Φ Φ'
negCond (cmp     op) = cmp     (negCmpOp op)
negCond (cmpZero op) = cmpZero (negCmpOp op)
negCond (eqBool  b)  = eqBool  (not b)

-- Optimizing sequences.

-- StackI followed by pop.

stackIPop' : ∀ {t Φ Φ'} (j : StackI Φ (t ∷ Φ')) → StackIs Φ Φ'
stackIPop'     (const v)  = []
stackIPop'     dup        = []
stackIPop' {t} pop        = pop ∷ pop {t = ` t} ∷ []
stackIPop' {t} (arith op) = pop {t = ` t} ∷ pop {t = ` t} ∷ []

stackIPopK : ∀ {t Φ Φ'} (j : StackI Φ (t ∷ Φ')) → StackK Φ Φ'
stackIPopK j = yonedaʳ (stackIPop' j)
  where open YonedaEmbedding {Hom = StackIs} Seq._++_

module _ {Σ : Sig} where

  stackIPop : ∀ {Γ t Φ Φ'} (j : StackI Φ (t ∷ Φ')) → JFs Σ (Γ , Φ) (Γ , Φ')
  stackIPop {Γ} = Seq.gmap (Γ ,_) stackI ∘ stackIPop'

  storeIPop : ∀ {Γ t Φ Φ'} (j : StoreI Γ Φ (t ∷ Φ')) → JFs Σ (Γ , Φ) (Γ , Φ')
  storeIPop (load x)     = []
  storeIPop (store x)    = storeI (store x) ∷ stackI pop ∷ []
  storeIPop (incDec b x) = stackI pop ∷ storeI (incDec b x) ∷ []

  -- Smart cons, doing peephole optimizations.

  _∷ᵒ_ : ∀{Ξ Ξ′ Ξ″} (j : JF Σ Ξ Ξ′) → JFs Σ Ξ′ Ξ″ → JFs Σ Ξ Ξ″
  j            ∷ᵒ jf@(callI _          ∷ _) = j ∷ jf
  j            ∷ᵒ jf@(storeI _         ∷ _) = j ∷ jf
  j            ∷ᵒ jf@(scopeI _         ∷ _) = j ∷ jf
  j            ∷ᵒ jf@(stackI (const _) ∷ _) = j ∷ jf
  j            ∷ᵒ jf@(stackI dup       ∷ _) = j ∷ jf
  j            ∷ᵒ jf@(stackI (arith _) ∷ _) = j ∷ jf
  j            ∷ᵒ (stackI (pop {t = void}) ∷ jf) = j ∷ jf
  (stackI  j)  ∷ᵒ (stackI (pop {t = ` t }) ∷ jf) = stackIPop j Seq.++ jf
  (storeI  j)  ∷ᵒ (stackI (pop {t = ` t }) ∷ jf) = storeIPop j Seq.++ jf
  (comment x)  ∷ᵒ (stackI (pop {t = ` t }) ∷ jf) = stackI pop ∷ comment x ∷ jf
  (comment x)  ∷ᵒ (comment y               ∷ jf) = comment (x ++ y) ∷ jf
  (scopeI adm) ∷ᵒ (comment x               ∷ jf) = comment x ∷ scopeI adm ∷ jf  -- HACK to join comments over "empty" instructions
  j ∷ᵒ jf = j ∷ jf

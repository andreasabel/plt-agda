-- Expressing control constructs in terms of labels and jumps.


open import Library renaming (⊆-lookup to weakLabel; ⊆-refl to !)
open import WellTypedSyntax
open import Value

module FlowChart where

-- As a first step, we use let and fix to deal with labels.
-- Flow charts are like statement lists.

-- Labels are numbers bounded by the number of available labels.
-- They are like de Bruijn indices.

-- A label represents the code after it,
-- starting in scope Γ.

-- infix 10 _⇛_

-- record LabelType' : Set where
--   constructor _⇛_
--   field Γ Γ' : Cxt

-- Stack type
ST = Block

-- Machine state type
MT = Cxt × ST

-- Labels are typed by the Machine state type at label definition point
LabelType = MT
Labels = List LabelType

-- Kripke structure: a world is a list of labels.
-- A future is an extension of this list.
-- We use more generally sublists (_⊆_), even though we need.

wk1 : ∀{lt} {Λ : Labels} → Λ ⊆ lt ∷ Λ
wk1 = ⊆-skip {A = LabelType} _ !

□ : (F : Labels → Set) → Labels → Set
□ F Λ = ∀ {Λ'} (ρ : Λ ⊆ Λ') → F Λ'

_□→_ : (F G : Labels → Set) → Labels → Set
(F □→ G) = □ λ Λ → F Λ → G Λ

_→̇_ : (F G : Labels → Set) → Labels → Set
F →̇ G = λ Λ → F Λ → G Λ

-- Comonad structure

-- _ ! : ∀{F Λ} (k : □ F Λ) → F Λ

_∙_ : ∀{F Λ} (k : □ F Λ) → □ (□ F) Λ
k ∙ ρ = λ ρ' → k (⊆-trans ρ ρ')

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

-- Scope-manipulating instructions
-- * Create and destroy local variables

data AdmScope : (Γ Γ' : Cxt) → Set where
  newBlock : ∀{Γ}   → AdmScope Γ        ([] ∷⁺ Γ)
  popBlock : ∀{Γ Δ} → AdmScope (Δ ∷⁺ Γ) Γ
  decl     : ∀{Γ t} → AdmScope Γ        (Γ ▷ ` t)

-- Conditions for jumps

data Cond : (Φ Φ' : ST) → Set where
  cmp    : ∀{Φ t} (cmp : CmpOp t) → Cond (t ∷ t ∷ Φ) Φ
  eqBool : ∀{Φ}   (b : Bool)      → Cond (bool ∷ Φ)  Φ
  eqZero : ∀{Φ}   (b : Bool)      → Cond (int ∷ Φ)   Φ


-- The following definitions are relative to a signature Σ of function symbols.

module _ (Σ : Sig) where

  data CallI : (Ξ Ξ' : MT) → Set where
    call    : ∀{Γ Φ Δ rt} (f : funType Δ rt ∈ Σ)       → CallI (Γ , Δ ++ Φ) (Γ , Φ ▷ᵇ rt)
    builtin : ∀{Γ Φ Δ rt} (b : Builtin (funType Δ rt)) → CallI (Γ , Δ ++ Φ) (Γ , Φ ▷ᵇ rt)

  -- Single jump-free instruction

  data JF : (Ξ Ξ' : MT) → Set where
    stackI  : ∀{Γ Φ Φ'} (j   : StackI   Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    storeI  : ∀{Γ Φ Φ'} (j   : StoreI Γ Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    scopeI  : ∀{Γ Γ' Φ} (adm : AdmScope Γ Γ') → JF (Γ , Φ) (Γ' , Φ)
    callI   : ∀{Ξ Ξ'}   (j   : CallI Ξ Ξ')    → JF Ξ Ξ'

  -- Within a method, the return type rt is fixed.

  module _ (rt : Type) where

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
      fcExec     : ∀{Ξ Ξ'} (j : JF Ξ Ξ') (fc : FC Λ Ξ') → FC Λ Ξ

    -- JVM-like instructions as pattern-synonyms.

    -- fcAdm : ∀{Γ Γ' Φ}(adm : ScopeI Γ Γ') (fc : FC Λ (Γ', Φ)) → FC Λ (Γ , Φ)
    pattern fcAdm j fc = fcExec (scopeI j) fc

    -- fcNewBlock : ∀{Γ}   (fc : FC Λ ([] ∷⁺ Γ)) → FC Λ Γ
    pattern fcNewBlock fc = fcAdm newBlock fc

    -- fcPopBlock : ∀{Γ Δ} (fc : FC Λ Γ) → FC Λ (Δ ∷⁺ Γ)
    pattern fcPopBlock fc = fcAdm popBlock fc

    -- fcDecl     : ∀{Γ t} (fc : FC Λ (Γ ▷ just t)) → FC Λ Γ
    pattern fcDecl fc = fcAdm decl fc

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

-- Negating conditions

negCond : ∀{Φ Φ'} → Cond Φ Φ' → Cond Φ Φ'
negCond (cmp op)   = cmp (negCmpOp op)
negCond (eqBool b) = eqBool (not b)
negCond (eqZero b) = eqZero (not b)

-- -}
-- -}
-- -}

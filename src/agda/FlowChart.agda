-- Expressing control constructs in terms of labels and jumps.


open import Library renaming (⊆-lookup to weakLabel)
open import WellTypedSyntax
open import Value

module FlowChart (Σ : Sig) where

-- As a first step, we use let and fix to deal with labels.
-- Flow charts are like statement lists.

-- Labels are numbers bounded by the number of available labels.
-- They are like de Bruijn indices.

-- A label represents the code after it,
-- starting in scope Γ.

infix 10 _⇛_

record LabelType' : Set where
  constructor _⇛_
  field Γ Γ' : Cxt

-- Stack type
ST = Block

-- Machine state type
MT = Cxt × ST
LabelType = MT
Labels = List LabelType

wk1 : ∀{lt : LabelType} {Λ} → Λ ⊆ lt ∷ Λ
wk1 = ⊆-skip ⊆-refl

□ : (F : Labels → Set) → Labels → Set
□ F Λ = ∀ {Λ'} (ρ : Λ ⊆ Λ') → F Λ'

_□→_ : (F G : Labels → Set) → Labels → Set
(F □→ G) = □ λ Λ → F Λ → G Λ

_→̇_ : (F G : Labels → Set) → Labels → Set
F →̇ G = λ Λ → F Λ → G Λ

_∙_ : ∀{F Λ} (k : □ F Λ) → □ (□ F) Λ
k ∙ ρ = λ ρ' → k (⊆-trans ρ ρ')

-- Stack-only instructions

data StackI : (Φ Φ' : ST) → Set where
  const : ∀{Φ} (t : Ty) (c : Val` t) → StackI Φ (t ∷ Φ)
  dup   : ∀{Φ t} → StackI (t ∷ Φ) (t ∷ t ∷ Φ)
  pop   : ∀{Φ t} → StackI (t ∷ Φ) Φ
  dcmp  : ∀{Φ} → StackI (double ∷ double ∷ Φ) (int ∷ Φ)
  arith : ∀{Φ t} (op : ArithOp t) → StackI (t ∷ t ∷ Φ) (t ∷ Φ)

-- Store-manipulating instructions

data IncDec : Set where
  inc dec : IncDec

data StoreI (Γ : Cxt) : (Φ Φ' : ST) → Set where
  store  : ∀{Φ t} (x : Var Γ t) → StoreI Γ (t ∷ Φ) Φ
  load   : ∀{Φ t} (x : Var Γ t) → StoreI Γ Φ (t ∷ Φ)
  incDec : ∀{Φ} (b : IncDec) (x : Var Γ int) → StoreI Γ Φ Φ

-- -- Control-free instructions:
-- --
-- -- * No jumps.
-- -- * Can mutate local variables but not create them.
-- -- * Can manipulate the stack
--
-- data SI (Γ : Cxt) : (Φ Φ' : ST) → Set where
--   store  : ∀{Φ t} (x : Var Γ t) → SI Γ (t ∷ Φ) Φ
--   load   : ∀{Φ t} (x : Var Γ t) → SI Γ Φ (t ∷ Φ)
--   iconst : ∀{Φ} (i : ℤ) → SI Γ Φ (int ∷ Φ)
--   dconst : ∀{Φ} (d : Float) → SI Γ Φ (double ∷ Φ)
--   dup    : ∀{Φ t} → SI Γ (t ∷ Φ) (t ∷ t ∷ Φ)
--   pop    : ∀{Φ t} → SI Γ (t ∷ Φ) Φ
--   -- callProc : ∀{Φ Δ}   (f : funType Δ void ∈ Σ) → SI Γ (Δ ++ Φ) Φ
--   -- callFun  : ∀{Φ Δ t} (f : funType Δ (` t) ∈ Σ) → SI Γ (Δ ++ Φ) (t ∷ Φ)
--   call  : ∀{Φ Δ rt} (f : funType Δ rt ∈ Σ) → SI Γ (Δ ++ Φ) (Φ ▷ᵗ rt)
--   dcmp  : ∀{Φ} → SI Γ (double ∷ double ∷ Φ) (int ∷ Φ)
--   arith : ∀{Φ t} (op : ArithOp t) → SI Γ (t ∷ t ∷ Φ) (t ∷ Φ)
--   -- -- Embed some flow chart with local jumps
--   -- box   : FC [] Γ SI  -- This would require and ending context as well.

-- Scope-manipulating instructions
-- * Create and destroy local variables

data AdmScope : (Γ Γ' : Cxt) → Set where
  newBlock : ∀{Γ}   → AdmScope Γ        ([] ∷⁺ Γ)
  popBlock : ∀{Γ Δ} → AdmScope (Δ ∷⁺ Γ) Γ
  decl     : ∀{Γ} t → AdmScope Γ        (Γ ▷ just t)

-- Conditions for jumps

data Cond : (Φ Φ' : ST) → Set where
  cmp    : ∀{Φ t} (cmp : CmpOp t) → Cond (t ∷ t ∷ Φ) Φ
  eqBool : ∀{Φ}   (b : Bool)      → Cond (bool ∷ Φ)  Φ
  eqZero : ∀{Φ}   (b : Bool)      → Cond (int ∷ Φ)   Φ

-- Single jump-free instruction

data JF : (Ξ Ξ' : MT) → Set where
  stackI : ∀{Γ Φ Φ'} (j : StackI Φ Φ') → JF (Γ , Φ) (Γ , Φ')
  storeI : ∀{Γ Φ Φ'} (j : StoreI Γ Φ Φ') → JF (Γ , Φ) (Γ , Φ')
  scopeI : ∀{Γ Γ' Φ} (adm : AdmScope Γ Γ') → JF (Γ , Φ) (Γ' , Φ)
  call   : ∀{Γ Φ Δ rt} (f : funType Δ rt ∈ Σ) → JF (Γ , Δ ++ Φ) (Γ , Φ ▷ᵗ rt)

-- module _ (Σ : Sig) where
--   data JF : (Γ Γ' : Cxt) (Φ Φ' : ST) → Set where
--     stackI : ∀{Γ Φ Φ'} (j : StackI Φ Φ') → JF Γ Γ Φ Φ'
--     storeI : ∀{Γ Φ Φ'} (j : StoreI Γ Φ Φ') → JF Γ Γ Φ Φ'
--     scopeI : ∀{Γ Γ' Φ} (adm : AdmScope Γ Γ') → JF Γ Γ' Φ Φ
--     call   : ∀{Γ Φ Δ rt} (f : funType Δ rt ∈ Σ) → JF Γ Γ (Δ ++ Φ) (Φ ▷ᵗ rt)

-- Control

-- Ξ is machine state type when starting to run fc
data FC (Λ : Labels) : (Ξ : MT) → Set where
  -- Ends:
  fcGoto   : ∀{Ξ} (l : Ξ ∈ Λ) → FC Λ Ξ           -- goto join point (same Ξ)
  fcReturn : ∀{Γ Φ} t         → FC Λ (Γ , t ∷ Φ) -- return from function
  -- Branching:
  fcIfElse : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (fc fc' : FC Λ (Γ , Φ')) → FC Λ (Γ , Φ)
  -- Label definition
  fcLet    : ∀{Ξ Ξ'} (fc  : FC Λ Ξ') (fc' : FC (Ξ' ∷ Λ) Ξ) → FC Λ Ξ
  fcFix    : ∀{Ξ} (fc : FC (Ξ ∷ Λ) Ξ) → FC Λ Ξ
  -- Cons-like: Instruction
  fcExec     : ∀{Ξ Ξ'} (j : JF Ξ Ξ') (fc : FC Λ Ξ') → FC Λ Ξ

  -- Scope
  -- fcAdm      : ∀{Γ Γ'}(adm : AdmScope Γ Γ') (fc : FC Λ Γ') → FC Λ Γ
  -- fcNewBlock : ∀{Γ}   (fc : FC Λ ([] ∷⁺ Γ)) → FC Λ Γ
  -- fcPopBlock : ∀{Γ Δ} (fc : FC Λ Γ) → FC Λ (Δ ∷⁺ Γ)
  -- fcDecl     : ∀{Γ} t (fc : FC Λ (Γ ▷ just t)) → FC Λ Γ
  -- Instruction
  -- fcExec     : ∀{Ξ Ξ'} (j : JF Ξ Ξ') (fc : FC Λ Ξ') → FC Λ Ξ
  -- fcExec     : ∀{Γ} (j : JF Γ Γ' Φ Φ' ) (fc : FC Λ Γ) → FC Λ Γ
  -- fcExec     : ∀{Γ} (e : Eff Γ) (fc : FC Λ Γ) → FC Λ Γ

-- fcAdm : ∀{Γ Γ' Φ}(adm : ScopeI Γ Γ') (fc : FC Λ (Γ', Φ)) → FC Λ (Γ , Φ)
pattern fcAdm j fc = fcExec (scopeI j) fc
-- fcNewBlock : ∀{Γ}   (fc : FC Λ ([] ∷⁺ Γ)) → FC Λ Γ
pattern fcNewBlock fc = fcAdm newBlock fc
-- fcPopBlock : ∀{Γ Δ} (fc : FC Λ Γ) → FC Λ (Δ ∷⁺ Γ)
pattern fcPopBlock fc = fcAdm popBlock fc
-- fcDecl     : ∀{Γ} t (fc : FC Λ (Γ ▷ just t)) → FC Λ Γ
pattern fcDecl t   fc = fcAdm (decl t) fc

FC' : (Ξ : MT) (Λ : Labels) → Set
FC' Ξ Λ = FC Λ Ξ

_newLabel :  ∀{Λ Ξ Ξ'}
  → (f : □ (□ (FC' Ξ') →̇ FC' Ξ) Λ)
  → FC (Ξ' ∷ Λ) Ξ
_newLabel f = f wk1 λ ρ → fcGoto (weakLabel ρ (here refl))

joinPoint : ∀{Λ Ξ Ξ'}
  → (k : □ (FC' Ξ') Λ)
  → (f : □ (□ (FC' Ξ') →̇ FC' Ξ) Λ)
  → FC Λ Ξ
joinPoint k f = case k ⊆-refl of λ where
  (fcGoto _) → f ⊆-refl k
  k'         → fcLet k' $ f newLabel

fix : ∀{Ξ Λ}
  → (f : □ (□ (FC' Ξ) →̇ FC' Ξ) Λ)
  → FC Λ Ξ
fix f = fcFix $ f newLabel

{-

  module CompileStm where
   mutual

    -- Continuation k is not duplicable
    compileStm : ∀{rt Γ mt}
      (s : Stm Σ rt Γ mt) {Λ}
      (k : □ (FC' (Γ ▷ mt)) Λ)
      → FC Λ Γ
    compileStm (sReturn e)   k = fcReturn {!compileRet e!}
    compileStm (sExp e)      k = fcExec {!compileEff e!} (k ⊆-refl)
    compileStm (sInit {t} e) k = fcDecl t {!compileAss e!}

    compileStm (sBlock ss) k =
      fcNewBlock $ compileStms ss λ ρ →
      fcPopBlock $ k ρ

    compileStm (sWhile e s) k = fix λ ρ kstart →
      compileIf e (λ ρ' → compileStm s (kstart ∙ ρ'))
                  (k ∙ ρ)

    compileStm (sIfElse e s s') k =
      joinPoint k λ ρ k' →
      compileIf e (compileStm s  ∘ (k' ∙_))
                  (compileStm s' ∘ (k' ∙_))

    -- Compiling statements

    compileStms : ∀{rt Γ Δ Δ'}
      (ss : Stms Σ rt Γ Δ Δ') {Λ}
      (k : □ (FC' (Δ' ∷ Γ)) Λ)
      → FC Λ (Δ ∷ Γ)
    compileStms []       k = k ⊆-refl
    compileStms (s ∷ ss) k =
      compileStm  s  λ ρ →
      compileStms ss λ ρ' →
      k (⊆-trans ρ ρ')

    -- Compiling conditionals

    compileIf : ∀{Γ}
      (e : Exp` Σ Γ bool) {Λ}
      (kt kf : □ (FC' Γ) Λ)  -- kt: true, kf: false
      → FC' Γ Λ

    compileIf (eBool false) kt kf = kf ⊆-refl
    compileIf (eBool true) kt kf = kt ⊆-refl

    compileIf (eOp (logic and) e e') kt kf =
      joinPoint kf λ ρ kf' →
      compileIf e (λ ρ' → compileIf e' (kt ∙ ⊆-trans ρ ρ')
                                       (kf' ∙ ρ'))
                  kf'

    compileIf (eOp (logic or) e e') kt kf =
      joinPoint kt λ ρ kt' →
      compileIf e kt' λ ρ' →
      compileIf e' (kt' ∙ ρ') (kf ∙ ⊆-trans ρ ρ')

    compileIf (eOp (cmp op) e e') kt kf = {!!}

    -- General boolean expressions:
    compileIf (eVar x)    kt kf = {!!}
    compileIf (eApp f es) kt kf = {!!}
    compileIf (eAss x e)  kt kf = {!!}

    -- Impossible cases:
    compileIf (eBuiltin () es) kt kf
    compileIf (eIncrDecr p (incr ()) x) kt kf
    compileIf (eIncrDecr p (decr ()) x) kt kf
    compileIf (eOp (arith (plus ())) e e') kt kf
    compileIf (eOp (arith (minus ())) e e') kt kf
    compileIf (eOp (arith (times ())) e e') kt kf
    compileIf (eOp (arith (div ())) e e') kt kf

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

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
wk1 = ⊆-skip !

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
  const : ∀{Φ t} (c : Val t) → StackI Φ (Φ ▷ᵇ t)
  dup   : ∀{Φ t} → StackI (t ∷ Φ) (t ∷ t ∷ Φ)
  pop   : ∀{Φ t} → StackI (Φ ▷ᵇ t) Φ
  dcmp  : ∀{Φ} → StackI (double ∷ double ∷ Φ) (int ∷ Φ)
  arith : ∀{Φ t} (op : ArithOp t) → StackI (t ∷ t ∷ Φ) (t ∷ Φ)

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

  -- Single jump-free instruction

  data JF : (Ξ Ξ' : MT) → Set where
    stackI  : ∀{Γ Φ Φ'} (j : StackI Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    storeI  : ∀{Γ Φ Φ'} (j : StoreI Γ Φ Φ') → JF (Γ , Φ) (Γ , Φ')
    scopeI  : ∀{Γ Γ' Φ} (adm : AdmScope Γ Γ') → JF (Γ , Φ) (Γ' , Φ)
    call    : ∀{Γ Φ Δ rt} (f :       funType Δ rt ∈ Σ) → JF (Γ , Δ ++ʳ Φ) (Γ , Φ ▷ᵇ rt)
    builtin : ∀{Γ Φ Δ rt} (b : Builtin (funType Δ rt)) → JF (Γ , Δ ++ʳ Φ) (Γ , Φ ▷ᵇ rt)

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

    FC' : (Ξ : MT) (Λ : Labels) → Set
    FC' Ξ Λ = FC Λ Ξ

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

    pattern fcCall    f fc = fcExec (call    f) fc
    pattern fcBuiltin f fc = fcExec (builtin f) fc

    -- Continue something at the latest introduced label.

    _newLabel :  ∀{Λ Ξ Ξ'}
      → (f : □ (□ (FC' Ξ') →̇ FC' Ξ) Λ)
      → FC (Ξ' ∷ Λ) Ξ
    _newLabel f = f wk1 λ ρ → fcGoto (weakLabel ρ (here refl))

    -- Provide a duplicable version of a continuation,
    -- introducing a new label if necessary.

    joinPoint : ∀{Λ Ξ Ξ'}
      → (k : □ (FC' Ξ') Λ)
      → (f : □ (□ (FC' Ξ') →̇ FC' Ξ) Λ)
      → FC Λ Ξ
    joinPoint k f = case k ! of λ where
      (fcGoto _) → f ! k
      k'         → fcLet k' $ f newLabel

    -- Define a label at the current position
    -- as a target to go back to (e.g. in a while loop).

    fix : ∀{Ξ Λ}
      → (f : □ (□ (FC' Ξ) →̇ FC' Ξ) Λ)
      → FC Λ Ξ
    fix f = fcFix $ f newLabel

    -- Compilation of expressions and conditionals.

    mutual

      -- Compiling expressions.

      compileExp : ∀{Γ t}
        (e : Exp Σ Γ t)          {Λ Φ}
        (k : □ (FC' (Γ , Φ ▷ᵇ t)) Λ)
        → FC' (Γ , Φ) Λ
      compileExp (eConst v)  k = fcConst v (k !)
      compileExp (eVar x)    k = fcLoad x (k !)
      compileExp (eAss x e)  k = compileExp e $ fcDup ∘ fcAssign x ∘ k

      compileExp (eIncrDecr pre  (incr int)    x) k = fcIncDec inc x $ fcLoad x $ k !
      compileExp (eIncrDecr pre  (decr int)    x) k = fcIncDec dec x $ fcLoad x $ k !
      compileExp (eIncrDecr post (incr int)    x) k = fcLoad x $ fcIncDec inc x $ k !
      compileExp (eIncrDecr post (decr int)    x) k = fcLoad x $ fcIncDec dec x $ k !

      compileExp (eIncrDecr pre  (incr double) x) k = fcLoad x $ fcConst 1.0 $ fcAdd double $ fcDup $ fcAssign x $ k !
      compileExp (eIncrDecr pre  (decr double) x) k = fcLoad x $ fcConst 1.0 $ fcSub double $ fcDup $ fcAssign x $ k !
      compileExp (eIncrDecr post (incr double) x) k = fcLoad x $ fcDup $ fcConst 1.0 $ fcAdd double $ fcAssign x $ k !
      compileExp (eIncrDecr post (decr double) x) k = fcLoad x $ fcDup $ fcConst 1.0 $ fcSub double $ fcAssign x $ k !

      compileExp (eOp (arith op) e e') k = compileExp e $ compileExp e' ∘ ((fcArith op ∘ k) ∙_)
      compileExp (eOp (cmp   op) e e') k = compileBoolOp (cmp   op) e e' k
      compileExp (eOp (logic op) e e') k = compileBoolOp (logic op) e e' k

      compileExp (eApp     f es) k = compileExps es $ fcCall    f ∘ k
      compileExp (eBuiltin f es) k = compileExps es $ fcBuiltin f ∘ k

      -- Compiling expression list.
      -- First value ends up first on the stack.

      compileExps : ∀{Γ Δ}
        (es : Exps Σ Γ Δ)          {Λ Φ}
        (k : □ (FC' (Γ , Δ ++ʳ Φ)) Λ)
        → FC' (Γ , Φ) Λ

      compileExps []       k = k !
      compileExps (e ∷ es) k = compileExp e λ ρ → compileExps es λ ρ' → k (⊆-trans ρ ρ')

      -- Compiling conditionals.

      compileIf : ∀{Γ}
        (e : Exp` Σ Γ bool) {Λ Φ}
        (kt kf : □ (FC' (Γ , Φ)) Λ)  -- kt: true, kf: false
        → FC' (Γ , Φ) Λ

      compileIf (eConst false) kt kf = kf !
      compileIf (eConst true ) kt kf = kt !
      compileIf (eOp op e e')  kt kf = compileIfOp op e e' kt kf

      -- General boolean expressions:
      compileIf e@(eVar _  ) kt kf = compileExp e λ ρ → fcIfElse (eqBool true) (kt ρ) (kf ρ)
      compileIf e@(eApp _ _) kt kf = compileExp e λ ρ → fcIfElse (eqBool true) (kt ρ) (kf ρ)
      compileIf e@(eAss _ _) kt kf = compileExp e λ ρ → fcIfElse (eqBool true) (kt ρ) (kf ρ)

      -- Impossible cases:
      compileIf (eBuiltin () es) kt kf
      compileIf (eIncrDecr p (incr ()) x) kt kf
      compileIf (eIncrDecr p (decr ()) x) kt kf

      -- Compiling composite conditionals.

      compileIfOp : ∀{Γ t}
        (op   : Op t bool)
        (e e' : Exp` Σ Γ t) {Λ Φ}
        (kt kf : □ (FC' (Γ , Φ)) Λ)  -- kt: true, kf: false
        → FC' (Γ , Φ) Λ

      -- if (e and e') kt kf = if e (if e' kt kf) kf
      compileIfOp (logic and) e e' kt kf =
        joinPoint kf λ ρ kf' →
        compileIf e (λ ρ' → compileIf e' (kt ∙ ⊆-trans ρ ρ')
                                         (kf' ∙ ρ'))
                    kf'

      -- if (e or e') kt kf = if e kt (if e' kt kf)
      compileIfOp (logic or) e e' kt kf =
        joinPoint kt λ ρ kt' →
        compileIf e kt' λ ρ' →
        compileIf e' (kt' ∙ ρ') (kf ∙ ⊆-trans ρ ρ')

      compileIfOp (cmp op) e e' kt kf =
        compileExp e  λ ρ  →
        compileExp e' λ ρ' →
        fcIfElse (cmp op) (kt (⊆-trans ρ ρ'))
                          (kf (⊆-trans ρ ρ'))

      -- Impossible cases:
      compileIfOp (arith (plus  ()))
      compileIfOp (arith (minus ()))
      compileIfOp (arith (times ()))
      compileIfOp (arith (div   ()))

      -- Compiling boolean operators.

      compileBoolOp : ∀{Γ t}
        (op   : Op t bool)
        (e e' : Exp` Σ Γ t) {Λ Φ}
        (k : □ (FC' (Γ , bool ∷ Φ)) Λ)
        → FC' (Γ , Φ) Λ
      compileBoolOp op e e' k =
        joinPoint k λ ρ k' →
        compileIfOp op e e' (fcConst true ∘ k') (fcConst false ∘ k')


    -- Compilation of statements.

    mutual

      -- Continuation k is not duplicable in general!

      compileStm : ∀{Γ mt}
        (s : Stm Σ rt Γ mt)         {Λ Φ}
        (k : □ (FC' (Γ ▷ mt , Φ)) Λ)
        → FC' (Γ , Φ) Λ

      compileStm (sReturn e)      k = compileExp e λ ρ → fcReturn
      compileStm (sExp e)         k = compileExp e $ fcPop ∘ k

      compileStm (sInit nothing)  k = fcDecl (k !)
      compileStm (sInit (just e)) k = compileExp e $
        fcDecl ∘ fcAssign vzero ∘ k

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

      -- Compiling statements.

      compileStms : ∀{Γ Δ Δ'}
        (ss : Stms Σ rt Γ Δ Δ') {Λ Φ}
        (k : □ (FC' (Δ' ∷ Γ , Φ)) Λ)
        → FC' (Δ ∷ Γ , Φ) Λ
      compileStms []       k = k !
      compileStms (s ∷ ss) k =
        compileStm  s  λ ρ →
        compileStms ss λ ρ' →
        k (⊆-trans ρ ρ')

-- Method

Meth : (Σ : Sig) (ft : FunType) → Set
Meth Σ (funType Δ rt) = FC Σ rt [] (Δ ∷ [] , [])

-- If the statements do not end in returns,
-- a default value will be returned.

compileDef : ∀{Σ ft} → Def Σ ft → Meth Σ ft
compileDef {Σ} {funType Δ rt} (_ , ss) =
  compileStms Σ rt ss λ ρ → fcConst (defaultVal rt) fcReturn

-- Methods

Meths : (Σ Σ' : Sig) → Set
Meths Σ = List.All (Meth Σ)

compilePrg : ∀{Σ Σ'} → Prg Σ Σ' → Meths Σ Σ'
compilePrg = List.All.map compileDef

-- Class

Class : (Σ : Sig) → Set
Class = Program' Meths

compileProgram : ∀{Σ} → Program Σ → Class Σ
compileProgram (program prg main) = program (compilePrg prg) main

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

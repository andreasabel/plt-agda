module CompileToFC where

open import Library renaming (⊆-lookup to weakLabel; ⊆-refl to !)
open import WellTypedSyntax
open import Value
open import FlowChart

module _ (Σ : Sig) (rt : Type) where

  FC' : (Ξ : MT) (Λ : Labels) → Set
  FC' Ξ Λ = FC Σ rt Λ Ξ

  -- Continue something at the latest introduced label.

  _newLabel :  ∀{Λ Ξ Ξ'}
    → (f : □ (□ (FC' Ξ') →̇ FC' Ξ) Λ)
    → FC' Ξ (Ξ' ∷ Λ)
  _newLabel f = f wk1 λ ρ → fcGoto (weakLabel ρ (here refl))

  -- Provide a duplicable version of a continuation,
  -- introducing a new label if necessary.

  joinPoint : ∀{Λ Ξ Ξ'}
    → (k : □ (FC' Ξ') Λ)
    → (f : □ (□ (FC' Ξ') →̇ FC' Ξ) Λ)
    → FC' Ξ Λ
  joinPoint k f = case k ! of λ where
    (fcGoto _) → f ! k
    k'         → fcLet k' $ f newLabel

  -- Define a label at the current position
  -- as a target to go back to (e.g. in a while loop).

  fix : ∀{Ξ Λ}
    → (f : □ (□ (FC' Ξ) →̇ FC' Ξ) Λ)
    → FC' Ξ Λ
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
      (k : □ (FC' (Γ , Δ ++ Φ)) Λ)
      → FC' (Γ , Φ) Λ

    compileExps []       k = k !
    compileExps (e ∷ es) k = compileExps es λ ρ → compileExp e λ ρ' → k (⊆-trans ρ ρ')

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

fcDefaultReturn : ∀ {Σ Λ Ξ} rt → FC Σ rt Λ Ξ
fcDefaultReturn (` t) = fcConst (defaultVal` t) fcReturn
fcDefaultReturn void  = fcReturn

compileDef : ∀{Σ ft} → Def Σ ft → Meth Σ ft
compileDef {Σ} {funType Δ rt} (Γ , ss) =
  compileStms Σ rt ss λ ρ → fcDefaultReturn rt

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

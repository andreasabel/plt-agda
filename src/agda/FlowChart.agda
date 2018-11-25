-- Expressing control constructs in terms of labels and jumps.


open import Library
open import WellTypedSyntax

module FlowChart (Σ : Sig) where

-- As a first step, we use let and fix to deal with labels.
-- Flow charts are like statement lists.

-- Labels are numbers bounded by the number of available lables.
-- They are like de Bruijn indices.

-- A label represents the code after it,
-- starting in scope Γ and ending in scope Γ'.

record LabelType : Set where
  constructor _⇛_
  field Γ Γ' : Cxt

Labels = List LabelType

module _ (Ret Cond Eff : Cxt → Set) where

  data FC (Λ : Labels) : (Γ Γ' : Cxt) → Set where
    -- Ends:
    fcGoto   : ∀{Γ Γ'} (l : (Γ ⇛ Γ') ∈ Λ) → FC Λ Γ Γ'  -- goto join point
    fcReturn : ∀{Γ Γ'} (r : Ret Γ) → FC Λ Γ Γ'      -- return from function
    -- Branching:
    fcIfElse : ∀{Γ} (c : Cond Γ) (fc fc' : FC Λ Γ Γ) → FC Λ Γ Γ
    -- Label definition
    fcLet    : ∀{Γ Γ' Γ₁ Γ₂} (fc : FC Λ Γ₁ Γ₂) (fc' : FC ((Γ₁ ⇛ Γ₂) ∷ Λ) Γ Γ') → FC Λ Γ Γ'
    fcFix    : ∀{Γ Γ'} (fc : FC ((Γ ⇛ Γ) ∷ Λ) Γ Γ') → FC Λ Γ Γ'
    -- Cons-like:
    -- Scope
    fcNewBlock : ∀{Γ Γ'} (fc : FC Λ ([] ∷⁺ Γ) Γ') → FC Λ Γ Γ'
    fcPopBlock : ∀{Γ Γ' Δ} (fc : FC Λ Γ Γ') → FC Λ (Δ ∷⁺ Γ) Γ'
    fcDecl     : ∀{Γ Γ'} {t : Ty} (fc : FC Λ (Γ ▷ just t) Γ') → FC Λ Γ Γ'
    -- Instruction
    fcExec     : ∀{Γ Γ'} (e : Eff Γ) (fc : FC Λ Γ Γ') → FC Λ Γ Γ'

  joinPoint : ∀{Λ Γ Γ' Γ₁ Γ₂}
    → (k : ∀{Λ'} (ρ : Λ ⊆ Λ') → FC Λ' Γ₁ Γ₂)
    → (f : ∀{Λ'} (ρ : Λ ⊆ Λ') (k : ∀{Λ''} (ρ' : Λ' ⊆ Λ'') → FC Λ'' Γ₁ Γ₂) → FC Λ' Γ Γ')
    → FC Λ Γ Γ'
  joinPoint k f = case k ⊆-refl of λ where
    (fcGoto _) → f ⊆-refl k
    k'         → fcLet k' (f (⊆-skip ⊆-refl) (λ ρ → fcGoto {!!}))
  -- joinPoint : ∀{Λ Γ Γ' C} (fc : FC Λ Γ Γ') (k : FC Λ Γ Γ' → C) → C
  -- joinPoint (fcGoto l) = {!!}

  module CompileStm where
   mutual
    -- Continuation k is not duplicable
    compileStm : ∀{rt Γ Γ' mt}
      (s : Stm Σ rt Γ mt) {Λ}
      (k : ∀{Λ'} (ρ : Λ ⊆ Λ') → FC Λ' (Γ ▷ mt) Γ')
      → FC Λ Γ Γ'
    compileStm (sReturn e) k = fcReturn {!compileRet e!}
    compileStm (sExp e)    k = fcExec {!compileEff e!} (k ⊆-refl)
    compileStm (sInit e)   k = fcDecl {!compileAss e!}
    compileStm (sBlock ss) k = fcNewBlock (compileStms ss λ ρ → fcPopBlock (k ρ))
    compileStm (sWhile e s) k = fcFix
      (let Lstart = (here refl)
       in  compileIf e (compileStm s λ ρ → fcGoto {!Lstart ρ!}) (k (⊆-skip ⊆-refl)))
      -- fcLet (k ⊆-refl) (fcFix
      -- (let start = fcGoto (here refl)
      --      done  = fcGoto (there (here refl))
      --  in  compileIf e (compileStm s λ ρ → {!start!}) done))
    compileStm (sIfElse e s s') k = joinPoint k λ ρ k' →
        compileIf e (compileStm s  k')
                    (compileStm s' k')
      -- fcLet (k ⊆-refl) (let join = fcGoto (here refl) in
      --   compileIf e (compileStm s  λ ρ → {!join !})
      --               (compileStm s' λ ρ → {!join !}))

    compileStms : ∀{rt Γ Δ Δ' Γ'}
      (ss : Stms Σ rt Γ Δ Δ') {Λ}
      (k : ∀{Λ'} (ρ : Λ ⊆ Λ') → FC Λ' (Δ' ∷ Γ) Γ')
      → FC Λ (Δ ∷ Γ) Γ'
    compileStms []       k = k ⊆-refl
    compileStms (s ∷ ss) k =
      compileStm  s  λ ρ →
      compileStms ss λ ρ' →
      k (⊆-trans ρ ρ')

    compileIf : ∀{Γ Γ'}
      (e : Exp` Σ Γ bool) {Λ}
      (kt kf : FC Λ Γ Γ')  -- k: true, kf: false
      -- (kt kf : ∀{Λ'} (ρ : Λ ⊆ Λ') → FC Λ Γ Γ')
      → FC Λ Γ Γ'
    compileIf (eBool false) kt kf = kf
    compileIf (eBool true) kt kf = kt
    compileIf (eVar x) kt kf = {!!}
    compileIf (eApp f es) kt kf = {!!}
    compileIf (eBuiltin () es) kt kf
    compileIf (eIncrDecr p (incr ()) x) kt kf
    compileIf (eIncrDecr p (decr ()) x) kt kf
    compileIf (eOp (arith (plus ())) e e') kt kf
    compileIf (eOp (arith (minus ())) e e') kt kf
    compileIf (eOp (arith (times ())) e e') kt kf
    compileIf (eOp (arith (div ())) e e') kt kf
    compileIf (eOp (cmp op) e e') kt kf = {!!}
    compileIf (eOp (logic and) e e') kt kf =
      joinPoint kf λ ρ kf' → {!!}
    compileIf (eOp (logic or) e e') kt kf = {!!}
    compileIf (eAss x e) kt kf = {!!}

-- Expressing control constructs in terms of labels and jumps.


open import Library renaming (⊆-lookup to weakLabel)
open import WellTypedSyntax

module FlowChart (Σ : Sig) where

-- As a first step, we use let and fix to deal with labels.
-- Flow charts are like statement lists.

-- Labels are numbers bounded by the number of available lables.
-- They are like de Bruijn indices.

-- A label represents the code after it,
-- starting in scope Γ and ending in scope Γ'.

infix 10 _⇛_

record LabelType : Set where
  constructor _⇛_
  field Γ Γ' : Cxt

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


module _ (Ret Cond Eff : Cxt → Set) where

  data FC (Λ : Labels) : (Γ Γ' : Cxt) → Set where
    -- Ends:
    fcGoto   : ∀{Γ Γ'} (l : (Γ ⇛ Γ') ∈ Λ) → FC Λ Γ Γ'  -- goto join point
    fcReturn : ∀{Γ Γ'} (r : Ret Γ) → FC Λ Γ Γ'      -- return from function
    -- Branching:
    fcIfElse : ∀{Γ Γ'} (c : Cond Γ) (fc fc' : FC Λ Γ Γ') → FC Λ Γ Γ'
    -- Label definition
    fcLet    : ∀{Γ Γ' Γ₁ Γ₂} (fc  : FC Λ Γ₁ Γ₂)
                             (fc' : FC ((Γ₁ ⇛ Γ₂) ∷ Λ) Γ Γ') → FC Λ Γ Γ'
    fcFix    : ∀{Γ Γ'} (fc : FC ((Γ ⇛ Γ') ∷ Λ) Γ Γ') → FC Λ Γ Γ'
    -- Cons-like:
    -- Scope
    fcNewBlock : ∀{Γ Γ'}   (fc : FC Λ ([] ∷⁺ Γ) Γ') → FC Λ Γ Γ'
    fcPopBlock : ∀{Γ Γ' Δ} (fc : FC Λ Γ Γ') → FC Λ (Δ ∷⁺ Γ) Γ'
    fcDecl     : ∀{Γ Γ' t} (fc : FC Λ (Γ ▷ just t) Γ') → FC Λ Γ Γ'
    -- Instruction
    fcExec     : ∀{Γ Γ'} (e : Eff Γ) (fc : FC Λ Γ Γ') → FC Λ Γ Γ'

  FC' : (Γ Γ' : Cxt) (Λ : Labels) → Set
  FC' Γ Γ' Λ = FC Λ Γ Γ'

  _newLabel :  ∀{Λ Γ Γ' Γ₁ Γ₂}
    → (f : □ (□ (FC' Γ₁ Γ₂) →̇ FC' Γ Γ') Λ)
    → FC ((Γ₁ ⇛ Γ₂) ∷ Λ) Γ Γ'
  _newLabel f = f wk1 λ ρ → fcGoto (weakLabel ρ (here refl))

  -- continueAtNewLabel :  ∀{Λ Γ Γ' Γ₁ Γ₂}
  --   → (f : □ (□ (FC' Γ₁ Γ₂) →̇ FC' Γ Γ') Λ)
  --   → FC ((Γ₁ ⇛ Γ₂) ∷ Λ) Γ Γ'
  -- continueAtNewLabel f =
  --   f wk1 λ ρ → fcGoto (weakLabel ρ (here refl))

  joinPoint : ∀{Λ Γ Γ' Γ₁ Γ₂}
    → (k : □ (FC' Γ₁ Γ₂) Λ)
    → (f : □ (□ (FC' Γ₁ Γ₂) →̇ FC' Γ Γ') Λ)
    → FC Λ Γ Γ'
  joinPoint k f = case k ⊆-refl of λ where
    (fcGoto _) → f ⊆-refl k
    k'         → fcLet k' $ f newLabel
    -- k'         → fcLet k' $ continueAtNewLabel f

  fix : ∀{Γ Γ' Λ}
    → (f : □ (□ (FC' Γ Γ') →̇ FC' Γ Γ') Λ)
    → FC Λ Γ Γ'
  fix f = fcFix $ f newLabel
  -- fix f = fcFix $ continueAtNewLabel f

  module CompileStm where
   mutual

    -- Continuation k is not duplicable
    compileStm : ∀{rt Γ Γ' mt}
      (s : Stm Σ rt Γ mt) {Λ}
      (k : □ (FC' (Γ ▷ mt) Γ') Λ)
      → FC Λ Γ Γ'
    compileStm (sReturn e) k = fcReturn {!compileRet e!}
    compileStm (sExp e)    k = fcExec {!compileEff e!} (k ⊆-refl)
    compileStm (sInit e)   k = fcDecl {!compileAss e!}

    compileStm (sBlock ss) k =
      fcNewBlock $ compileStms ss λ ρ →
      fcPopBlock $ k ρ

    compileStm (sWhile e s) k = fix λ ρ kstart →
      compileIf e (λ ρ' → compileStm s (kstart ∙ ρ'))
                  (k ∙ ρ)

    -- compileStm (sWhile e s) k = fix λ ρ kstart →
    --   compileIf e (λ ρ' → compileStm s λ ρ'' →  kstart {!(⊆-trans ρ' ρ'')!}  )
    --               (λ ρ' → k ρ') ρ
    -- compileStm (sWhile e s) k = fcFix
    --   (let Lstart = (here refl)
    --    in  compileIf e (compileStm s λ ρ → fcGoto (weakLabel ρ Lstart))
    --                    (k (⊆-skip ⊆-refl)))

    compileStm (sIfElse e s s') k =
      joinPoint k λ ρ k' →
      compileIf e (compileStm s  ∘ (k' ∙_))
                  (compileStm s' ∘ (k' ∙_))

    -- Compiling statements

    compileStms : ∀{rt Γ Δ Δ' Γ'}
      (ss : Stms Σ rt Γ Δ Δ') {Λ}
      (k : □ (FC' (Δ' ∷ Γ) Γ') Λ)
      → FC Λ (Δ ∷ Γ) Γ'
    compileStms []       k = k ⊆-refl
    compileStms (s ∷ ss) k =
      compileStm  s  λ ρ →
      compileStms ss λ ρ' →
      k (⊆-trans ρ ρ')

    -- Compiling conditionals

    compileIf : ∀{Γ Γ'}
      (e : Exp` Σ Γ bool) {Λ}
      (kt kf : □ (FC' Γ Γ') Λ)  -- kt: true, kf: false
      → FC' Γ Γ' Λ

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


    -- compileIf : ∀{Γ Γ'}
    --   (e : Exp` Σ Γ bool) {Λ}

    --   (kt kf : □ (FC' Γ Γ') Λ)  -- kt: true, kf: false
    --   → □ (FC' Γ Γ') Λ
    -- compileIf (eBool false) kt kf = kf
    -- compileIf (eBool true) kt kf = kt
    -- compileIf (eVar x) kt kf = {!!}
    -- compileIf (eApp f es) kt kf = {!!}
    -- compileIf (eBuiltin () es) kt kf
    -- compileIf (eIncrDecr p (incr ()) x) kt kf
    -- compileIf (eIncrDecr p (decr ()) x) kt kf
    -- compileIf (eOp (arith (plus ())) e e') kt kf
    -- compileIf (eOp (arith (minus ())) e e') kt kf
    -- compileIf (eOp (arith (times ())) e e') kt kf
    -- compileIf (eOp (arith (div ())) e e') kt kf
    -- compileIf (eOp (cmp op) e e') kt kf = {!!}
    -- compileIf (eOp (logic and) e e') kt kf =
    --   {!joinPoint kf λ ρ kf' → {!!}!}
    -- compileIf (eOp (logic or) e e') kt kf = {!!}
    -- compileIf (eAss x e) kt kf = {!!}

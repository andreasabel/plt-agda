module Compiler.BasicBlocks where

open import Library
open import Library.AllExt

open import Value
open import WellTypedSyntax
open import InternalToAbstract

open import Compiler.JumpFreeInstructions public
open import Compiler.Labels               public
open import Compiler.FlowChart

module BBTypes (Σ : Sig) (rt : Type) where

  -- Basic blocks are flow charts without label definition

  mutual

    record BB (Λ : Labels) (Ξ : MT) : Set where
      inductive; constructor mkBB
      field
        {Ξ'}     : MT
        jumpFree : JFs Σ Ξ Ξ'
        controlI : BBCtrl Λ Ξ'

    data BBCtrl (Λ : Labels) : (Ξ : MT) → Set where
      -- Ends:
      bbGoto   : ∀{Ξ} (l : Ξ ∈ Λ) → BBCtrl Λ Ξ             -- goto join point (same Ξ)
      bbReturn : ∀{Γ Φ}           → BBCtrl Λ (Γ , Φ ▷ᵇ rt) -- return from function (stack is destroyed)
      -- Branching:
      bbIfElse : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (bb bb' : BB Λ (Γ , Φ')) → BBCtrl Λ (Γ , Φ)
      bbIf     : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (l : (Γ , Φ') ∈ Λ) (bb : BB Λ (Γ , Φ')) → BBCtrl Λ (Γ , Φ)

  -- data BB (Λ : Labels) : (Ξ : MT) → Set where
  --   -- Ends:
  --   bbGoto   : ∀{Ξ} (l : Ξ ∈ Λ) → BB Λ Ξ             -- goto join point (same Ξ)
  --   bbReturn : ∀{Γ Φ}           → BB Λ (Γ , Φ ▷ᵇ rt) -- return from function (stack is destroyed)
  --   -- Branching:
  --   bbIfElse : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (bb bb' : BB Λ (Γ , Φ')) → BB Λ (Γ , Φ)
  --   bbIf     : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (l : (Γ , Φ') ∈ Λ) (bb : BB Λ (Γ , Φ')) → BB Λ (Γ , Φ)
  --   -- Cons-like: Instruction
  --   bbExec     : ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') (bb : BB Λ Ξ') → BB Λ Ξ

  BB′ = λ Ξ Λ → BB Λ Ξ
  BBCtrl′ = λ Ξ Λ → BBCtrl Λ Ξ

  BBs : ∀ {Λ Λ'} (ξ : Λ ⊆ Λ') → Set
  BBs {Λ} {Λ′} ξ = (□ λ Λ″ → AllExt (BB Λ″) ξ) Λ′

  data BBOrGoto (Ξ : MT) (Λ : Labels) : Set where
    block : (bb : □ (BB′ Ξ) Λ) → BBOrGoto Ξ Λ
    goto  : (l  : □ (Ξ ∈_) Λ)  → BBOrGoto Ξ Λ

  record WithBBs (P : Labels → Set) (Λ : Labels) : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : BBs ext
      res   : P Ext

  CompRes :  (Ξ : MT) (Λ : Labels) → Set
  CompRes Ξ Λ = WithBBs (BBOrGoto Ξ) Λ


module _ {Σ : Sig} {rt : Type} where

  open BBTypes Σ rt

  -- Weakening.

  mutual
    weakBB : ∀{Ξ} → BB′ Ξ ⇒ □ (BB′ Ξ)
    weakBB (mkBB jfs ctrl) ρ = mkBB jfs (weakBBCtrl ctrl ρ)

    weakBBCtrl : ∀{Ξ} → BBCtrl′ Ξ ⇒ □ (BBCtrl′ Ξ)
    weakBBCtrl (bbGoto l)           ρ = bbGoto (⊆-lookup ρ l)
    weakBBCtrl (bbReturn)           ρ = bbReturn
    weakBBCtrl (bbIfElse c bb₁ bb₂) ρ = bbIfElse c (weakBB bb₁ ρ) (weakBB bb₂ ρ)
    weakBBCtrl (bbIf c l bb)        ρ = bbIf c (⊆-lookup ρ l) (weakBB bb ρ)


  -- Smart constructors.

  -- Execute j, then pop t.

  -- bbStackIPop : ∀ {t Γ Φ Φ'} (j : StackI Φ (t ∷ Φ')) → BB′ (Γ , Φ') ⇒ BB′ (Γ , Φ)
  -- bbStackIPop j (mkBB jfs ctrl) = mkBB (stackIPop j jfs) ctrl

  -- bbStackIPop : ∀ {t Γ Φ Φ'} (j : StackI Φ (t ∷ Φ')) → BB′ (Γ , Φ') ⇒ BB′ (Γ , Φ)
  -- bbStackIPop     (const v)  = id
  -- bbStackIPop     dup        = id
  -- bbStackIPop {t} pop        = bbExec (stackI pop)             ∘ bbExec (stackI (pop {t = ` t}))
  -- bbStackIPop {t} (arith op) = bbExec (stackI (pop {t = ` t})) ∘ bbExec (stackI (pop {t = ` t}))

  -- bbStoreIPop : ∀ {t Γ Φ Φ'} (j : StoreI Γ Φ (t ∷ Φ')) → BB′ (Γ , Φ') ⇒ BB′ (Γ , Φ)
  -- bbStoreIPop (load x)     = id
  -- bbStoreIPop (store x)    = bbExec (storeI (store x)) ∘ bbExec (stackI pop)
  -- bbStoreIPop (incDec b x) = bbExec (stackI pop) ∘ bbExec (storeI (incDec b x))

  -- bbExecPop : ∀ {Γ Φ Φ' t} (j : JF Σ (Γ , Φ) (Γ , t ∷ Φ')) → BB′ (Γ , Φ') ⇒ BB′ (Γ , Φ)
  -- bbExecPop j = {!j!}

  -- Smart cons, doing peephole optimizations.

  bbExecOpt :  ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') → BB′ Ξ' ⇒ BB′ Ξ
  bbExecOpt j (mkBB jfs ctrl) = mkBB (j ∷ᵒ jfs) ctrl

  -- bbExecOpt :  ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') → BB′ Ξ' ⇒ BB′ Ξ
  -- bbExecOpt j            (bbExec (stackI (pop {t = void})) bb) = bbExec j bb
  -- bbExecOpt (stackI  j)  (bbExec (stackI (pop {t = ` t })) bb) = bbStackIPop j bb
  -- bbExecOpt (storeI  j)  (bbExec (stackI (pop {t = ` t })) bb) = bbStoreIPop j bb
  -- bbExecOpt (comment x)  (bbExec (stackI (pop {t = ` t })) bb) = bbExec (stackI pop) $ bbExec (comment x) bb
  -- bbExecOpt (comment x)  (bbExec (comment y)               bb) = bbExec (comment $ x ++ y) bb
  -- bbExecOpt (scopeI adm) (bbExec (comment x)               bb) = bbExec (comment x) $ bbExec (scopeI adm) bb  -- HACK to join comments over "empty" instructions
  -- bbExecOpt j bb = bbExec j bb

  -- Compilation of C-- to basic blocks

  gotoToBB : ∀{Ξ Λ} → BBOrGoto Ξ Λ → □ (BB′ Ξ) Λ
  gotoToBB (block bb) = bb
  gotoToBB (goto l)   = λ ρ → mkBB [] (bbGoto (l ρ))

  weakBOG : ∀{Ξ Λ Λ′} (ρ : Λ ⊆ Λ′) → BBOrGoto Ξ Λ → BBOrGoto Ξ Λ′
  weakBOG ρ (block bb) = block (bb ∙ ρ)
  weakBOG ρ (goto l)   = goto  (l  ∙ ρ)

  mapBBs :  ∀ {P Q} (f : P ⇒ Q) → WithBBs P ⇒ WithBBs Q
  mapBBs f (ext ∙ bbs ∙ p) = ext ∙ bbs ∙ f p

  joinBBs : ∀ {P Q Λ} → WithBBs (□ P) Λ → WithBBs (□ Q) Λ → WithBBs (□ (P ∩ Q)) Λ
  joinBBs (η₁ ∙ bbs₁ ∙ p) (η₂ ∙ bbs₂ ∙ q)
    = η
    ∙ (λ ρ → AllExt-join (bbs₁ (⊆-trans ξ₁ ρ)) (bbs₂ (⊆-trans ξ₂ ρ)))
    ∙ (λ ρ → p (⊆-trans ξ₁ ρ) , q (⊆-trans ξ₂ ρ))
    where
    rpo   = ⊆-pushoutˡ η₁ η₂
    -- Λ₁₂   = RawPushout.upperBound rpo
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo
    η     = ⊆-trans η₁ ξ₁
    -- bbs   : □ (λ Λ′ → AllExt (BB Λ′) η) Λ₁₂
    -- bbs   = λ τ → AllExt-join (bbs₁ (⊆-trans ξ₁ τ)) (bbs₂ (⊆-trans ξ₂ τ))

  crWeak : ∀{Ξ Λ Λ′} (ρ : Λ ⊆ Λ′) → CompRes Ξ Λ → CompRes Ξ Λ′
  crWeak ρ (η ∙ bbs ∙ res) = ξ₂ ∙ (λ τ → AllExt-slide (bbs (⊆-trans ξ₁ τ)) ρ) ∙ weakBOG ξ₁ res
    where
    rpo   = ⊆-pushoutˡ η ρ
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo

  crGoto : ∀{Ξ Λ} (l : Ξ ∈ Λ) → CompRes Ξ Λ
  crGoto l = _ ∙ (λ ρ → AllExt-id) ∙ goto λ ρ → ⊆-lookup ρ l

  crBB : ∀{Ξ Λ} → □ (BB′ Ξ) Λ → CompRes Ξ Λ
  crBB bb = _ ∙ (λ ρ → AllExt-id) ∙ block bb

  crToBB : ∀ {Ξ Λ} → CompRes Ξ Λ → WithBBs (□ (BB′ Ξ)) Λ
  crToBB (ext ∙ bbs ∙ gb) = ext ∙ bbs ∙ gotoToBB gb

  crToGoto' : ∀ {Ξ Λ} → CompRes Ξ Λ → WithBBs (□ (Ξ ∈_)) Λ
  crToGoto' (ext ∙ bbs ∙ goto l) = ext ∙ bbs ∙ l
  crToGoto' (ext ∙ bbs ∙ block bb)
    = ⊆-skip _ ext
    ∙ (λ ρ → let ρ′ = ⊆-trans ⊆-wk1 ρ in bb ρ′ ∷ bbs ρ′)
    ∙ λ ρ → ⊆-lookup ρ here!

  crToGoto : ∀ {Ξ Λ} → CompRes Ξ Λ  → CompRes Ξ Λ
  crToGoto cr@(ext ∙ bbs ∙ goto l) = cr
  crToGoto (ext ∙ bbs ∙ block bb)
    = ⊆-skip _ ext
    ∙ (λ ρ → let ρ′ = ⊆-trans ⊆-wk1 ρ in bb ρ′ ∷ bbs ρ′)
    ∙ goto (λ ρ → ⊆-lookup ρ here!)

  -- NB: CPS form of joinPoint forces sharing of computation (crToGoto cr)
  joinPoint : ∀ {Ξ Λ}
    → {-@01-} CompRes Ξ Λ → ∀{P}
    → (∀{Λ′} (ρ : Λ ⊆ Λ′) → @ω CompRes Ξ Λ′ → WithBBs P Λ′)
    → WithBBs P Λ
  joinPoint cr k = let
       (η₁ ∙ bbs₁ ∙ l)  = crToGoto' cr
       (η₂ ∙ bbs₂ ∙ bb) = k η₁ (_ ∙ (λ _ → AllExt-id) ∙ goto l)
    in ⊆-trans η₁ η₂ ∙ (λ ρ → AllExt-comp (bbs₁ (⊆-trans η₂ ρ)) (bbs₂ ρ)) ∙ bb


  fix : ∀ {Ξ Λ} → CompRes Ξ (Ξ ∷ Λ) → CompRes Ξ Λ
  fix (η ∙ bbs ∙ bb)
     -- η : (Ξ ∷ Λ) ⊆ Λ′
     -- We could try to get Λ⁻ and l : Ξ ∈ Λ′ such that τ : Λ ⊆ Λ⁻
     -- and then construct a renaming from Λ′ to Ξ ∷ Λ⁻ that takes
     -- l to here!.
     -- This renaming would then be applied to bbs and bb to get
     -- bbs′ and bb′
     -- NOT: -- Use ∷ˡ⁻ : ∀ {a as bs} → Sublist R (a ∷ as) bs → Sublist R as bs
    = ⊆-trans ⊆-wk1 η
    ∙ (λ ρ → AllExt-comp (gotoToBB bb ρ ∷ AllExt-id) (bbs ρ))
    ∙ goto (λ ρ → ⊆-lookup (⊆-trans η ρ) here!)

  -- Compiling to binary if.

  crIfElse' : ∀{Γ Φ Φ' Λ} (c : Cond Φ Φ') (cr₁ cr₂ : CompRes (Γ , Φ') Λ) → CompRes (Γ , Φ) Λ
  crIfElse' c cr₁ cr₂ =
    mapBBs (λ te → block (λ ρ → mkBB [] (bbIfElse c (proj₁ (te ρ)) (proj₂ (te ρ))))) $
    joinBBs (crToBB cr₁) (crToBB cr₂)

  -- Compiling to unary if.

  crIf     : ∀{Γ Φ Φ' Λ}
    (c   : Cond Φ Φ')
    (lw  : WithBBs (□ ((Γ , Φ') ∈_)) Λ)
    (bbw : WithBBs (□ (BB′ (Γ , Φ'))) Λ)
    → CompRes (Γ , Φ) Λ
  crIf c lw bbw =
    mapBBs (λ te → block (λ ρ → mkBB [] (bbIf c (proj₁ (te ρ)) (proj₂ (te ρ))))) $
    joinBBs lw bbw

  crIfElse : ∀{Γ Φ Φ' Λ} (c : Cond Φ Φ') (cr₁ cr₂ : CompRes (Γ , Φ') Λ) → CompRes (Γ , Φ) Λ
  crIfElse c (ext₁ ∙ bbs₁ ∙ goto l₁  ) (ext₂ ∙ bbs₂ ∙ block bb₂) = crIf c           (ext₁ ∙ bbs₁ ∙ l₁) (ext₂ ∙ bbs₂ ∙ bb₂)
  crIfElse c (ext₁ ∙ bbs₁ ∙ goto l₁  ) (ext₂ ∙ bbs₂ ∙ goto l₂  ) = crIf c           (ext₁ ∙ bbs₁ ∙ l₁) (ext₂ ∙ bbs₂ ∙ (mkBB [] ∘ bbGoto ∘ l₂))
  crIfElse c (ext₁ ∙ bbs₁ ∙ block bb₁) (ext₂ ∙ bbs₂ ∙ goto l₂  ) = crIf (negCond c) (ext₂ ∙ bbs₂ ∙ l₂) (ext₁ ∙ bbs₁ ∙ bb₁)
  crIfElse c cr₁@(_ ∙ _ ∙ block _)     (ext₂ ∙ bbs₂ ∙ block bb₂) = crIf c           (crToGoto' cr₁)    (ext₂ ∙ bbs₂ ∙ bb₂)

  -- Non-optimizing:

  bbExec :  ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') → BB′ Ξ' ⇒ BB′ Ξ
  bbExec j (mkBB jfs ctrl) = mkBB (j ∷ jfs) ctrl

  crExec' : ∀{Ξ Ξ' Λ} (j : JF Σ Ξ Ξ') (bb : CompRes Ξ' Λ) → CompRes Ξ Λ
  crExec' j = mapBBs λ k → block $ bbExec j ∘ gotoToBB k

  -- Optimizing:

  crExec : ∀{Ξ Ξ' Λ} (j : JF Σ Ξ Ξ') (bb : CompRes Ξ' Λ) → CompRes Ξ Λ
  crExec j = mapBBs λ k → block $ bbExecOpt j ∘ gotoToBB k

  crComment :  ∀{Ξ Λ} (x : String) (bb : CompRes Ξ Λ) → CompRes Ξ Λ
  crComment x = crExec (comment [ x ])

  commentStm :  ∀ {Γ mt Φ}
      → Stm Σ rt Γ mt
      → CompRes (Γ , Φ)
      ⇒ CompRes (Γ , Φ)
  commentStm s = crComment (printStm s)

  mutual

    -- Compiling a statement.

    compileStm : ∀ {Γ mt Φ}
      → Stm Σ rt Γ mt
      → CompRes (Γ ▷ mt , Φ)
      ⇒ CompRes (Γ , Φ)

    compileStm s@(sReturn e)       _ = commentStm s $ compileExp e $ crBB λ ρ → mkBB [] bbReturn
    compileStm s@(sExp e)            = commentStm s ∘ compileExp e ∘ crExec (stackI pop)
    compileStm s@(sInit x nothing)   = commentStm s ∘ crExec (scopeI (decl x))
    compileStm s@(sInit x (just e))  = commentStm s ∘ compileExp e ∘ crExec (scopeI (decl x)) ∘ crExec (storeI (store (vzero x)))
    compileStm s@(sBlock ss)         = crExec (scopeI newBlock) ∘ compileStms ss ∘ crExec (scopeI popBlock)
    compileStm s@(sWhile e s₀)     k = crComment ("while" <+> parens (printExp e)) $
                                       fix $ compileCond e (compileStm s₀ $ crGoto here!) (crWeak ⊆-wk1 k)
    compileStm s@(sIfElse e s₁ s₂) k = crComment ("if" <+> parens (printExp e)) $
                                       joinPoint k λ ρ k' → compileCond e (compileStm s₁ k') (compileStm s₂ k')

    -- Compiling a statement list.

    compileStms : ∀{Γ Δ Δ'  Φ}
      → Stms Σ rt Γ Δ Δ'
      → CompRes (Δ' ∷ Γ , Φ)
      ⇒ CompRes (Δ  ∷ Γ , Φ)
    compileStms []       = id
    compileStms (s ∷ ss) = compileStm s ∘ compileStms ss

    -- Compiling conditionals.

    compileCond : ∀{Γ}
      (e : Exp` Σ Γ bool) {Φ Λ}
      (kᵗ kᶠ : CompRes (Γ , Φ) Λ)
      → CompRes (Γ , Φ) Λ
    compileCond (eConst false) kᵗ kᶠ = kᶠ
    compileCond (eConst true ) kᵗ kᶠ = kᵗ
    compileCond (eOp op e e')  kᵗ kᶠ = compileCondOp op e e' kᵗ kᶠ

    compileCond e@(eVar _  )   kᵗ kᶠ = compileExp e $ crIfElse (eqBool true) kᵗ kᶠ
    compileCond e@(eApp _ _)   kᵗ kᶠ = compileExp e $ crIfElse (eqBool true) kᵗ kᶠ
    compileCond e@(eAss _ _)   kᵗ kᶠ = compileExp e $ crIfElse (eqBool true) kᵗ kᶠ

    compileCond (eIncrDecr p (incr ()) x) kᵗ kᶠ
    compileCond (eIncrDecr p (decr ()) x) kᵗ kᶠ

    -- Compiling composite conditionals.

    compileCondOp : ∀{Γ t}
      (op   : Op t bool)
      (e e' : Exp` Σ Γ t) {Φ Λ}
      (kᵗ kᶠ : CompRes (Γ , Φ) Λ)
      → CompRes (Γ , Φ) Λ

    compileCondOp (logic and) e e' kᵗ kᶠ = joinPoint kᶠ λ ρ kf' → compileCond e (compileCond e' (crWeak ρ kᵗ) kf') kf'
    compileCondOp (logic or)  e e' kᵗ kᶠ = joinPoint kᵗ λ ρ kt' → compileCond e kt' (compileCond e' kt' $ crWeak ρ kᶠ)

    compileCondOp (cmp   op)  e eZero kᵗ kᶠ = compileExp e $ crIfElse (cmpZero op) kᵗ kᶠ
    compileCondOp (cmp   op)  eZero e kᵗ kᶠ = compileExp e $ crIfElse (cmpZero (flipCmpOp op)) kᵗ kᶠ

    compileCondOp (cmp   op)  e e' kᵗ kᶠ =
      compileExp e  $
      compileExp e' $
      crIfElse (cmp op) kᵗ kᶠ

    compileCondOp (arith (plus ()))
    compileCondOp (arith (minus ()))
    compileCondOp (arith (times ()))
    compileCondOp (arith (div ()))

    -- Compiling boolean operators.

    compileBoolOp : ∀{Γ t Φ}
      (op   : Op t bool)
      (e e' : Exp` Σ Γ t)
      → CompRes (Γ , bool ∷ Φ)  -- Continuation expects a bool on the stack.
      ⇒ CompRes (Γ , Φ)

    compileBoolOp op e e' k =
      joinPoint k λ ρ k' →
      compileCondOp op e e'
        (crExec (stackI (const true )) k')
        (crExec (stackI (const false)) k')

    -- Compiling expressions.

    compileExp : ∀{Γ t Φ}
      → Exp Σ Γ t
      → CompRes (Γ , Φ ▷ᵇ t)  -- Continuation expects a value of type t on the stack.
      ⇒ CompRes (Γ , Φ)

    compileExp (eConst v)            = crExec (stackI (const v))
    compileExp (eVar x)              = crExec (storeI (load x))
    compileExp (eAss x e)            = compileExp e ∘ crExec (storeI (store x)) ∘ crExec (storeI (load x))

    compileExp (eApp (fun x f) es)   = compileExps es ∘ crExec (callI (call f))
    compileExp (eBuiltin f     es)   = compileExps es ∘ crExec (callI (builtin f))

    compileExp (eOp (arith op) e e') = compileExp e ∘ compileExp e' ∘ crExec (stackI (arith op))
    compileExp (eOp (cmp   op) e e') = compileBoolOp (cmp op) e e'
    compileExp (eOp (logic op) e e') = compileBoolOp (logic op) e e'

    compileExp (eIncrDecr pp id x)   = compileIncrDecr pp id x

    compileIncrDecr : ∀ {Γ t Φ}
      → (pp : PrePost) (id : IncrDecr t) (x : Var Γ t)
      → CompRes (Γ , t ∷ Φ)  -- Continuation expects a value of type t on the stack.
      ⇒ CompRes (Γ , Φ)

    compileIncrDecr pre  (incr int) x = crExec (storeI (incDec inc x)) ∘ crExec (storeI (load x))
    compileIncrDecr pre  (decr int) x = crExec (storeI (incDec dec x)) ∘ crExec (storeI (load x))
    compileIncrDecr post (incr int) x = crExec (storeI (load x)) ∘ crExec (storeI (incDec inc x))
    compileIncrDecr post (decr int) x = crExec (storeI (load x)) ∘ crExec (storeI (incDec dec x))

    compileIncrDecr pre  (incr double) x
      = crExec (storeI (load x))
      ∘ crExec (stackI (const 1.0))
      ∘ crExec (stackI (arith (plus double)))
      ∘ crExec (storeI (store x))
      ∘ crExec (storeI (load x))

    compileIncrDecr pre  (decr double) x
      = crExec (storeI (load x))
      ∘ crExec (stackI (const 1.0))
      ∘ crExec (stackI (arith (minus double)))
      ∘ crExec (storeI (store x))
      ∘ crExec (storeI (load x))

    compileIncrDecr post (incr double) x
      = crExec (storeI (load x))
      ∘ crExec (stackI dup)
      ∘ crExec (stackI (const 1.0))
      ∘ crExec (stackI (arith (plus double)))
      ∘ crExec (storeI (store x))

    compileIncrDecr post (decr double) x
      = crExec (storeI (load x))
      ∘ crExec (stackI dup)
      ∘ crExec (stackI (const 1.0))
      ∘ crExec (stackI (arith (minus double)))
      ∘ crExec (storeI (store x))

    -- Compiling expression list.
    -- First value ends up first on the stack.

    compileExps : ∀{Γ Δ}
      (es : Exps Σ Γ Δ) {Λ Φ}
      → CompRes (Γ , Δ ++ Φ) Λ
      → CompRes (Γ , Φ)       Λ
    compileExps []       = id
    compileExps (e ∷ es) = compileExps es ∘ compileExp e

open BBTypes

-- Method

-- Meth : (Σ : Sig) (ft : FunType) → Set
-- Meth Σ (funType Δ rt) = CompRes Σ rt (Δ ∷ [] , []) []

record Meth (Σ : Sig) (ft : FunType) : Set where
  constructor bbMethod
  field
    labels : Labels
    entry  : let funType Δ rt = ft; Ξ = (Δ ∷ [] , []) in
             BB Σ rt labels Ξ
    blocks : let funType Δ rt = ft in
             List.All (BB Σ rt labels) labels

-- If the statements do not end in returns,
-- a default value will be returned.

bbDefaultReturn : ∀ {Σ Λ Ξ} rt → BB Σ rt Λ Ξ
bbDefaultReturn (` t) = bbExec (stackI (const (defaultVal` t))) (mkBB [] bbReturn)
bbDefaultReturn void  = mkBB [] bbReturn

-- compileDef : ∀{Σ ft} → Def Σ ft → Meth Σ ft
-- compileDef {Σ} {funType Δ rt} (Γ , ss) =
--   compileStms Σ rt ss $ crBB Σ rt λ ρ → bbDefaultReturn rt

compileDef : ∀{Σ ft} → Def Σ ft → Meth Σ ft
compileDef {Σ} {funType Δ rt} (Γ , ss) = record
  { labels = Λ
  ; entry  = gotoToBB bb ⊆-refl
  ; blocks = extendAll (bbs ⊆-refl) []
  }
  where
  cr = compileStms ss $ crBB λ ρ → bbDefaultReturn rt
  open WithBBs cr using (bbs) renaming (Ext to Λ; res to bb)

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

module BasicBlocks where

open import Library
open import Library.AllExt

open import WellTypedSyntax
open import Value
open import FlowChart

module _ (Σ : Sig) (rt : Type) where

  -- Basic blocks are flow charts without label definition

  data BB (Λ : Labels) : (Ξ : MT) → Set where
    -- Ends:
    bbGoto   : ∀{Ξ} (l : Ξ ∈ Λ) → BB Λ Ξ             -- goto join point (same Ξ)
    bbReturn : ∀{Γ Φ}           → BB Λ (Γ , Φ ▷ᵇ rt) -- return from function (stack is destroyed)
    -- Branching:
    bbIfElse : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (bb bb' : BB Λ (Γ , Φ')) → BB Λ (Γ , Φ)
    bbIf     : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (l : (Γ , Φ') ∈ Λ) (bb : BB Λ (Γ , Φ')) → BB Λ (Γ , Φ)
    -- Cons-like: Instruction
    bbExec     : ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') (bb : BB Λ Ξ') → BB Λ Ξ

  BB′ = λ Ξ Λ → BB Λ Ξ

  -- Execute j, then pop t.

  bbStackIPop : ∀ {t Γ Φ Φ'} (j : StackI Φ (t ∷ Φ')) → BB′ (Γ , Φ') ⇒ BB′ (Γ , Φ)
  bbStackIPop     (const v)  = id
  bbStackIPop     dup        = id
  bbStackIPop {t} pop        = bbExec (stackI pop)             ∘ bbExec (stackI (pop {t = ` t}))
  bbStackIPop {t} (arith op) = bbExec (stackI (pop {t = ` t})) ∘ bbExec (stackI (pop {t = ` t}))

  bbStoreIPop : ∀ {t Γ Φ Φ'} (j : StoreI Γ Φ (t ∷ Φ')) → BB′ (Γ , Φ') ⇒ BB′ (Γ , Φ)
  bbStoreIPop (load x)     = id
  bbStoreIPop (store x)    = bbExec (storeI (store x)) ∘ bbExec (stackI pop)
  bbStoreIPop (incDec b x) = bbExec (stackI pop) ∘ bbExec (storeI (incDec b x))

  -- bbExecPop : ∀ {Γ Φ Φ' t} (j : JF Σ (Γ , Φ) (Γ , t ∷ Φ')) → BB′ (Γ , Φ') ⇒ BB′ (Γ , Φ)
  -- bbExecPop j = {!j!}

  -- Smart cons, doing peephole optimizations.

  bbExecOpt :  ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') → BB′ Ξ' ⇒ BB′ Ξ
  bbExecOpt j          (bbExec (stackI (pop {t = void})) bb) = bbExec j bb
  bbExecOpt (stackI j) (bbExec (stackI (pop {t = ` t })) bb) = bbStackIPop j bb
  bbExecOpt (storeI j) (bbExec (stackI (pop {t = ` t })) bb) = bbStoreIPop j bb
  bbExecOpt j bb = bbExec j bb

  -- Flatten out label definitions from a flow chart

  record Flat Λ Ξ : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : □ (λ Λ′ → AllExt (BB Λ′) ext) Ext
      bb    : □ (λ Λ′ → BB Λ′ Ξ) Ext

  flat : ∀{Λ Ξ} → FC Σ rt Λ Ξ → Flat Λ Ξ

  flat (fcGoto l) = ⊆-refl ∙ (λ τ → AllExt-id) ∙ λ τ → bbGoto (⊆-lookup τ l)
  flat fcReturn   = ⊆-refl ∙ (λ τ → AllExt-id) ∙ λ τ → bbReturn

  flat (fcExec j fc)
    with η ∙ bbs ∙ bb ← flat fc = η ∙ bbs ∙ (bbExec j ∘ bb)

  flat (fcFix fc)
    with η ∙ bbs ∙ bb ← flat fc
      = ⊆-trans (⊆-skip _ ⊆-refl) η
      ∙ (λ τ → AllExt-comp (bb τ ∷ AllExt-id) (bbs τ))
      ∙ (λ τ → bbGoto (⊆-lookup (⊆-trans η τ) here!))

  flat (fcIfElse c fc₁ fc₂)
    with η₁ ∙ bbs₁ ∙ bb₁ ← flat fc₁
       | η₂ ∙ bbs₂ ∙ bb₂ ← flat fc₂
      = η ∙ bbs ∙ bs
    where
    rpo   = ⊆-pushoutˡ η₁ η₂
    Λ     = RawPushout.upperBound rpo
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo
    η     = ⊆-trans η₁ ξ₁
    bs    : □ (λ Λ′ → BB Λ′ _) _
    bs  τ = bbIfElse c (bb₁ (⊆-trans ξ₁ τ)) (bb₂ (⊆-trans ξ₂ τ))
    bbs   : □ (λ Λ′ → AllExt (BB Λ′) η) Λ
    bbs τ = AllExt-join (bbs₁ (⊆-trans ξ₁ τ)) (bbs₂ (⊆-trans ξ₂ τ))

  flat (fcLet fc₁ fc₂)
    with η₁ ∙ bbs₁ ∙ bb₁ ← flat fc₁
       | η₂ ∙ bbs₂ ∙ bb₂ ← flat fc₂
      = ⊆-trans (⊆-skip _ ⊆-refl) η
      ∙ (λ τ → AllExt-comp ((bb₁ (⊆-trans ξ₁′ τ)) ∷ AllExt-id) (bbs τ))
      ∙ λ τ → bb₂ (⊆-trans ξ₂ τ)
    where
    rpo   = ⊆-pushoutˡ (refl ∷ η₁) η₂
    Λ     = RawPushout.upperBound rpo
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo
    η     = ⊆-trans (refl ∷ η₁) ξ₁
    ξ₁′   = ⊆-trans (⊆-skip _ ⊆-refl) ξ₁
    bbs   : □ (λ Λ′ → AllExt (BB Λ′) η) Λ
    bbs τ = AllExt-join (lift (bbs₁ (⊆-trans ξ₁′ τ))) (bbs₂ (⊆-trans ξ₂ τ))

  -- Compilation of C-- to basic blocks

  BBs : ∀ {Λ Λ'} (ξ : Λ ⊆ Λ') → Set
  BBs {Λ} {Λ′} ξ = (□ λ Λ″ → AllExt (BB Λ″) ξ) Λ′

  data BBOrGoto (Ξ : MT) (Λ : Labels) : Set where
    block : (bb : □ (BB′ Ξ) Λ) → BBOrGoto Ξ Λ
    goto  : (l  : □ (Ξ ∈_) Λ)  → BBOrGoto Ξ Λ

  gotoToBB : ∀{Ξ Λ} → BBOrGoto Ξ Λ → □ (BB′ Ξ) Λ
  gotoToBB (block bb) = bb
  gotoToBB (goto l)   = λ ρ → bbGoto (l ρ)

  weakBOG : ∀{Ξ Λ Λ′} (ρ : Λ ⊆ Λ′) → BBOrGoto Ξ Λ → BBOrGoto Ξ Λ′
  weakBOG ρ (block bb) = block (bb ∙ ρ)
  weakBOG ρ (goto l)   = goto  (l  ∙ ρ)

  record WithBBs (P : Labels → Set) (Λ : Labels) : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : BBs ext
      res   : P Ext

  CompRes :  (Ξ : MT) (Λ : Labels) → Set
  CompRes Ξ Λ = WithBBs (BBOrGoto Ξ) Λ

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
  joinPoint : ∀ {Ξ Λ} → {-@01-} CompRes Ξ Λ → ∀{P} → (∀{Λ′} (ρ : Λ ⊆ Λ′) → @ω CompRes Ξ Λ′ → WithBBs P Λ′) → WithBBs P Λ
  -- joinPoint cr k = k ⊆-refl (crToGoto cr)
  joinPoint cr k = let
       (η₁ ∙ bbs₁ ∙ l)  = crToGoto' cr
       (η₂ ∙ bbs₂ ∙ bb) = k η₁ (_ ∙ (λ _ → AllExt-id) ∙ goto l)
    in ⊆-trans η₁ η₂ ∙ (λ ρ → AllExt-comp (bbs₁ (⊆-trans η₂ ρ)) (bbs₂ ρ)) ∙ bb


  fix : ∀ {Ξ Λ} → CompRes Ξ (Ξ ∷ Λ) → CompRes Ξ Λ
  fix (η ∙ bbs ∙ bb)
    = ⊆-trans ⊆-wk1 η
    ∙ (λ ρ → AllExt-comp (gotoToBB bb ρ ∷ AllExt-id) (bbs ρ))
    ∙ goto (λ ρ → ⊆-lookup (⊆-trans η ρ) here!)

  -- Compiling to binary if.

  crIfElse' : ∀{Γ Φ Φ' Λ} (c : Cond Φ Φ') (cr₁ cr₂ : CompRes (Γ , Φ') Λ) → CompRes (Γ , Φ) Λ
  crIfElse' c cr₁ cr₂ =
    mapBBs (λ te → block (λ ρ → bbIfElse c (proj₁ (te ρ)) (proj₂ (te ρ)))) $
    joinBBs (crToBB cr₁) (crToBB cr₂)

  -- Compiling to unary if.

  crIf     : ∀{Γ Φ Φ' Λ}
    (c   : Cond Φ Φ')
    (lw  : WithBBs (□ ((Γ , Φ') ∈_)) Λ)
    (bbw : WithBBs (□ (BB′ (Γ , Φ'))) Λ)
    → CompRes (Γ , Φ) Λ
  crIf c lw bbw =
    mapBBs (λ te → block (λ ρ → bbIf c (proj₁ (te ρ)) (proj₂ (te ρ)))) $
    joinBBs lw bbw

  crIfElse : ∀{Γ Φ Φ' Λ} (c : Cond Φ Φ') (cr₁ cr₂ : CompRes (Γ , Φ') Λ) → CompRes (Γ , Φ) Λ
  crIfElse c (ext₁ ∙ bbs₁ ∙ goto l₁  ) (ext₂ ∙ bbs₂ ∙ block bb₂) = crIf c           (ext₁ ∙ bbs₁ ∙ l₁) (ext₂ ∙ bbs₂ ∙ bb₂)
  crIfElse c (ext₁ ∙ bbs₁ ∙ goto l₁  ) (ext₂ ∙ bbs₂ ∙ goto l₂  ) = crIf c           (ext₁ ∙ bbs₁ ∙ l₁) (ext₂ ∙ bbs₂ ∙ (bbGoto ∘ l₂))
  crIfElse c (ext₁ ∙ bbs₁ ∙ block bb₁) (ext₂ ∙ bbs₂ ∙ goto l₂  ) = crIf (negCond c) (ext₂ ∙ bbs₂ ∙ l₂) (ext₁ ∙ bbs₁ ∙ bb₁)
  crIfElse c cr₁@(_ ∙ _ ∙ block _)     (ext₂ ∙ bbs₂ ∙ block bb₂) = crIf c           (crToGoto' cr₁)    (ext₂ ∙ bbs₂ ∙ bb₂)

  -- Non-optimizing:

  crExec' : ∀{Ξ Ξ' Λ} (j : JF Σ Ξ Ξ') (bb : CompRes Ξ' Λ) → CompRes Ξ Λ
  crExec' j = mapBBs λ k → block $ bbExec j ∘ gotoToBB k

  -- Optimizing:

  crExec : ∀{Ξ Ξ' Λ} (j : JF Σ Ξ Ξ') (bb : CompRes Ξ' Λ) → CompRes Ξ Λ
  crExec j = mapBBs λ k → block $ bbExecOpt j ∘ gotoToBB k

  crWeak : ∀{Ξ Λ Λ′} (ρ : Λ ⊆ Λ′) → CompRes Ξ Λ → CompRes Ξ Λ′
  crWeak ρ (η ∙ bbs ∙ res) = ξ₂ ∙ (λ τ → AllExt-slide (bbs (⊆-trans ξ₁ τ)) ρ) ∙ weakBOG ξ₁ res
    where
    rpo   = ⊆-pushoutˡ η ρ
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo

  mutual

    -- Compiling a statement.

    compileStm : ∀ {Γ mt Φ}
      → Stm Σ rt Γ mt
      → CompRes (Γ ▷ mt , Φ)
      ⇒ CompRes (Γ , Φ)

    compileStm (sReturn e)       _ = compileExp e $ crBB λ ρ → bbReturn
    compileStm (sExp e)            = compileExp e ∘ crExec (stackI pop)
    compileStm (sInit nothing)     = crExec (scopeI decl)
    compileStm (sInit (just e))    = compileExp e ∘ crExec (scopeI decl) ∘ crExec (storeI (store vzero))
    compileStm (sBlock ss)         = crExec (scopeI newBlock) ∘ compileStms ss ∘ crExec (scopeI popBlock)
    compileStm (sWhile e s)      k = fix $ compileCond e (compileStm s $ crGoto here!) (crWeak wk1 k)
    compileStm (sIfElse e s₁ s₂) k = joinPoint k λ ρ k' → compileCond e (compileStm s₁ k') (compileStm s₂ k')

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

    compileExp (eApp f es)           = compileExps es ∘ crExec (callI (call f))
    compileExp (eBuiltin f es)       = compileExps es ∘ crExec (callI (builtin f))

    compileExp (eOp (arith op) e e') = compileExp e ∘ compileExp e' ∘ crExec (stackI (arith op))
    compileExp (eOp (cmp   op) e e') = compileBoolOp (cmp op) e e'
    compileExp (eOp (logic op) e e') = compileBoolOp (logic op) e e'

    compileExp (eIncrDecr pre  (incr int) x) = crExec (storeI (incDec inc x)) ∘ crExec (storeI (load x))
    compileExp (eIncrDecr pre  (decr int) x) = crExec (storeI (incDec dec x)) ∘ crExec (storeI (load x))
    compileExp (eIncrDecr post (incr int) x) = crExec (storeI (load x)) ∘ crExec (storeI (incDec inc x))
    compileExp (eIncrDecr post (decr int) x) = crExec (storeI (load x)) ∘ crExec (storeI (incDec dec x))

    compileExp (eIncrDecr pre  (incr double) x)
      = crExec (storeI (load x))
      ∘ crExec (stackI (const 1.0))
      ∘ crExec (stackI (arith (plus double)))
      ∘ crExec (storeI (store x))
      ∘ crExec (storeI (load x))

    compileExp (eIncrDecr pre  (decr double) x)
      = crExec (storeI (load x))
      ∘ crExec (stackI (const 1.0))
      ∘ crExec (stackI (arith (minus double)))
      ∘ crExec (storeI (store x))
      ∘ crExec (storeI (load x))

    compileExp (eIncrDecr post (incr double) x)
      = crExec (storeI (load x))
      ∘ crExec (stackI dup)
      ∘ crExec (stackI (const 1.0))
      ∘ crExec (stackI (arith (plus double)))
      ∘ crExec (storeI (store x))

    compileExp (eIncrDecr post (decr double) x)
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
bbDefaultReturn (` t) = bbExec (stackI (const (defaultVal` t))) bbReturn
bbDefaultReturn void  = bbReturn

-- compileDef : ∀{Σ ft} → Def Σ ft → Meth Σ ft
-- compileDef {Σ} {funType Δ rt} (Γ , ss) =
--   compileStms Σ rt ss $ crBB Σ rt λ ρ → bbDefaultReturn rt

compileDef : ∀{Σ ft} → Def Σ ft → Meth Σ ft
compileDef {Σ} {funType Δ rt} (Γ , ss) = record
  { labels = Λ
  ; entry  = gotoToBB _ _ bb ⊆-refl
  ; blocks = extendAll (bbs ⊆-refl) []
  }
  where
  cr = compileStms Σ rt ss $ crBB Σ rt λ ρ → bbDefaultReturn rt
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

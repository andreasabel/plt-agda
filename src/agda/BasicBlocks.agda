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
    -- Cons-like: Instruction
    bbExec     : ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') (bb : BB Λ Ξ') → BB Λ Ξ

  BB′ = λ Ξ Λ → BB Λ Ξ

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

  mapBBs :  ∀ {P Q} (f : P ⇒ Q) → WithBBs P ⇒ WithBBs Q
  mapBBs f (ext ∙ bbs ∙ p) = ext ∙ bbs ∙ f p

  joinBBs : ∀ {P Q Λ} → WithBBs (□ P) Λ → WithBBs (□ Q) Λ → WithBBs (□ (P ∩ Q)) Λ
  joinBBs (η₁ ∙ bbs₁ ∙ p) (η₂ ∙ bbs₂ ∙ q)
    = η
    ∙ (λ ρ → AllExt-join (bbs₁ (⊆-trans ξ₁ ρ)) (bbs₂ (⊆-trans ξ₂ ρ)))
    ∙ (λ ρ → p (⊆-trans ξ₁ ρ) , q (⊆-trans ξ₂ ρ))
    where
    rpo   = ⊆-pushoutˡ η₁ η₂
    Λ₁₂   = RawPushout.upperBound rpo
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo
    η     = ⊆-trans η₁ ξ₁
    bbs   : □ (λ Λ′ → AllExt (BB Λ′) η) Λ₁₂
    bbs   = λ τ → AllExt-join (bbs₁ (⊆-trans ξ₁ τ)) (bbs₂ (⊆-trans ξ₂ τ))

  CompRes :  (Ξ : MT) (Λ : Labels) → Set
  CompRes Ξ Λ = WithBBs (BBOrGoto Ξ) Λ

  -- record CompRes (Ξ : MT) (Λ : Labels) : Set where
  --   constructor _∙_∙_
  --   field
  --     {Ext} : Labels
  --     ext   : Λ ⊆ Ext
  --     bbs   : BBs ext
  --     res   : BBOrGoto Ξ Ext

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
  joinPoint : ∀ {Ξ Λ} {A : Set} → {-@01-} CompRes Ξ Λ → (@ω CompRes Ξ Λ → A) → A
  joinPoint cr k = k (crToGoto cr)

  fix : ∀ {Ξ Λ} → CompRes Ξ (Ξ ∷ Λ) → CompRes Ξ Λ
  fix (η ∙ bbs ∙ bb)
    = ⊆-trans ⊆-wk1 η
    ∙ (λ ρ → AllExt-comp (gotoToBB bb ρ ∷ AllExt-id) (bbs ρ))
    ∙ goto (λ ρ → ⊆-lookup (⊆-trans η ρ) here!)

  crIfElse : ∀{Γ Φ Φ' Λ} (c : Cond Φ Φ') (cr₁ cr₂ : CompRes (Γ , Φ') Λ) → CompRes (Γ , Φ) Λ
  crIfElse c cr₁ cr₂ =
    mapBBs (λ te → block (λ ρ → bbIfElse c (proj₁ (te ρ)) (proj₂ (te ρ)))) $
    joinBBs (crToBB cr₁) (crToBB cr₂)

  crExec : ∀{Ξ Ξ' Λ} (j : JF Σ Ξ Ξ') (bb : CompRes Ξ' Λ) → CompRes Ξ Λ
  crExec j = mapBBs λ k → block $ bbExec j ∘ gotoToBB k

  crWeak : ∀{Ξ Λ Λ′} (ρ : Λ ⊆ Λ′) → CompRes Ξ Λ → CompRes Ξ Λ′
  crWeak ρ (η ∙ bbs ∙ res) = ξ₂ ∙ (λ τ → AllExt-slide (bbs (⊆-trans ξ₁ τ)) ρ) ∙ weakBOG ξ₁ res
    where
    rpo   = ⊆-pushoutˡ η ρ
    ξ₁    = RawPushout.leg₁ rpo
    ξ₂    = RawPushout.leg₂ rpo

  mutual

    compileStm : ∀ {Γ mt}
        (s : Stm Σ rt Γ mt) {Λ Φ}
        (k : CompRes (Γ ▷ mt , Φ) Λ)
        → CompRes (Γ , Φ) Λ

    compileStm (sReturn e)       _ = compileExp e $ crBB λ ρ → bbReturn
    compileStm (sExp e)          k = compileExp e $ crExec (stackI pop) k
    compileStm (sInit nothing)   k = crExec (scopeI decl) k
    compileStm (sInit (just e))  k = compileExp e $ crExec (scopeI decl) $ crExec (storeI (store vzero)) k
    compileStm (sBlock ss)       k = crExec (scopeI newBlock) $ compileStms ss $ crExec (scopeI popBlock) k
    compileStm (sWhile e s)      k = fix $ compileCond e (compileStm s $ crGoto here!) (crWeak wk1 k)
    compileStm (sIfElse e s₁ s₂) k = joinPoint k λ k' → compileCond e (compileStm s₁ k') (compileStm s₂ k')

    compileStms : ∀{Γ Δ Δ'}
      (ss : Stms Σ rt Γ Δ Δ') {Λ Φ}
      → CompRes (Δ' ∷ Γ , Φ) Λ
      → CompRes (Δ ∷ Γ , Φ) Λ
    compileStms []       k = k
    compileStms (s ∷ ss) k = compileStm s $ compileStms ss k

    compileCond : ∀{Γ}
      (e : Exp` Σ Γ bool) {Λ Φ}
      (kᵗ kᶠ : CompRes (Γ , Φ) Λ)
      → CompRes (Γ , Φ) Λ
    compileCond (eConst false) kᵗ kᶠ = kᶠ
    compileCond (eConst true ) kᵗ kᶠ = kᵗ
    compileCond (eOp op e e') kᵗ kᶠ = compileCondOp op e e' kᵗ kᶠ
    compileCond e@(eVar _  )  kᵗ kᶠ = compileExp e $ crIfElse (eqBool true) kᵗ kᶠ
    compileCond e@(eApp _ _)  kᵗ kᶠ = compileExp e $ crIfElse (eqBool true) kᵗ kᶠ
    compileCond e@(eAss _ _)  kᵗ kᶠ = compileExp e $ crIfElse (eqBool true) kᵗ kᶠ
    compileCond (eIncrDecr p (incr ()) x) kᵗ kᶠ
    compileCond (eIncrDecr p (decr ()) x) kᵗ kᶠ

    -- Compiling composite conditionals.

    compileCondOp : ∀{Γ t}
      (op   : Op t bool)
      (e e' : Exp` Σ Γ t) {Λ Φ}
      (kt kf : CompRes (Γ , Φ) Λ)  -- kt: true, kf: false
      → CompRes (Γ , Φ) Λ

    compileCondOp (logic and) e e' kt kf = joinPoint kf λ kf' → compileCond e (compileCond e' kt kf') kf'
    compileCondOp (logic or)  e e' kt kf = joinPoint kt λ kt' → compileCond e kt' (compileCond e' kt' kf)
    compileCondOp (cmp   op)  e e' kt kf =
      compileExp e  $
      compileExp e' $
      crIfElse (cmp op) kt kf
    compileCondOp (arith (plus ()))
    compileCondOp (arith (minus ()))
    compileCondOp (arith (times ()))
    compileCondOp (arith (div ()))


    compileBoolOp : ∀{Γ t}
      (op   : Op t bool)
      (e e' : Exp` Σ Γ t) {Λ Φ}
      (k    : CompRes (Γ , bool ∷ Φ) Λ)
      → CompRes (Γ , Φ) Λ
    compileBoolOp op e e' k =
      joinPoint k λ k' →
      compileCondOp op e e'
        (crExec (stackI (const true )) k')
        (crExec (stackI (const false)) k')

    -- Compiling expressions.

    compileExp : ∀{Γ t}
      (e : Exp Σ Γ t)          {Λ Φ}
      (k : CompRes (Γ , Φ ▷ᵇ t) Λ)
      → CompRes (Γ , Φ) Λ
    compileExp (eConst v)            k = crExec (stackI (const v)) k
    compileExp (eVar x)              k = crExec (storeI (load x)) k
    compileExp (eAss x e)            k = compileExp e $ crExec (stackI dup) $ crExec (storeI (store x)) k

    compileExp (eApp f es)           k = compileExps es $ crExec (call f) k
    compileExp (eBuiltin f es)       k = compileExps es $ crExec (builtin f) k

    compileExp (eOp (arith op) e e') k = compileExp e $ compileExp e' $ crExec (stackI (arith op)) k
    compileExp (eOp (cmp   op) e e') k = compileBoolOp (cmp op) e e' k
    compileExp (eOp (logic op) e e') k = compileBoolOp (logic op) e e' k

    compileExp (eIncrDecr pre  (incr int) x)    k = {!!}
    compileExp (eIncrDecr pre  (decr int) x)    k = {!!}
    compileExp (eIncrDecr post (incr int) x)    k = {!!}
    compileExp (eIncrDecr post (decr int) x)    k = {!!}

    compileExp (eIncrDecr pre  (incr double) x) k = {!!}
    compileExp (eIncrDecr pre  (decr double) x) k = {!!}
    compileExp (eIncrDecr post (incr double) x) k = {!!}
    compileExp (eIncrDecr post (decr double) x) k = {!!}

    -- Compiling expression list.
    -- First value ends up first on the stack.

    compileExps : ∀{Γ Δ}
      (es : Exps Σ Γ Δ)          {Λ Φ}
      (k : CompRes (Γ , Δ ++ʳ Φ) Λ)
      → CompRes (Γ , Φ) Λ
    compileExps [] k = k
    compileExps (e ∷ es) k = compileExp e $ compileExps es $ k

{-

  -- Compilation of C-- to basic blocks

  BBs : ∀ (Ξ : MT) {Λ Λ'} (ξ : Λ ⊆ Λ') → Set
  BBs Ξ {Λ} {Λ′} ξ = (□ λ Λ″ → AllExt (BB Λ″) (⊆-skip Ξ ξ)) Λ′

  record CompRes (Ξ : MT) (Λ : Labels) : Set where
    constructor _,_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : BBs Ξ ext

  mutual

    compileStm : ∀ {Γ mt}
        (s : Stm Σ rt Γ mt) {Λ Φ}
        (lᵏ : (Γ ▷ mt , Φ) ∈ Λ)
        → CompRes (Γ , Φ) Λ
        -- → ∃₂ λ Λₜ (ξ : Λ ⊆ Λₜ) → BBs (Γ , Φ) ξ
    compileStm s lᵏ = {!!}

    compileCond : ∀{Γ}
      (e : Exp` Σ Γ bool) {Λ Φ}
      (lᵗ lᶠ : (Γ , Φ) ∈ Λ)
      → CompRes (Γ , Φ) Λ
    compileCond (eConst false) lᵗ lᶠ = ⊆-refl , λ ρ → bbGoto (⊆-lookup ρ lᶠ) ∷ AllExt-id
    compileCond (eConst true) lᵗ lᶠ  = ⊆-refl , λ ρ → bbGoto (⊆-lookup ρ lᵗ) ∷ AllExt-id
    compileCond (eOp op e e') lᵗ lᶠ = {!!}
    compileCond e@(eVar _) lᵗ lᶠ = {!!}
    compileCond e@(eApp _ _) lᵗ lᶠ = {!!}
    compileCond e@(eAss _ _) lᵗ lᶠ = {!!}
    compileCond (eIncrDecr p (incr ()) x) lᵗ lᶠ
    compileCond (eIncrDecr p (decr ()) x) lᵗ lᶠ



  -- record BBExt (Λ

  record WithBBs (Λ : Labels) (P : ∀ {Λ′} (ξ : Λ ⊆ Λ′) → Set) : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : BBs ext
      res   : P ext

  -- WithBBs Λ


  record CompRes (Ξ : MT) (Λ : Labels) : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : BBs ext
      res   : BBOrGoto Ξ Ext

  crBB : ∀{Ξ Λ} → BBOrGoto Ξ Λ → CompRes Ξ Λ
  crBB res = _ ∙ (λ ρ → AllExt-id) ∙ res

  crToBB : ∀ {Ξ Λ} → CompRes Ξ Λ → WithBBs Λ λ {Λ′} ξ → BB′ Ξ Λ′
  crToBB (ext ∙ bbs ∙ block bb) = ext ∙ bbs ∙ {!!}
  crToBB (ext ∙ bbs ∙ goto l) = {!!}


  mutual

    compileStm : ∀ {Γ mt}
        (s : Stm Σ rt Γ mt) {Λ Φ}
        (k : CompRes (Γ ▷ mt , Φ) Λ)
        → CompRes (Γ , Φ) Λ
        -- → ∃₂ λ Λₜ (ξ : Λ ⊆ Λₜ) → BBs (Γ , Φ) ξ
    compileStm s k = {!!}

    compileCond : ∀{Γ}
      (e : Exp` Σ Γ bool) {Λ Φ}
      (kᵗ kᶠ : CompRes (Γ , Φ) Λ)
      → CompRes (Γ , Φ) Λ
    compileCond (eConst false) kᵗ kᶠ = kᶠ
    compileCond (eConst true ) kᵗ kᶠ = kᵗ
    compileCond (eOp op e e') kᵗ kᶠ = {!!}
    compileCond e@(eVar _  )  kᵗ kᶠ = compileExp e $ crIfElse (eqBool true) kᵗ kᶠ
    compileCond e@(eApp _ _)  kᵗ kᶠ = compileExp e (block (λ ρ → bbIfElse (eqBool true) (gotoToBB kᵗ ρ) (gotoToBB kᶠ ρ)))
    compileCond e@(eAss _ _)  kᵗ kᶠ = compileExp e (block (λ ρ → bbIfElse (eqBool true) (gotoToBB kᵗ ρ) (gotoToBB kᶠ ρ)))
    compileCond (eIncrDecr p (incr ()) x) kᵗ kᶠ
    compileCond (eIncrDecr p (decr ()) x) kᵗ kᶠ

    -- Compiling composite conditionals.

    compileCondOp : ∀{Γ t}
      (op   : Op t bool)
      (e e' : Exp` Σ Γ t) {Λ Φ}
      (kt kf : CompRes (Γ , Φ) Λ)  -- kt: true, kf: false
      → CompRes (Γ , Φ) Λ

    compileCondOp (logic and) e e' kt kf = {!!}
    compileCondOp (logic or)  e e' kt kf = {!!}
    compileCondOp (cmp   op)  e e' kt kf =
      compileExp e  $ λ ρ  →
      compileExp e' $ λ ρ' →
      bbIfElse (cmp op) (gotoToBB kt (⊆-trans ρ ρ'))
                        (gotoToBB kf (⊆-trans ρ ρ'))
    compileCondOp (arith (plus ()))
    compileCondOp (arith (minus ()))
    compileCondOp (arith (times ()))
    compileCondOp (arith (div ()))
-- -}
-- -}
-- -}
-- -}

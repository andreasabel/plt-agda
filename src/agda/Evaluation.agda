module Evaluation where

open import Library
open import WellTypedSyntax
open import Environment public

-- We do not need a return statement when a function returns void.

data ResVal : ∀ t → Res t → Val t → Set where
  ret  : ∀{t} {v : Val t} → ResVal t (ret v) v
  cont : ResVal void cont _

_≡return_ : ∀{t} → Res t → Val t → Set
r ≡return v = ResVal _ r v

-- Lookup of variables

record _⊢_⇓ˣ_ {Γ} (γ : Env Γ) {t} (x : Var Γ t) (v : Val` t) : Set where
  module Var = Var⁻
  field
    {δ} : Frame (Var.Δ x)
    δ∈γ : (Var.Δ∈Γ x) ↦ δ ∈ γ
    v∈δ : (Var.t∈Δ x) ↦ just v ∈ δ

-- Pushing new value

_∙_≡_ : ∀{Γ} (γ : Env Γ) {t} (v : Entry` t) (γ' : Env (Γ ▷ ` t)) → Set
γ ∙ v ≡ γ' = γ' ≡ push v γ

-- Update of variables

-- data UpdateFrame {t} (v : Val t) : ∀{Δ} (x : t ∈ Δ) (δ δ′ : Frame Δ) → Set where
--   here : ∀{Γ} {δ : Env Γ} (v₀ : Val t)
--     → UpdateEnv v (here refl) (v₀ ∷ δ) (v ∷ δ)

-- data UpdateEnv {t} (v : Val t) : ∀{Γ} (x : Var Γ t) (γ γ′ : Env Γ) → Set where
--   here : ∀{Γ} {γ : Env Γ} (v₀ : Val t)
--     → UpdateFrame v
--     → UpdateEnv v (here refl) (δ ∷ γ) (δ′ ∷ γ)

_⊢_≔_⇓_ : ∀ {Γ} (γ : Env Γ) {t} (x : Var Γ t) (v : Val` t) (γ′ : Env Γ) → Set
γ ⊢ var x Δ∈Γ t∈Δ ≔ v ⇓ γ′ = -- UpdateEnv v x γ γ′
  List.All.UpdateAt (List.All.UpdateAt (λ _ → just v ≡_) t∈Δ) Δ∈Γ γ γ′

-- Evaluation of built-ins (non-deterministic).
-- A read can return any value of the correct type (except undefined).
-- A print returns void (side effect is ignored).

data _⊢_⇓ᵇ_ : ∀ {Δ} (vs : Vals Δ) {t} (b : Builtin (funType Δ t)) (v : Val t) → Set where
  evReadInt     : ∀ i → [] ⊢ bReadInt    ⇓ᵇ i
  evReadDouble  : ∀ d → [] ⊢ bReadDouble ⇓ᵇ d
  evPrintInt    : ∀ i → (i ∷ []) ⊢ bPrintInt    ⇓ᵇ _
  evPrintDouble : ∀ d → (d ∷ []) ⊢ bPrintDouble ⇓ᵇ _

-- Increment / decrement

data _~_⟨_⟩ᵖ {a}{A : Set a} (x : A) : ∀ (y : A) (p : PrePost) → Set a where
  refl : x ~ x ⟨ post ⟩ᵖ
  triv : ∀{y} → x ~ y ⟨ pre ⟩ᵖ

data _≡_±1_ : ∀{t} (v v' : Val` t) (k : IncrDecr t) → Set where

-- Operators

postulate
  _⟨_⟩_⇓ᵃ_ : ∀{t} (v : Val` t) (op : ArithOp t) (v' : Val` t) (w : Val` t) → Set
  _⟨_⟩_⇓ᶜ_ : ∀{t} (v : Val` t) (op : CmpOp t) (v' : Val` t) (b : Bool) → Set
  _⟨_⟩_⇓ˡ_ : ∀ (b₁ : Bool) (op : LogicOp) (b₂ : Bool) (b : Bool) → Set


data _⟨_⟩_⇓ᵒ_ : ∀{t t'} (v : Val` t) (op : Op t t') (v' : Val` t) (w : Val` t') → Set where

  evArith : ∀{t} {op : ArithOp t} {v₁ v₂ v : Val` t}
    → v₁ ⟨ op ⟩ v₂ ⇓ᵃ v
    → v₁ ⟨ arith op ⟩ v₂ ⇓ᵒ v

  evCmp : ∀{t} {op : CmpOp t} {v₁ v₂ : Val` t} {b : Bool}
    → v₁ ⟨ op ⟩ v₂ ⇓ᶜ b
    → v₁ ⟨ cmp op ⟩ v₂ ⇓ᵒ b

  evLogic : ∀{op : LogicOp} {b₁ b₂ b : Bool}
    → b₁ ⟨ op ⟩ b₂ ⇓ˡ b
    → b₁ ⟨ logic op ⟩ b₂ ⇓ᵒ b


--  γ ⊢ x ⇓ v ±=1 k ⇓ v′ , γ′

record _⊢_⇓_±=1_⇓_,_ {Γ t}
  (γ : Env Γ) (x : Var Γ t) (v : Val` t) (k : IncrDecr t) (v′ : Val` t) (γ′ : Env Γ) : Set where
  constructor evIncrDecr
  field
    loadVal  : γ ⊢ x ⇓ˣ v
    incDec   : v′ ≡ v ±1 k
    storeVal : γ ⊢ x ≔ v′ ⇓ γ′

--  γ ⊢ x ±=1 k ⇓ γ′

record _⊢_±=1_⇓_ {Γ t} (γ : Env Γ) (x : Var Γ t) (k : IncrDecr t) (γ′ : Env Γ) : Set where
  constructor packIncrDecr
  field
    {v}      : Val` t
    {v′}     : Val` t
    incrDecr : γ ⊢ x ⇓ v ±=1 k ⇓ v′ , γ′

-- Evaluation of expressions (non-deterministic partial big-step semantics).

mutual
  data _,_⊢_⇓ᵉ_,_ {Σ} (P : Prg Σ Σ) {Γ} (γ : Env Γ) :
    ∀ {t} (e : Exp Σ Γ t) (v : Val t) (γ' : Env Γ) → Set where

    evConst : ∀{t}{v : Val` t}
      → P , γ ⊢ eConst v ⇓ᵉ v , γ

    evVar : ∀{t} {x : Var Γ t} {v : Val` t}
      → γ ⊢ x ⇓ˣ v
      → P , γ ⊢ eVar x ⇓ᵉ v , γ

    evApp : ∀ {Δ Δ' t} (let ft = funType Δ t) {x : Name} {f : ft ∈ Σ} {ss : Stms Σ t [] Δ Δ'}
      → f ↦ (Δ' , ss) ∈ P                     → ∀ {es : Exps Σ Γ Δ} {vs : Vals Δ} {γ′ : Env Γ}
      → P , γ ⊢ es ⇓ᵉˢ vs , γ′                → ∀ {δ′ : Frame Δ'} {r : Res t} (let δ = List.All.map just vs)
      → P , (δ ∷ []) ⊢ ss ⇓ˢˢ r , (δ′ ∷ [])   → ∀ {v : Val t}
      → r ≡return v
      → P , γ ⊢ eApp (fun x f) es ⇓ᵉ v , γ′

    evBuiltin : ∀ {Δ} {es : Exps Σ Γ Δ} {vs : Vals Δ} {γ′ : Env Γ}
      → P , γ ⊢ es ⇓ᵉˢ vs , γ′       → ∀ {t} {b : Builtin (funType Δ t)} {v : Val t}
      → vs ⊢ b ⇓ᵇ v
      → P , γ ⊢ eBuiltin b es ⇓ᵉ v , γ′

    evIncrDecr : ∀{t} {p : PrePost} {k : IncrDecr t} {x : Var Γ t} {v v′ v″ : Val` t} {γ′}
      → γ ⊢ x ⇓ v ±=1 k ⇓ v′ , γ′
      → v″ ≡ ifPost p then v else v′
      → P , γ ⊢ eIncrDecr p k x ⇓ᵉ v″ , γ′

    evOp : ∀{t t′} {op : Op t t′} {e e′ : Exp` Σ Γ t} {v v′ : Val` t} {γ′ γ″ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ v , γ′
      → P , γ′ ⊢ e′ ⇓ᵉ v′ , γ″        → ∀{w}
      → v ⟨ op ⟩ v′ ⇓ᵒ w
      → P , γ ⊢ eOp op e e′ ⇓ᵉ w , γ″

    evAss : ∀{t} {e : Exp` Σ Γ t} {v : Val` t} {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ v , γ′            → ∀{x : Var Γ t} {γ″ : Env Γ}
      → γ′ ⊢ x ≔ v ⇓ γ″
      → P , γ ⊢ eAss x e ⇓ᵉ v , γ″

  data _,_⊢_⇓ᵉˢ_,_ {Σ} (P : Prg Σ Σ) {Γ} (γ : Env Γ) :
    ∀ {Δ} (es : Exps Σ Γ Δ) (vs : Vals Δ) (γ' : Env Γ) → Set where

    evNil : P , γ ⊢ [] ⇓ᵉˢ [] , γ

    evCons : ∀ {t} {e : Exp` Σ Γ t} {v : Val` t} {γ′}
      → P , γ ⊢ e ⇓ᵉ v , γ′           → ∀{Δ} {es : Exps Σ Γ Δ} {vs} {γ″}
      → P , γ′ ⊢ es ⇓ᵉˢ vs , γ″
      → P , γ ⊢ (e ∷ es) ⇓ᵉˢ (v ∷ vs) , γ″

  data _,_⊢_⇓ˢ_,_ {Σ} (P : Prg Σ Σ) {Γ} (γ : Env Γ) {rt} :
    ∀ {mt} (s : Stm Σ rt Γ mt) (r : Res rt) (γ' : Env (Γ ▷ mt)) → Set where

    evReturn : ∀ {e : Exp Σ Γ rt} {v : Val rt} {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ v , γ′
      → P , γ ⊢ sReturn e ⇓ˢ ret v , γ′

    evExp : ∀ {t} {e : Exp Σ Γ t} {v : Val t} {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ v , γ′
      → P , γ ⊢ sExp e ⇓ˢ cont , γ′

    evDecl :  ∀{t x}
      → P , γ ⊢ sInit {t = t} x nothing ⇓ˢ cont , push nothing γ

    evInit :  ∀{t x} {e : Exp` Σ Γ t} {v : Val` t} {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ v , γ′
      → P , γ ⊢ sInit x (just e) ⇓ˢ cont , push (just v) γ′

    -- evInit :  ∀{e : Exp Σ Γ t} {v : Val t} {γ′ : Env Γ}
    --   → P , γ ⊢ e ⇓ᵉ v , γ′   → ∀ {γ″ : Env (Γ ▷ just t)}
    --   → γ′ ∙ v ≡ γ″
    --   → P , γ ⊢ sInit e ⇓ˢ cont , γ″

    evBlock : ∀ {Δ} {ss : Stms Σ rt (List⁺.toList Γ) [] Δ} {r : Res rt} {δ : Frame Δ} {γ′ : Env Γ}
      → P , ([] ∷ γ) ⊢ ss ⇓ˢˢ r , (δ ∷ γ′)
      → P , γ ⊢ sBlock ss ⇓ˢ r , γ′

    -- while

    evWhileDone : ∀ {e : Exp` Σ Γ bool}  {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ false , γ′      → ∀{s : Stm Σ rt Γ void}
      → P , γ ⊢ sWhile e s ⇓ˢ cont , γ′

    evWhileStep : ∀ {e : Exp` Σ Γ bool} {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ true , γ′  → ∀{s : Stm Σ rt Γ void} {γ″ : Env Γ}
      → P , γ′ ⊢ s ⇓ˢ cont , γ″       → ∀{r : Res rt} {γ‴ : Env Γ}
      → P , γ″ ⊢ sWhile e s ⇓ˢ r , γ‴
      → P , γ ⊢ sWhile e s ⇓ˢ r , γ‴

    evWhileRet : ∀ {e : Exp` Σ Γ bool} {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ true , γ′  → ∀{s : Stm Σ rt Γ void} {γ″ : Env Γ} {v : Val rt}
      → P , γ′ ⊢ s ⇓ˢ ret v , γ″      → ∀{r : Res rt} {γ‴ : Env Γ}
      → P , γ ⊢ sWhile e s ⇓ˢ ret v , γ″

    -- if-else

    evIfThen : ∀ {e : Exp` Σ Γ bool} {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ true , γ′  → ∀{s s' : Stm Σ rt Γ void} {γ″ : Env Γ} {r : Res rt}
      → P , γ′ ⊢ s ⇓ˢ r , γ″
      → P , γ ⊢ sIfElse e s s' ⇓ˢ r , γ″

    evIfElse : ∀ {e : Exp` Σ Γ bool} {γ′ : Env Γ}
      → P , γ ⊢ e ⇓ᵉ false , γ′  → ∀{s s' : Stm Σ rt Γ void} {γ″ : Env Γ} {r : Res rt}
      → P , γ′ ⊢ s' ⇓ˢ r , γ″
      → P , γ ⊢ sIfElse e s s' ⇓ˢ r , γ″

  data _,_⊢_⇓ˢˢ_,_ {Σ} (P : Prg Σ Σ) {Γ} {Δ} (γ : Env (Δ  ∷ Γ)) {rt} :
    ∀ {Δ'} (ss : Stms Σ rt Γ Δ Δ') (r : Res rt) {Δ''} (γ' : Env (Δ'' ∷ Γ)) → Set where

    evNil : P , γ ⊢ [] ⇓ˢˢ cont , γ

    evCont : ∀ {mt} {s : Stm Σ rt (Δ ∷ Γ) mt} (let Γ′ = (Δ ∷ Γ) ▷ mt) {γ′ : Env Γ′}
      → P , γ ⊢ s ⇓ˢ cont , γ′      → ∀ {Δ'} {ss : Stms Σ rt Γ (Δ ▷ᵇ mt) Δ'} {r : Res rt} {γ″ : Env (Δ' ∷ Γ)}
      → P , γ′ ⊢ ss ⇓ˢˢ r , γ″
      → P , γ ⊢ (s ∷ ss) ⇓ˢˢ r , γ″

    evRet : ∀ {mt} {s : Stm Σ rt (Δ ∷ Γ) mt} {v : Val rt} (let Γ′ = (Δ ∷ Γ) ▷ mt) {γ′ : Env Γ′}
      → P , γ ⊢ s ⇓ˢ ret v , γ′      → ∀ {Δ'} {ss : Stms Σ rt Γ (Δ ▷ᵇ mt) Δ'}
      → P , γ ⊢ (s ∷ ss) ⇓ˢˢ ret v , γ′

-- Run a parameterless function (typically main).

record _⊢_⇓ᵖ_ {Σ} (P : Prg Σ Σ) {t} (main : funType [] t ∈ Σ) (v : Val t) : Set where
  constructor evMain
  field
    {Δ₀}    : Block
    {ss}    : Stms Σ t [] [] Δ₀
    hasMain : main ↦ (Δ₀ , ss) ∈ P
    {Δ}     : Block    -- We might not run ss to completion (return), thus, Δ might be shorter than Δ₀
    {δ}     : Frame Δ
    runMain : P , ([] ∷ []) ⊢ ss ⇓ˢˢ ret v , (δ ∷ [])

-- Run the program

_⇓ᵖ_ : ∀{Σ} (P : Program Σ) (v : Val` int) → Set
program P (fun _ main) ⇓ᵖ v = P ⊢ main ⇓ᵖ v

-- -}

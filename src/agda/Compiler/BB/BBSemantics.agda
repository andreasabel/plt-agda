
module Compiler.BB.BBSemantics where

open import Library
open import Library.AllExt

open import WellTypedSyntax
open import Environment
open import Evaluation

open import Compiler.BasicBlocks; open BBTypes
open import Compiler.JFSemantics

-- "Label semantics": mapping each label to its basic block

LS : (Σ : Sig) (rt : Type) (Λ : Labels) → Set
LS Σ rt Λ = List.All (BB Σ rt Λ) Λ

_++LS_ : ∀ {Σ rt Λ Λ'} {η : Λ ⊆ Λ'}
  → AllExt (BB Σ rt Λ') η
  → LS Σ rt Λ
  → LS Σ rt Λ'
_++LS_ {η = η} ƛ' ƛ = extendAll ƛ' (List.All.map (λ bb → weakBB bb η) ƛ)

module _ {Σ : Sig} (ms : Meths Σ Σ) where -- {rt : Type} (_⊢_⇓ᶠ_ : FunEvalT Σ) where

  mutual

    data _⊢_⇓ᶠ_ {Δ t} (δ : Frame Δ) (f : funType Δ t ∈ Σ) (v : Val t) : Set where

      evFun : ∀ (let bbMethod Λ entry ƛ = List.All.lookup ms f)
        → BBEval ƛ v (δ ∷ [] , []) entry
        → δ ⊢ f ⇓ᶠ v

    -- Big-step semantics of basic blocks.

  -- module _ {Λ : Labels} (ƛ : LS Σ rt Λ) (v : Val rt) where

    data BBEval {rt Λ} (ƛ : LS Σ rt Λ) (v : Val rt) : ∀ {Ξ} (ξ : MS Ξ) → BB Σ rt Λ Ξ → Set where

      -- Single jump-free instruction.

      evBB : ∀{Ξ Ξ'} {ξ ξ'} {jfs : JFs Σ Ξ Ξ'} {ctrl : BBCtrl Σ rt Λ Ξ'}

           → JFsEval _⊢_⇓ᶠ_ jfs ξ ξ'
           → BBCtrlEval ƛ v ξ' ctrl
           → BBEval ƛ v ξ (mkBB jfs ctrl)

    data BBCtrlEval {rt Λ} (ƛ : LS Σ rt Λ) (v : Val rt) : ∀ {Ξ} (ξ : MS Ξ) → BBCtrl Σ rt Λ Ξ → Set where

      -- Return.

      evReturn : ∀ {Γ Φ} {γ : Env Γ} {φ : Frame (Φ ▷ᵇ rt)}
           → ReturnVal rt v φ
           → BBCtrlEval ƛ v (γ , φ) bbReturn

      -- Goto l amounts to fetching the flowchart corresponding to l from ƛ and continue there.

      evGoto : ∀{Ξ l}{ξ : MS Ξ}
           → BBEval ƛ v ξ (List.All.lookup ƛ l)
           → BBCtrlEval ƛ v ξ (bbGoto l)

      -- Unary conditionals.

      evIfTrue : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {lᵗ : (Γ , Φ′) ∈ Λ} {bbᶠ : BB Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ true
           → BBEval ƛ v (γ , φ′) (List.All.lookup ƛ lᵗ)
           → BBCtrlEval ƛ v (γ , φ ) (bbIf c lᵗ bbᶠ)

      evIfFalse : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {lᵗ : (Γ , Φ′) ∈ Λ} {bbᶠ : BB Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ false
           → BBEval ƛ v (γ , φ′) bbᶠ
           → BBCtrlEval ƛ v (γ , φ ) (bbIf c lᵗ bbᶠ)

      -- Binary conditionals.

      evIfElseTrue : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {bbᵗ bbᶠ : BB Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ true
           → BBEval ƛ v (γ , φ′) bbᵗ
           → BBCtrlEval ƛ v (γ , φ ) (bbIfElse c bbᵗ bbᶠ)

      evIfElseFalse : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {bbᵗ bbᶠ : BB Σ rt Λ (Γ , Φ′)}
           → CondEval c φ φ′ false
           → BBEval ƛ v (γ , φ′) bbᶠ
           → BBCtrlEval ƛ v (γ , φ ) (bbIfElse c bbᵗ bbᶠ)

    -- data BBEval {rt Λ} (ƛ : LS Σ rt Λ) (v : Val rt) : ∀ {Ξ} (ξ : MS Ξ) → BB Σ rt Λ Ξ → Set where

    --   -- Single jump-free instruction.

    --   evExec : ∀{Ξ Ξ'} {ξ ξ'} {jf : JF Σ Ξ Ξ'} {bb : BB Σ rt Λ Ξ'}

    --        → JFEval _⊢_⇓ᶠ_ jf ξ ξ'
    --        → BBEval ƛ v ξ' bb
    --        → BBEval ƛ v ξ (bbExec jf bb)

    --   -- Return.

    --   evReturn : ∀ {Γ Φ} {γ : Env Γ} {φ : Frame (Φ ▷ᵇ rt)}
    --        → ReturnVal rt v φ
    --        → BBEval ƛ v (γ , φ) bbReturn

    --   -- Goto l amounts to fetching the flowchart corresponding to l from ƛ and continue there.

    --   evGoto : ∀{Ξ l}{ξ : MS Ξ}
    --        → BBEval ƛ v ξ (List.All.lookup ƛ l)
    --        → BBEval ƛ v ξ (bbGoto l)

    --   -- Unary conditionals.

    --   evIfTrue : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {lᵗ : (Γ , Φ′) ∈ Λ} {bbᶠ : BB Σ rt Λ (Γ , Φ′)}
    --        → CondEval c φ φ′ true
    --        → BBEval ƛ v (γ , φ′) (List.All.lookup ƛ lᵗ)
    --        → BBEval ƛ v (γ , φ ) (bbIf c lᵗ bbᶠ)

    --   evIfFalse : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {lᵗ : (Γ , Φ′) ∈ Λ} {bbᶠ : BB Σ rt Λ (Γ , Φ′)}
    --        → CondEval c φ φ′ false
    --        → BBEval ƛ v (γ , φ′) bbᶠ
    --        → BBEval ƛ v (γ , φ ) (bbIf c lᵗ bbᶠ)

    --   -- Binary conditionals.

    --   evIfElseTrue : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {bbᵗ bbᶠ : BB Σ rt Λ (Γ , Φ′)}
    --        → CondEval c φ φ′ true
    --        → BBEval ƛ v (γ , φ′) bbᵗ
    --        → BBEval ƛ v (γ , φ ) (bbIfElse c bbᵗ bbᶠ)

    --   evIfElseFalse : ∀{Γ Φ Φ′} {γ : Env Γ} {φ : Frame Φ} {φ′ : Frame Φ′} {c : Cond Φ Φ′} {bbᵗ bbᶠ : BB Σ rt Λ (Γ , Φ′)}
    --        → CondEval c φ φ′ false
    --        → BBEval ƛ v (γ , φ′) bbᶠ
    --        → BBEval ƛ v (γ , φ ) (bbIfElse c bbᵗ bbᶠ)

    data BOGEval {rt Λ} (ƛ : LS Σ rt Λ) (v : Val rt) : ∀ {Ξ} (ξ : MS Ξ) → BBOrGoto Σ rt Ξ Λ → Set where

      ev□Block' : ∀ {Ξ} {ξ : MS Ξ} {□bb : □ (BB′ Σ rt Ξ) Λ}
        → BBEval  ƛ v ξ (□bb ⊆-refl)
        → BOGEval ƛ v ξ (block □bb)

      ev□Goto' : ∀ {Ξ} {ξ : MS Ξ} {□l : □ (Ξ ∈_) Λ}
        → BBEval  ƛ v ξ (List.All.lookup ƛ (□l ⊆-refl))
        → BOGEval ƛ v ξ (goto □l)

    data CREval {rt Λ} (ƛ : LS Σ rt Λ) (v : Val rt) {Ξ} : (cr : CompRes Σ rt Ξ Λ) (ξ : MS Ξ) → Set where
      evCR : ∀{Λ'} {η : Λ ⊆ Λ'} {ƛ' : BBs Σ rt η} {bog ξ}
        → BOGEval (ƛ' ⊆-refl ++LS ƛ) v ξ bog
        → CREval ƛ v (η ∙ ƛ' ∙ bog) ξ

    pattern ev□Block ev = evCR (ev□Block' ev)
    pattern ev□Goto  ev = evCR (ev□Goto'  ev)

    -- CREval : ∀ {rt Λ} (ƛ : LS Σ rt Λ) (v : Val rt) {Ξ} (cr : CompRes Σ rt Ξ Λ) (ξ : MS Ξ) → Set
    -- CREval ƛ v (η ∙ ƛ' ∙ bog) ξ = BOGEval (ƛ' ⊆-refl ++LS ƛ) v ξ bog

      -- open WithBBs cr using () renaming (ext to Λ'; bbs to ƛ'; res to bb)
      -- field
      --   BBEval (ƛ ++ ƛ') v ξ bb
-- record MethEval {Σ} (m : Meth Σ (funType Δ rt)) (δ : Frame Δ) (v : Val rt) : Set


-- -}
-- -}
-- -}
-- -}
-- -}

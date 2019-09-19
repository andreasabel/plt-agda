module BasicBlocks where

open import Library
open import Library.AllExt

open import WellTypedSyntax
open import Value
open import FlowChart

module _ (Σ : Sig) (rt : Type) where

  data BB (Λ : Labels) : (Ξ : MT) → Set where
    -- Ends:
    bbGoto   : ∀{Ξ} (l : Ξ ∈ Λ) → BB Λ Ξ             -- goto join point (same Ξ)
    bbReturn : ∀{Γ Φ}           → BB Λ (Γ , Φ ▷ᵇ rt) -- return from function (stack is destroyed)
    -- Branching:
    bbIfElse : ∀{Γ Φ Φ'} (c : Cond Φ Φ') (bb bb' : BB Λ (Γ , Φ')) → BB Λ (Γ , Φ)
    -- Cons-like: Instruction
    bbExec     : ∀{Ξ Ξ'} (j : JF Σ Ξ Ξ') (bb : BB Λ Ξ') → BB Λ Ξ

  record Flat Λ Ξ : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : AllExt (BB Ext) ext
      bb    : BB Ext Ξ

  flat : ∀{Λ Ξ} → FC Σ rt Λ Ξ → Flat Λ Ξ
  flat (fcGoto l) = ⊆-refl ∙ AllExt-id ∙ bbGoto l
  flat fcReturn   = ⊆-refl ∙ AllExt-id ∙ bbReturn
  flat (fcExec j fc)
    with η ∙ bbs ∙ bb ← flat fc = η ∙ bbs ∙ bbExec j bb
  flat (fcIfElse c fc₁ fc₂)
    with η₁ ∙ bbs₁ ∙ bb₁ ← flat fc₁
       | η₂ ∙ bbs₂ ∙ bb₂ ← flat fc₂
    with record { leg₁    = ξ₁ ; leg₂ = ξ₂ } ← ⊆-pushoutˡ η₁ η₂
    with record { legExt₁ = bbs₁ᶜ ; legExt₂ = bbs₂ᶜ } ← AllExt-pushout bbs₁′ bbs₂′ = η ∙ {!!} ∙ {!!}
    where
    η   = ⊆-trans η₁ ξ₁
    bbs₁′ = AllExp-map (BB-map ξ₁) bbs₁
    bbs₂′ = AllExp-map (BB-map ξ₂) bbs₂
    bbs = AllExt-comp bbs₁′ bbs₁ᶜ
  flat (fcLet fc₁ fc₂) = {!!}
  flat (fcFix fc) = {!!}

module Compiler.BB.FCToBB where

open import Library
open import Library.AllExt
open import WellTypedSyntax

open import Compiler.FlowChart
open import Compiler.BasicBlocks

-- Flatten out label definitions from a flow chart

module _ (Σ : Sig) (rt : Type) where

  record Flat Λ Ξ : Set where
    constructor _∙_∙_
    field
      {Ext} : Labels
      ext   : Λ ⊆ Ext
      bbs   : □ (λ Λ′ → AllExt (BB Σ rt Λ′) ext) Ext
      bb    : □ (BB′ Σ rt Ξ) Ext

module _ {Σ : Sig} {rt : Type} where

  flat : ∀{Λ Ξ} → FC Σ rt Λ Ξ → Flat Σ rt Λ Ξ

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
    bs    : □ (λ Λ′ → BB Σ rt Λ′ _) _
    bs  τ = bbIfElse c (bb₁ (⊆-trans ξ₁ τ)) (bb₂ (⊆-trans ξ₂ τ))
    bbs   : □ (λ Λ′ → AllExt (BB Σ rt Λ′) η) Λ
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
    bbs   : □ (λ Λ′ → AllExt (BB Σ rt Λ′) η) Λ
    bbs τ = AllExt-join (lift (bbs₁ (⊆-trans ξ₁′ τ))) (bbs₂ (⊆-trans ξ₂ τ))

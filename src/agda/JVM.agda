-- JVM instructions

module JVM where

open import FlowChart

-- A method is a collection of snippets which are linear
-- sequences of instructions ending with a jump or a return.
-- A snippet is identified by a label.
-- We exclude fall-through to labels, rather we require
-- explicit jumps.  This keeps labels "free", rather than
-- identifying some (label,offset) pairs.
-- A final printing can insert labels and remove
-- jumps to just the next instruction address.


module _ (Σ : Sig) (Λ : Labels) where

  data JVM : (Γ Γ' : Cxt) (Φ Φ' : ST) → Set where

    -- Simple instructions, only modifying the stack
    si : ∀{Γ Φ Φ'} (si : SI Σ Γ Φ Φ') → JVM Γ Γ Φ Φ'

    -- Administrative instructions, modifying the context
    adm : ∀{Γ Γ' Φ} (adm : Adm Γ Γ') → JVM Γ Γ' Φ Φ

    -- Conditional jump on comparison: takes two values off stack
    ifCmp : ∀{Γ Φ t} (cmp : CompOp t) (l : (Γ , Φ) ∈ Label) → JVM Γ Γ (t ∷ t ∷ Φ) Φ
    -- Conditional jump on Boolean: takes one boolean off stack
    ifBool : ∀{Γ Φ t} (cmp : CompOp t) (l : (Γ , Φ) ∈ Label) → JVM Γ Γ (t ∷ t ∷ Φ) Φ

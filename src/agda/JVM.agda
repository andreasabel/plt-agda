-- JVM instructions

module JVM where

open import Library
open import WellTypedSyntax
open import FlowChart

-- Addresses are de Bruijn levels

-- n is the total size of the address space
-- n ≥ sum Γ

tsize : Ty → ℕ
tsize int    = 1
tsize double = 2
tsize bool   = 1


-- Address contexts of bounded size (number of words).
-- In these contexts, the left-most entry is on the left
-- (like in telescopes).

data ACxt : (n : ℕ) → Set where
  []  : ∀{n} → ACxt n
  _∷_ : ∀{n} t (α : ACxt n) → ACxt (tsize t + n)

data EqACxt : ∀{n m} → ACxt n → ACxt m → Set where
  []  : ∀{n m} → EqACxt ([] {n}) ([] {m})
  _∷_ : ∀ t {n m} {α : ACxt n} {β : ACxt m}
      → (eq : EqACxt α β)
      → EqACxt (t ∷ α) (t ∷ β)

WkACxt : ∀{n m} (α : ACxt n) (n≤m : n ≤ m) → ∃ λ (β : ACxt m) → EqACxt α β
WkACxt []           n≤m             = [] , []
WkACxt (int    ∷ α) (s≤s n≤m)       = let _ , e = WkACxt α n≤m in _ , int    ∷ e
WkACxt (bool   ∷ α) (s≤s n≤m)       = let _ , e = WkACxt α n≤m in _ , bool   ∷ e
WkACxt (double ∷ α) (s≤s (s≤s n≤m)) = let _ , e = WkACxt α n≤m in _ , double ∷ e

data Addr : (a : ℕ) (t : Ty) {n : ℕ} (α : ACxt n) → Set where
  here  : ∀{t n} {α : ACxt n} → Addr 0 t (t ∷ α)
  there : ∀{a t t' n} {α : ACxt n} → Addr a t α → Addr (tsize t' + a) t (t' ∷ α)

convAddr : ∀{n m} {α : ACxt n} {β : ACxt m} (e : EqACxt α β) {a} {t} (ad : Addr a t α) → Addr a t β
convAddr (t ∷ e) here       = here
convAddr (t ∷ e) (there ad) = there (convAddr e ad)

data BlockRev {n} (αfinal : ACxt n) : ∀ (Δ : Block) {m} (αcc : ACxt m) → Set where
  []  : BlockRev αfinal [] αfinal
  _∷_ : ∀ t {Δ m} {αcc : ACxt m}
      → BlockRev αfinal Δ (t ∷ αcc)
      → BlockRev αfinal (t ∷ Δ) αcc

data CxtRev {n} (αfinal : ACxt n) : ∀ (Γ : Cxt⁻) {m} (αcc : ACxt m) → Set where
  [] : CxtRev αfinal [] αfinal
  _∷_ : ∀{Δ Γ m m'} {αcc : ACxt m} {αcc' : ACxt m'}
      → BlockRev αfinal Δ αcc'
      → CxtRev αcc' Γ αcc
      → CxtRev αfinal (Δ ∷ Γ) αcc

revBlock : ∀ (Δ : Block) {m} (α : ACxt m) → ∃₂ λ n (αfinal : ACxt n) → BlockRev αfinal Δ α
revBlock []      α = _ , α , []
revBlock (t ∷ Δ) α =
  let n , α' , d     = revBlock Δ (t ∷ α)
  in  n , α' , t ∷ d

revCxt : ∀ (Γ : Cxt⁻) {m} (α : ACxt m) → ∃₂ λ n (αfinal : ACxt n) → CxtRev αfinal Γ α
revCxt []      α = _ , α , []
revCxt (Δ ∷ Γ) α =
  let n₁ , α₁ , d₁ = revCxt Γ α
      n₂ , α₂ , d₂ = revBlock Δ α₁
  in  n₂ , α₂ , (d₂ ∷ d₁)

-- CxtToA : (Γ : Cxt) →

{-
data Addr (t : Ty) : (Γ : Cxt) (n : ℕ) → Set where
  zero : ∀{n} → Addr t ((t ∷ []) ∷ []) n
-}

-- A method is a collection of snippets which are linear
-- sequences of instructions ending with a jump or a return.
-- A snippet is identified by a label.
-- We exclude fall-through to labels, rather we require
-- explicit jumps.  This keeps labels "free", rather than
-- identifying some (label,offset) pairs.
-- A final printing can insert labels and remove
-- jumps to just the next instruction address.


{-
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
-}

-- -}
-- -}

-- Simply-typed lambda terms with globally unique variables

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional
-- open import Data.List.Relation.Unary.Membership.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional
open import Data.List.Relation.Binary.Sublist.Propositional.Properties

postulate
  Base : Set

data Ty : Set where
  base : (o : Base) → Ty
  _⇒_ : (a b : Ty) → Ty

Cxt = List Ty
BVars = List Ty

variable
  a b : Ty
  Γ Δ : Cxt
  x : a ∈ Γ
  ys : BVars

-- There is a single global context of all variables used in the terms

module UniquelyNamed (Γ : Cxt) where

  BoundVars : BVars → Set
  BoundVars = (_⊆ Γ)

  variable
    β βₜ βᵤ yβ β\y : BoundVars ys

  data Tm : (a : Ty) (β : BoundVars ys) → Set where

    var : (x : a ∈ Γ)
        → Tm a (minimum _)

    abs : (y : a ∈ Γ)
          (t : Tm b β\y)
          (y#t : DisjointUnion (from∈ y) β yβ)
        → Tm (a ⇒ b) yβ

    app : (t : Tm (a ⇒ b) βₜ)
          (u : Tm a βᵤ)
          (t#u : DisjointUnion βₜ βᵤ β)
        → Tm b β

{-
    abs : (y : a ∈ Γ) (let [y] = from∈ y)
          (t : Tm b β)
          (y#t : Disjoint β [y])
          (let uβy = ⊆-disjoint-union y#t)
        → Tm (a ⇒ b) (UpperBound.sub uβy)

    app : (t : Tm (a ⇒ b) βₜ)
          (u : Tm a βᵤ)
          (t#u : Disjoint βₜ βᵤ)
          (let uβ = ⊆-disjoint-union t#u)
        → Tm b (UpperBound.sub uβ)
-- -}

module DeBruijn where

  data Tm (Δ : Cxt) : (a : Ty) → Set where
    var : (x : a ∈ Δ) → Tm Δ a
    abs : (t : Tm (a ∷ Δ) b) → Tm Δ (a ⇒ b)
    app : (t : Tm Δ (a ⇒ b)) (u : Tm Δ a) → Tm Δ b

open DeBruijn renaming (Tm to Exp)
open UniquelyNamed

-- Relating de Bruijn terms and uniquely named terms

variable
  δ : Δ ⊆ Γ

data _⊢_~_▷_ {Γ Δ : Cxt} (δ : Δ ⊆ Γ) : ∀{a} (e : Exp Δ a) {ys} (β : ys ⊆ Γ) (t : Tm Γ a β) → Set where
  var : δ ⊢ var x ~ minimum _ ▷ var (lookup δ x)

-- -}
-- -}

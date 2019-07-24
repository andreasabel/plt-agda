module Library.AllExt where

open import Library
open import Data.List.Relation.Binary.Sublist.Propositional using (_∷ʳ_)

module _ {ℓ p} {A : Set ℓ} (P : A → Set p) where

  variable
    a     : A
    xs ys : List A
    τ τ'  : xs ⊆ ys
    ps    : List.All P xs

  -- Insertion of elements in to a List.All

  data AllExt : (τ : xs ⊆ ys) → Set p where
    []   : AllExt []
    lift : AllExt τ → AllExt (refl {x = a} ∷ τ)
    _∷_  : P a → AllExt τ → AllExt (a ∷ʳ τ)

  variable
    es es' : AllExt τ

  AllExt-id : AllExt (⊆-refl {x = xs})
  AllExt-id {xs = []    } = []
  AllExt-id {xs = x ∷ xs} = lift AllExt-id

  AllExt-comp : AllExt τ → AllExt τ' → AllExt (⊆-trans τ τ')
  AllExt-comp ps        (q ∷ qs)  = q ∷ AllExt-comp ps qs
  AllExt-comp (p ∷ ps)  (lift qs) = p ∷ AllExt-comp ps qs
  AllExt-comp (lift ps) (lift qs) = lift (AllExt-comp ps qs)
  AllExt-comp []        []        = []

  -- Semantics of AllExt

  extendAll : ∀{τ : xs ⊆ ys} → List.All P xs → AllExt τ → List.All P ys
  extendAll ps       []       = ps
  extendAll (p ∷ ps) (lift e) = p ∷ extendAll ps e
  extendAll ps        (p ∷ e) = p ∷ extendAll ps e

  -- extendAll-id : {τ : xs ⊆ xs} (es : AllExt τ) → extendAll ps es ≡ ps
  -- extendAll-id {xs = []} {ps = ps} [] = refl
  -- extendAll-id {xs = x ∷ xs} {ps = p ∷ ps} (lift es) = cong (p ∷_) (extendAll-id es)
  -- extendAll-id {xs = x ∷ xs} {ps = p ∷ ps} (e ∷ es) = {!xs!}

  extendAll-id : extendAll ps (AllExt-id {xs = xs}) ≡ ps
  extendAll-id {xs = []    }               = refl
  extendAll-id {xs = x ∷ xs} {ps = p ∷ ps} = cong (p ∷_) extendAll-id

  extendAll-comp : extendAll (extendAll ps es) es' ≡ extendAll ps (AllExt-comp es es')
  extendAll-comp {ps = ps}     {es = []}      {es' = []}       = refl
  extendAll-comp {ps = p ∷ ps} {es = lift es} {es' = lift es'} = cong (p ∷_) (extendAll-comp {ps = ps})
  extendAll-comp {ps = ps}     {es = p ∷ es}  {es' = lift es'} = cong (p ∷_) (extendAll-comp {ps = ps})
  extendAll-comp {ps = ps}     {es = es}      {es' = p ∷ es'}  = cong (p ∷_) (extendAll-comp {ps = ps})

module Library.AllExt where

open import Library
open import Data.List.Relation.Binary.Sublist.Propositional using (_∷ʳ_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

module _ {ℓa ℓp} {A : Set ℓa} (P : A → Set ℓp) where

  variable
    a a'  : A
    xs ys : List A
    τ τ'  : xs ⊆ ys
    p     : P a
    ps    : List.All P xs

  -- Insertion of elements in to a List.All

  data AllExt : (τ : xs ⊆ ys) → Set ℓp where
    []   : AllExt []
    lift : AllExt τ → AllExt (refl {x = a} ∷ τ)
    _∷_  : P a → AllExt τ → AllExt (a ∷ʳ τ)

  variable
    es es' es₁ es₂ es₃ : AllExt τ

  hcong-lift : {es : AllExt τ} {es' : AllExt τ'}
    → τ ≡ τ'
    → es ≅ es'
    → lift {a = a} es ≅ lift {a = a} es'
  hcong-lift refl refl = refl

  hcong-∷ : {es : AllExt τ} {es' : AllExt τ'}
    → τ ≡ τ'
    → es ≅ es'
    → (p AllExt.∷ es) ≅ (p AllExt.∷ es')
  hcong-∷ refl refl = refl

  -- Category AllExt is a decoration of the morphisms of _⊆_.
  -- Decorated morphisms are closed under identity and composition.

  AllExt-id : AllExt (⊆-refl {x = xs})
  AllExt-id {xs = []    } = []
  AllExt-id {xs = x ∷ xs} = lift AllExt-id

  AllExt-comp : AllExt τ → AllExt τ' → AllExt (⊆-trans τ τ')
  AllExt-comp ps        (q ∷ qs)  = q ∷ AllExt-comp ps qs
  AllExt-comp (p ∷ ps)  (lift qs) = p ∷ AllExt-comp ps qs
  AllExt-comp (lift ps) (lift qs) = lift (AllExt-comp ps qs)
  AllExt-comp []        []        = []

  -- The category laws of AllExt depend on the category laws of _⊆_.

  -- We use heterogeneous equality.
  AllExt-idˡ : AllExt-comp AllExt-id es ≅ es
  AllExt-idˡ {es = []}     = refl
  AllExt-idˡ {es = lift _} = hcong-lift ⊆-trans-idˡ AllExt-idˡ
  AllExt-idˡ {es = _ ∷ _ } = hcong-∷    ⊆-trans-idˡ AllExt-idˡ

  -- ALT, using icong:
  -- AllExt-idˡ {τ = _ ∷  _} {es = lift _} = H.icong AllExt ⊆-trans-idˡ lift AllExt-idˡ
  -- AllExt-idˡ {τ = _ ∷ʳ _} {es = p ∷ _ } = H.icong AllExt {B = λ {τ} _ → AllExt (_ ∷ʳ τ)}
  --                                            ⊆-trans-idˡ
  --                                            (p ∷_)
  --                                            AllExt-idˡ

  -- AllExt-idˡ : subst AllExt (⊆-trans-idˡ {τ = τ}) ∘ AllExt-comp AllExt-id ≗ id
  -- AllExt-idˡ {τ = []}     [] = refl
  -- AllExt-idˡ {τ = y ∷ʳ τ} es = {! AllExt-idˡ {!!} !}
  -- AllExt-idˡ {τ = refl ∷ τ} (lift es) = {!!}

  AllExt-idʳ : AllExt-comp es AllExt-id ≅ es
  AllExt-idʳ {es = []    } = refl
  AllExt-idʳ {es = lift _} = hcong-lift ⊆-trans-idʳ AllExt-idʳ
  AllExt-idʳ {es = _ ∷ _ } = hcong-∷    ⊆-trans-idʳ AllExt-idʳ

  AllExt-assoc : AllExt-comp es₁ (AllExt-comp es₂ es₃) ≅ AllExt-comp (AllExt-comp es₁ es₂) es₃
  AllExt-assoc {es₁ = _      } {es₂ = _     } {es₃ = _ ∷  _} = hcong-∷    ⊆-trans-assoc AllExt-assoc
  AllExt-assoc {es₁ = _      } {es₂ = _ ∷ _ } {es₃ = lift _} = hcong-∷    ⊆-trans-assoc AllExt-assoc
  AllExt-assoc {es₁ = _ ∷ _  } {es₂ = lift _} {es₃ = lift _} = hcong-∷    ⊆-trans-assoc AllExt-assoc
  AllExt-assoc {es₁ = lift _ } {es₂ = lift _} {es₃ = lift _} = hcong-lift ⊆-trans-assoc AllExt-assoc
  AllExt-assoc {es₁ = []     } {es₂ = []    } {es₃ = []    } = refl

  -- Semantics of AllExt
  --
  -- There is a functor from AllExt into the subcategory All P of Set.

  extendAll : ∀{τ : xs ⊆ ys} → AllExt τ → List.All P xs → List.All P ys
  extendAll []       ps       = ps
  extendAll (lift es) (p ∷ ps) = p ∷ extendAll es ps
  extendAll  (p ∷ es) ps       = p ∷ extendAll es ps

  -- First functor law: identity.

  extendAll-id : extendAll (AllExt-id {xs = xs}) ps ≡ ps
  extendAll-id {xs = []    }               = refl
  extendAll-id {xs = x ∷ xs} {ps = p ∷ ps} = cong (p ∷_) extendAll-id

  -- Second functor law: composition.

  extendAll-comp : extendAll (AllExt-comp es es') ≗ extendAll es' ∘ extendAll es
  extendAll-comp {es = es}      {es' = p ∷ es'}  ps       = cong (p ∷_) (extendAll-comp ps)
  extendAll-comp {es = lift es} {es' = lift es'} (p ∷ ps) = cong (p ∷_) (extendAll-comp ps)
  extendAll-comp {es = p ∷ es}  {es' = lift es'} ps       = cong (p ∷_) (extendAll-comp ps)
  extendAll-comp {es = []}      {es' = []}       ps       = refl

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

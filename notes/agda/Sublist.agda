-- The category of sublists

module Sublist (E : Set) where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality

-- Objects

variable
  a b c       : E
  A B C A₁ A₂ : List E

-- Morphisms

infix  2 _⊆_
infixr 5 _∷_ _∷ʳ_

data _⊆_ : ∀ A B → Set where
  []   : [] ⊆ []
  _∷_  : ∀ a (τ : A ⊆ B) → a ∷ A ⊆ a ∷ B
  _∷ʳ_ : ∀ b (τ : A ⊆ B) → A ⊆ b ∷ B

-- Category operations

id : A ⊆ A
id {A = []   } = []
id {A = a ∷ A} = a ∷ id

infixr 4.5 _∙_

_∙_ : (τ : A ⊆ B) (σ : B ⊆ C) → A ⊆ C
τ       ∙ b ∷ʳ σ = b ∷ʳ (τ ∙ σ)
.a ∷ʳ τ ∙ a ∷  σ = a ∷ʳ (τ ∙ σ)
.a ∷  τ ∙ a ∷  σ = a ∷  (τ ∙ σ)
[]      ∙ []     = []

-- Category laws

variable
  τ τ₁ τ₂ τ₃ σ : A ⊆ B

idˡ : id ∙ τ ≡ τ
idˡ {τ = []    } = refl
idˡ {τ = a ∷  τ} = cong (a ∷_ ) idˡ
idˡ {τ = b ∷ʳ τ} = cong (b ∷ʳ_) idˡ

idʳ : τ ∙ id ≡ τ
idʳ {τ = []    } = refl
idʳ {τ = a ∷  τ} = cong (a ∷_ ) idʳ
idʳ {τ = b ∷ʳ τ} = cong (b ∷ʳ_) idʳ

assoc : τ₁ ∙ (τ₂ ∙ τ₃) ≡ (τ₁ ∙ τ₂) ∙ τ₃
assoc                               {τ₃ = d ∷ʳ τ₃} = cong (d ∷ʳ_) assoc
assoc                {τ₂ = c ∷ʳ τ₂} {τ₃ = c ∷  τ₃} = cong (c ∷ʳ_) assoc
assoc {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷  τ₂} {τ₃ = b ∷  τ₃} = cong (b ∷ʳ_) assoc
assoc {τ₁ = a ∷  τ₁} {τ₂ = a ∷  τ₂} {τ₃ = a ∷  τ₃} = cong (a ∷_ ) assoc
assoc {τ₁ = []}      {τ₂ = []}      {τ₃ = []     } = refl

-- Initial object

ε : [] ⊆ A
ε {A = []}    = []
ε {A = a ∷ A} = a ∷ʳ ε

[]⊆-irrelevant : {τ σ : [] ⊆ A} → τ ≡ σ
[]⊆-irrelevant {τ = []    } {σ = []    } = refl
[]⊆-irrelevant {τ = b ∷ʳ τ} {σ = b ∷ʳ σ} = cong (b ∷ʳ_) []⊆-irrelevant

-- Pullback

record WeakPullback (τ₁ : A₁ ⊆ B) (τ₂ : A₂ ⊆ B) : Set where
  constructor wpb
  field
    {intersection} : _
    inj₁ : intersection ⊆ A₁
    inj₂ : intersection ⊆ A₂
    square : inj₁ ∙ τ₁ ≡ inj₂ ∙ τ₂

pullback : ∀ (τ₁ : A₂ ⊆ B) (τ₂ : A₁ ⊆ B) → WeakPullback τ₁ τ₂
pullback ([]      ) ([]      ) = wpb [] [] refl
pullback (a  ∷  τ₁) (a  ∷  τ₂) = let wpb ι₁ ι₂ sq = pullback τ₁ τ₂ in wpb (a ∷ ι₁)   (a ∷ ι₂)   (cong (a  ∷_)  sq)
pullback (a₁ ∷  τ₁) (a₁ ∷ʳ τ₂) = let wpb ι₁ ι₂ sq = pullback τ₁ τ₂ in wpb (a₁ ∷ʳ ι₁) ι₂         (cong (a₁ ∷ʳ_) sq)
pullback (a₂ ∷ʳ τ₁) (a₂ ∷  τ₂) = let wpb ι₁ ι₂ sq = pullback τ₁ τ₂ in wpb ι₁         (a₂ ∷ʳ ι₂) (cong (a₂ ∷ʳ_) sq)
pullback (b  ∷ʳ τ₁) (b  ∷ʳ τ₂) = let wpb ι₁ ι₂ sq = pullback τ₁ τ₂ in wpb ι₁         ι₂         (cong (b  ∷ʳ_) sq)

-- pullback : ∀ (τ₁ : A₂ ⊆ B) (τ₂ : A₁ ⊆ B) → WeakPullback τ₁ τ₂
-- pullback ([]      ) ([]      ) = wpb [] [] refl
-- pullback (a  ∷  τ₁) (a  ∷  τ₂) with wpb ι₁ ι₂ sq ← pullback τ₁ τ₂ = wpb (a ∷ ι₁)   (a ∷ ι₂)   (cong (a  ∷_)  sq)
-- pullback (a₁ ∷  τ₁) (a₁ ∷ʳ τ₂) with wpb ι₁ ι₂ sq ← pullback τ₁ τ₂ = wpb (a₁ ∷ʳ ι₁) ι₂         (cong (a₁ ∷ʳ_) sq)
-- pullback (a₂ ∷ʳ τ₁) (a₂ ∷  τ₂) with wpb ι₁ ι₂ sq ← pullback τ₁ τ₂ = wpb ι₁         (a₂ ∷ʳ ι₂) (cong (a₂ ∷ʳ_) sq)
-- pullback (b  ∷ʳ τ₁) (b  ∷ʳ τ₂) with wpb ι₁ ι₂ sq ← pullback τ₁ τ₂ = wpb ι₁         ι₂         (cong (b  ∷ʳ_) sq)

record PullbackMorphism (pb₁ pb₂ : WeakPullback τ₁ τ₂) : Set where
  constructor pbm
  open WeakPullback
  field
    morphism : pb₁ .intersection ⊆ pb₂ .intersection
    -- the injections of pb₁ factor through the morphism
    tri₁     : pb₁ .inj₁ ≡ morphism ∙ pb₂ .inj₁
    tri₂     : pb₁ .inj₂ ≡ morphism ∙ pb₂ .inj₂

pullback-terminal : ∀ (pb : WeakPullback τ₁ τ₂) → PullbackMorphism pb (pullback τ₁ τ₂)
-- pullback-terminal {τ₁ = τ₁} {τ₂ = τ₂} (wpb α₁ α₂ sqa) with wpb ι₁ ι₂ sqi ← pullback τ₁ τ₂ = {!τ₁ τ₂ ι₁ ι₂ α₁ α₂!}
-- pullback-terminal {τ₁ = τ₁} {τ₂ = τ₂} (wpb α₁ α₂ sqa) with pullback τ₁ τ₂
-- pullback-terminal {τ₁ = τ₁} {τ₂ = τ₂} (wpb α₁ α₂ sqa) | wpb ι₁ ι₂ sqi = {!τ₁ τ₂ ι₁ ι₂ α₁ α₂!}
pullback-terminal {τ₁ = τ₁} {τ₂ = τ₂} (wpb α₁ α₂ sqa) with pullback τ₁ τ₂
pullback-terminal {τ₁ = []} {τ₂ = []} (wpb [] [] sqa) | wpb [] [] sqi = pbm [] refl refl
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ τ₂} (wpb (.a ∷ α₁) (.a ∷ α₂) sqa) | wpb (.a ∷ ι₁) (.a ∷ ι₂) sqi = {!pbm!}
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ τ₂} (wpb (.a ∷ʳ α₁) (.a ∷ʳ α₂) sqa) | wpb (.a ∷ ι₁) (.a ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ τ₂} (wpb (.a ∷ α₁) (.a ∷ α₂) sqa) | wpb (.a ∷ʳ ι₁) (.a ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ τ₂} (wpb (.a ∷ʳ α₁) (.a ∷ʳ α₂) sqa) | wpb (.a ∷ʳ ι₁) (.a ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ʳ τ₂} (wpb (.a ∷ α₁) () sqa) | wpb (.a ∷ʳ ι₁) [] sqi
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) [] sqa) | wpb (.a ∷ʳ ι₁) [] sqi = {!!}
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) (.a₁ ∷ α₂) sqa) | wpb (.a ∷ʳ ι₁) (a₁ ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) (.a₁ ∷ʳ α₂) sqa) | wpb (.a ∷ʳ ι₁) (a₁ ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) (.b ∷ α₂) sqa) | wpb (.a ∷ʳ ι₁) (b ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = a ∷ τ₁} {τ₂ = .a ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) (.b ∷ʳ α₂) sqa) | wpb (.a ∷ʳ ι₁) (b ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ τ₂} (wpb [] (.b ∷ʳ α₂) sqa) | wpb [] (.b ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ τ₂} (wpb (.a ∷ α₁) (.b ∷ʳ α₂) sqa) | wpb (a ∷ ι₁) (.b ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ τ₂} (wpb (.a ∷ʳ α₁) (.b ∷ʳ α₂) sqa) | wpb (a ∷ ι₁) (.b ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ τ₂} (wpb (.b₁ ∷ α₁) (.b ∷ʳ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (.b ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ τ₂} (wpb (.b₁ ∷ʳ α₁) (.b ∷ʳ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (.b ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb [] [] sqa) | wpb [] [] sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb [] (.b₁ ∷ʳ α₂) sqa) | wpb [] (b₁ ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.a ∷ α₁) (.a ∷ α₂) sqa) | wpb (a ∷ ι₁) (.a ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.a ∷ α₁) (.a ∷ʳ α₂) sqa) | wpb (a ∷ ι₁) (.a ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) (.a ∷ α₂) sqa) | wpb (a ∷ ι₁) (.a ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) (.a ∷ʳ α₂) sqa) | wpb (a ∷ ι₁) (.a ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.a ∷ α₁) (.a ∷ α₂) sqa) | wpb (a ∷ ι₁) (.a ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.a ∷ α₁) (.b₁ ∷ʳ α₂) sqa) | wpb (a ∷ ι₁) (b₁ ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) (.b₁ ∷ α₂) sqa) | wpb (a ∷ ι₁) (b₁ ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.a ∷ʳ α₁) (.b₁ ∷ʳ α₂) sqa) | wpb (a ∷ ι₁) (b₁ ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ α₁) () sqa) | wpb (b₁ ∷ʳ ι₁) [] sqi
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ʳ α₁) [] sqa) | wpb (b₁ ∷ʳ ι₁) [] sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ α₁) (.b₁ ∷ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (.b₁ ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ α₁) (.a ∷ʳ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (a ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ʳ α₁) (.a ∷ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (a ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ʳ α₁) (.a ∷ʳ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (a ∷ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ α₁) (.b₁ ∷ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (.b₁ ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ α₁) (.b₂ ∷ʳ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (b₂ ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ʳ α₁) (.b₂ ∷ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (b₂ ∷ʳ ι₂) sqi = {!!}
pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = .b ∷ʳ τ₂} (wpb (.b₁ ∷ʳ α₁) (.b₂ ∷ʳ α₂) sqa) | wpb (b₁ ∷ʳ ι₁) (b₂ ∷ʳ ι₂) sqi = {!!}

-- pullback-terminal {τ₁ = []} {τ₂ = []} (wpb [] [] sq) = pbm [] refl refl
-- pullback-terminal {τ₁ = a ∷  τ₁} {τ₂ = a ∷  τ₂} (wpb (a ∷ α₁) (a ∷ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = a ∷  τ₁} {τ₂ = a ∷  τ₂} (wpb (a ∷ʳ α₁) (a ∷ʳ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = a ∷  τ₁} {τ₂ = a ∷ʳ τ₂} (wpb (a ∷ʳ α₁) [] sq) = {!!}
-- pullback-terminal {τ₁ = a ∷  τ₁} {τ₂ = a ∷ʳ τ₂} (wpb (a ∷ʳ α₁) (a₁ ∷ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = a ∷  τ₁} {τ₂ = a ∷ʳ τ₂} (wpb (a ∷ʳ α₁) (b ∷ʳ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷  τ₂} (wpb []         (b ∷ʳ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷  τ₂} (wpb (a ∷ α₁) (b ∷ʳ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷  τ₂} (wpb (b₁ ∷ʳ α₁) (b ∷ʳ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷ʳ τ₂} (wpb [] [] sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷ʳ τ₂} (wpb []       (b₁ ∷ʳ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷ʳ τ₂} (wpb (a  ∷ α₁) (a ∷ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷ʳ τ₂} (wpb (a  ∷ α₁) (b₁ ∷ʳ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷ʳ τ₂} (wpb (b₁ ∷ʳ α₁) [] sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷ʳ τ₂} (wpb (b₁ ∷ʳ α₁) (a ∷ α₂) sq) = {!!}
-- pullback-terminal {τ₁ = b ∷ʳ τ₁} {τ₂ = b ∷ʳ τ₂} (wpb (b₁ ∷ʳ α₁) (b₂ ∷ʳ α₂) sq) = {!!}

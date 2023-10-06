-- Imports from the standard library and additional Haskell bindings.

module Library where

open import Agda.Builtin.Float public using (Float) renaming
  ( primFloatEquality to _==?ᵈ_
  ; primFloatLess     to _<?ᵈ_
  ; primNatToFloat    to ℕ→double
  ; primFloatPlus     to _+ᵈ_
  ; primFloatMinus    to _-ᵈ_
  ; primFloatTimes    to _*ᵈ_
  ; primFloatDiv      to _/ᵈ_
  )
1ᵈ = ℕ→double 1

-- Base modules

open import Data.Bool.Base     public using (Bool; true; false; _xor_; not; if_then_else_) hiding (module Bool)
open import Data.Char.Base     public using (Char)
open import Data.Empty         public using (⊥)
open import Data.Integer.Base  public using (ℤ; -[1+_]; +_)
open import Data.List.Base     public using (List; []; _∷_; [_]; _++_) hiding (module List)
open import Data.List.NonEmpty public using (List⁺; _∷_; _∷⁺_) hiding (module List⁺)

open import Data.Maybe.Base    public using (Maybe; nothing; just)
open import Data.Nat.Base      public using (ℕ; zero; suc; _+_; _≤_; s≤s) hiding (module ℕ)
open import Data.Product       public using (∃; ∃₂; _×_; _,_; proj₁; proj₂; map₂; uncurry)
  renaming (map to ∃-map)
open import Data.String.Base   public using (String) renaming (_++_ to _<>_)
open import Data.Sum.Base      public using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base     public using (⊤)

open import Function           public using (id; _∘_; _∘′_; _$_; case_of_)
open import Level              public using (Level; _⊔_)

open import IO.Primitive       public using (IO)

open import Relation.Binary    public using (Decidable; Rel)
open import Relation.Nullary   public using (¬_; Dec; yes; no)
open import Relation.Unary     public using (_∩_) renaming (_⊆_ to _⇒_)

-- Advanced modules (long names)

open import Relation.Binary.PropositionalEquality public using (_≗_; _≡_; refl; trans; cong; subst)
open import Relation.Nullary.Decidable            public using (⌊_⌋) renaming (map′ to mapDec)

open import Data.Nat.Properties                   public using (+-identityʳ)

open import Data.List.Membership.Propositional              public using (_∈_; _∉_)
open import Data.List.Relation.Unary.All                    public using ([]; _∷_; updateAt)
open import Data.List.Relation.Unary.Any                    public using (here; there)
open import Data.List.Relation.Unary.Any.Properties         public using (there-injective)

open import Data.List.Relation.Binary.Sublist.Propositional public
  using (_⊆_; []; _∷_; ⊆-refl; ⊆-trans; RawPushout; ⊆-pushoutˡ)
  renaming (_∷ʳ_ to ⊆-skip; lookup to ⊆-lookup)

open import Data.List.Relation.Binary.Sublist.Propositional.Properties public
  using (⊆-trans-idˡ; ⊆-trans-idʳ; ⊆-trans-assoc)

import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (_◅◅_ to _++_)
module Seq = Relation.Binary.Construct.Closure.ReflexiveTransitive
open Seq public using () renaming (Star to Seq; ε to []; _◅_ to _∷_) hiding (module Star)

pattern here! = here refl

-- Qualified imports:

-- module ∃ = Data.Product -- bad idea, Agda's printer cannot deal with it

module Bool where
  open import Data.Bool public using (_≟_; _∧_)

  _==_ : (b b' : Bool) → Bool
  b == b' = ⌊ b ≟ b' ⌋

module ℕ where
  open import Data.Nat.Base public
  open import Data.Nat.Properties public

module Integer where
  open import Data.Integer public

  infix 1 _==_ _<=_

  _==_ : (i j : ℤ) → Bool
  i == j = ⌊ i ≟ j ⌋

  _<=_ : (i j : ℤ) → Bool
  i <= j = ⌊ i ≤? j ⌋

  postulate div : (i j : ℤ) → ℤ
  {-# COMPILE GHC div = div #-}

-- Sublists.

⊆-wk1 : ∀{a}{A : Set a} {x : A} {xs : List A} → xs ⊆ x ∷ xs
⊆-wk1 = ⊆-skip _ ⊆-refl

-- Lists.

module List where
  open import Data.List.Base               public using ([_]; _++_; concat; map; foldl; foldr; reverse; sum; fromMaybe; intersperse)
  open import Data.List.Relation.Unary.All public using (All; []; _∷_) hiding (module All)
  open import Data.List.Categorical        public using (module TraversableM)

  module Any where

    open import Data.List.Relation.Unary.Any using (Any; here; there)

    toℕ : ∀ {a p} {A : Set a} {P : A → Set p} {xs} → Any P xs → ℕ
    toℕ (here  _) = zero
    toℕ (there i) = suc (toℕ i)

  module Membership where

    module _ {a} {A : Set a} where

      -- Equality of indices (uses K)

      _≟_ : ∀{x : A} {xs : List A} → Decidable (_≡_ {A = x ∈ xs})
      there i ≟ there j = mapDec (cong there) there-injective (i ≟ j)
      there _ ≟ here _  = no λ()
      here  _ ≟ there _ = no λ()
      here!   ≟ here!   = yes refl

      sameIndex : ∀ {x y} {xs : List A} (i : x ∈ xs) (j : y ∈ xs) → Dec (∃ λ x≡y → subst (_∈ xs) x≡y i ≡ j)
      sameIndex (there i) (there j) = mapDec
        (λ { (refl , eq) → refl , cong there eq      })
        (λ { (refl , eq) → refl , there-injective eq })
        (sameIndex i j)
      sameIndex (there _) (here  _) = no λ{ (refl , ()) }
      sameIndex (here  _) (there _) = no λ{ (refl , ()) }
      sameIndex (here!  ) (here!  ) = yes (refl , refl)

  module All where
    open import Data.List.Relation.Unary.All public using (lookup; map; tail; tabulate; reduce; zip)
    open import Data.List.Relation.Unary.All.Properties public using () renaming (++⁺ to _++_)

    module _ {a p} {A : Set a} {P : A → Set p} where

      indices : ∀ {xs : List A} → All (_∈ xs) xs
      indices = tabulate id

      reduceWithIndex : ∀ {b} {B : Set b} {xs : List A}
        (f : ∀ {x} → x ∈ xs → P x → B) → All P xs → List B
      reduceWithIndex f pxs = reduce (uncurry f) $ zip (indices , pxs)

      -- Update function for All

      data UpdateAt {r} {x} (R : Rel (P x) r)
        : ∀ {xs} (x∈xs : x ∈ xs) (vs vs' : All P xs) → Set (a ⊔ p ⊔ r) where

        here : ∀{xs} {vs : All P xs} {v v' : P x}
          → R v v'
          → UpdateAt R (here refl) (v ∷ vs) (v' ∷ vs)

        there : ∀{xs} {x∈xs : x ∈ xs} {vs vs' : All P xs} {y} {w : P y}
          → UpdateAt R x∈xs vs vs'
          → UpdateAt R (there x∈xs) (w ∷ vs) (w ∷ vs')

      Update : ∀ {x xs} (v : P x) (x∈xs : x ∈ xs) (vs vs' : All P xs) → Set (a ⊔ p)
      Update v = UpdateAt (λ _ → (v ≡_))

open List.All public using (here; there)

infixl 5 _++ʳ_

-- Reverse append.  (Soon in the std-lib as _ʳ++_.)

_++ʳ_ : ∀ {a} {A : Set a} → List A → List A → List A
xs ++ʳ ys = List.foldl (λ rev x → x ∷ rev) ys xs

module _ {a p} {A : Set a} {P : A → Set p} where

  -- Update in List.All

  _[_≔_]↝_ : ∀ {x xs}
    (vs : List.All P xs)
    (x∈xs : x ∈ xs)
    (v : P x)
    (vs' : List.All P xs) → Set (a ⊔ p)
  vs [ x∈xs ≔ v ]↝ vs' = List.All.Update v x∈xs vs vs'

  -- Membership in List.All  (In std-lib v1.2 as _[_]=_.)

  data _↤_∈_ {x} (v : P x) : ∀ {xs} → x ∈ xs → List.All P xs → Set (a ⊔ p) where

    here  : ∀ {xs} {vs : List.All P xs}
      → v ↤ here refl ∈ (v ∷ vs)

    there : ∀ {xs} {x∈xs : x ∈ xs} {vs : List.All P xs} {y} {w : P y}
      → v ↤ x∈xs ∈ vs
      → v ↤ there x∈xs ∈ (w ∷ vs)

  -- This is how we want to write it:

  _↦_∈_ : ∀ {x xs} → x ∈ xs → P x → List.All P xs → Set (a ⊔ p)
  x ↦ v ∈ vs = v ↤ x ∈ vs

-- Non-dependent association lists

AssocList : ∀{a b} {A : Set a} (B : Set b) (xs : List A) → Set (a ⊔ b)
AssocList B xs = List.All (λ _ → B) xs

module AssocList where

  module _ {a b} {A : Set a} {B : Set b} where

    -- Cons for non-dependent association lists.

    _↦_∷_ : ∀ (x : A) (v : B) {xs} (vs : AssocList B xs) → AssocList B (x ∷ xs)
    x ↦ v ∷ vs = _∷_ {x = x} v vs

    -- An non-dependent association list is unique
    -- if its range is a unique list.

    UniqueRange : ∀ {xs : List A} (vs : AssocList B xs) → Set (a ⊔ b)
    UniqueRange {xs} vs = ∀ {v x y} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs}
      (p : x∈xs ↦ v ∈ vs)
      (q : y∈xs ↦ v ∈ vs)
      → ∃ λ(x≡y : x ≡ y) → subst (_∈ xs) x≡y x∈xs ≡ y∈xs

    -- The empty association list is unique.

    []ᵘ : UniqueRange []
    []ᵘ () _

    -- ↦ v ∉ vs  means nothing points to v in vs.

    ↦_∉_ : ∀{xs} → B → AssocList B xs → Set (a ⊔ b)
    ↦_∉_ {xs} v vs = ∀{x : A} {x∈xs : x ∈ xs} → ¬ (x∈xs ↦ v ∈ vs)

    -- If nothing points to v we can cons it to a unique association list.

    _∷ᵘ_ : ∀{v xs x} {vs : AssocList B xs}
      (u : ↦ v ∉ vs) (us : UniqueRange vs) → UniqueRange (x ↦ v ∷ vs)
    (u ∷ᵘ us) here here = refl , refl
    (u ∷ᵘ us) here (there q) = case u q of λ()
    (u ∷ᵘ us) (there p) here = case u p of λ()
    (u ∷ᵘ us) (there p) (there q) with us p q
    ... | refl , refl = refl , refl

    -- The singleton association list is unique.

    sgᵘ : ∀ (x : A) (v : B) → UniqueRange (x ↦ v ∷ [])
    sgᵘ x v = (λ()) ∷ᵘ []ᵘ

    -- If something already points to v, we cannot add x↦v to
    -- an association list without losing uniqueness.

    head-not-unique : ∀{x y : A} {xs} {y∈xs : y ∈ xs} {v : B} {vs}
      (y↦v∈vs : y∈xs ↦ v ∈ vs) → ¬ UniqueRange (x ↦ v ∷ vs)
    head-not-unique y↦v∈vs us = case us here (there y↦v∈vs) of λ where
      (refl , ())

  module DecidableRange {b} {B : Set b} (_≟_ : Decidable (_≡_ {A = B})) where

    module _ {a} {A : Set a} where

      -- It is decidable whether something points to v in vs.

      ?↦_∈_ : ∀ (v : B) {xs : List A} (vs : AssocList B xs) →
        Dec (∃₂ λ x (x∈xs : x ∈ xs) → x∈xs ↦ v ∈ vs)

      ?↦ v ∈ [] = no λ{(x , () , _)}

      ?↦ v ∈ (w ∷ vs) with v ≟ w
      ?↦ v ∈ (v ∷ vs) | yes refl = yes (_ , here refl , here)

      ?↦ v ∈ (w ∷ vs) | no v≢w with ?↦ v ∈ vs
      ?↦ v ∈ (w ∷ vs) | no v≢w | yes (x , x∈xs , x∈xs↦v)
                               = yes (x , there x∈xs , there x∈xs↦v)
      ?↦ v ∈ (w ∷ vs) | no v≢w | no ¬p = no λ where
        (_ , _ , here)                  → v≢w refl
        (x , there x∈xs , there x∈xs↦v) → ¬p (x , x∈xs , x∈xs↦v)

      -- It is decidable whether we can cons to an association list
      -- without losing uniqueness.

      _↦_∷ᵘ?_ : ∀ (x : A) (v : B) {xs} {vs : AssocList B xs}
        (us : UniqueRange vs) → Dec (UniqueRange (x ↦ v ∷ vs))
      _↦_∷ᵘ?_ x v {xs} {vs} us with ?↦ v ∈ vs
      _↦_∷ᵘ?_ x v {xs} {vs} us | no ¬p = yes ((λ p → ¬p (_ , _ , p)) ∷ᵘ us)
      _↦_∷ᵘ?_ x v {xs} {vs} us | yes (_ , _ , y↦v∈vs) = no (head-not-unique y↦v∈vs)

-- Non-empty lists.

module List⁺ where
  open import Data.List.NonEmpty public using (toList; tail)

  All : ∀{a p} {A : Set a} (P : A → Set p) → List⁺ A → Set (p ⊔ a)
  All P xs = List.All P (toList xs)

module String where
  open import Data.String.Base public

-- Pretty printing

parens : String → String
parens s = "(" <> s <> ")"

sep2By : String → String → String → String
sep2By sep s s' = s <> sep <> s'

infixl 6 _<+>_ _<t>_ _<u>_

_<+>_ : String → String → String
_<+>_ = sep2By " "

_<t>_ : String → String → String
_<t>_ = sep2By "\t"

_<u>_ : String → String → String
_<u>_ = sep2By "_"

_</>_ : String → String → String
_</>_ = sep2By "/"

_<,>_ : String → String → String
_<,>_ = sep2By ", "

c>_ : String → String
c>_ = ";;" <+>_

t>_ : String → String
t> "" = ""
t>_   = "\t" <>_

vcat : List (List String) → List String
vcat = List.concat

vsep : List (List String) → List String
vsep = List.concat ∘ List.intersperse [ "" ] -- List.foldr (λ xs ys → xs ++ "" ∷ ys) []

-- Yoneda extension

module Yoneda {o h} {Ob : Set o} (Hom : Ob → Ob → Set h) where

  -- Hom(x,-): Covariant Hom functor

  Yonedaˡ : Ob → Ob → Set (o ⊔ h)
  Yonedaˡ y z = ∀{x} → Hom x y → Hom x z

  -- Hom(_,z): Contravariant Hom functor

  Yonedaʳ : Ob → Ob → Set (o ⊔ h)
  Yonedaʳ x y = ∀{z} → Hom y z → Hom x z

module YonedaEmbedding {o h} {Ob : Set o} {Hom : Ob → Ob → Set h}
  (_∙_ : ∀ {x y z} → Hom x y → Hom y z → Hom x z) (open Yoneda Hom) where

  yonedaˡ : ∀{x y} → Hom x y → Yonedaˡ x y
  yonedaˡ h g = g ∙ h

  yonedaʳ : ∀{x y} → Hom x y → Yonedaʳ x y
  yonedaʳ h g = h ∙ g

module YonedaProjection {o h} {Ob : Set o} {Hom : Ob → Ob → Set h}
  (id : ∀{x} → Hom x x) (open Yoneda Hom) where

  reifyˡ : ∀{x y} → Yonedaˡ x y → Hom x y
  reifyˡ f = f id

  reifyʳ : ∀{x y} → Yonedaʳ x y → Hom x y
  reifyʳ f = f id


-- Place overloaded monad operation in module

module ErrorMonad {e} {E : Set e} where

  Error : ∀{a} (A : Set a) → Set (e ⊔ a)
  Error A = E ⊎ A

  pattern fail err = inj₁ err
  pattern ok   val = inj₂ val

  return : ∀{a}{A : Set a} → A → Error A
  return = ok

  _>>=_ : ∀{a b} {A : Set a} {B : Set b} → Error A → (A → Error B) → Error B
  fail err >>= k = fail err
  ok   a   >>= k = k a

  _>>_ : ∀{b} {B : Set b} → Error ⊤ → Error B → Error B
  m >> m' = m >>= λ _ → m'

  _<&>_ : ∀{a b} {A : Set a} {B : Set b} → Error A → (A → B) → Error B
  fail e <&> f = fail e
  ok   a <&> f = ok (f a)

  _<$>_ : ∀{a b} {A : Set a} {B : Set b} → (A → B) → Error A → Error B
  f <$> m = m <&> f

  liftM2 : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    (f : A → B → C) → Error A → Error B → Error C
  liftM2 f m n = do
    a ← m
    f a <$> n

  throwError : ∀{a} {A : Set a} → E → Error A
  throwError = fail

  catchError : ∀{a} {A : Set a} → Error A → (E → Error A) → Error A
  catchError (fail e) h = h e
  catchError (ok a)   h = ok a


module IOMonad where
  open import IO.Primitive public using (return; _>>=_)

  infixl 1 _>>_

  _>>_  : ∀ {b} {B : Set b} → IO ⊤ → IO B → IO B
  _>>_ = λ m m' → m >>= λ _ → m'

  infixr 1 _=<<_

  _=<<_  : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → IO A → IO B
  k =<< m = m >>= k

{-# FOREIGN GHC import qualified Data.List #-}
{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Exit #-}
{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.FilePath #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified System.Process #-}

-- Binding more Haskell functions

postulate
  exitFailure    : ∀{a} {A : Set a} → IO A
  getArgs        : IO (List String)
  putStrLn       : String → IO ⊤
  readFiniteFile : String → IO String
  readInt        : IO ℤ
  readDouble     : IO Float
  takeBaseName   : String → String
  takeDirectory  : String → String
  writeFile      : String → String → IO ⊤
  callProcess    : String → List String → IO ⊤

{-# COMPILE GHC exitFailure    = \ _ _ -> System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs        = map Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC putStrLn       = System.IO.putStrLn . Data.Text.unpack #-}
{-# COMPILE GHC readFiniteFile = Data.Text.IO.readFile . Data.Text.unpack #-}
{-# COMPILE GHC readInt        = (System.IO.readLn :: System.IO.IO Integer) #-}
{-# COMPILE GHC readDouble     = (System.IO.readLn :: System.IO.IO Double)  #-}
{-# COMPILE GHC takeBaseName   = Data.Text.pack . System.FilePath.takeBaseName . Data.Text.unpack #-}
{-# COMPILE GHC takeDirectory  = Data.Text.pack . System.FilePath.takeDirectory . Data.Text.unpack #-}
{-# COMPILE GHC writeFile      = Data.Text.IO.writeFile . Data.Text.unpack #-}
{-# COMPILE GHC callProcess    = \ cmd -> System.Process.callProcess (Data.Text.unpack cmd) . Data.List.map Data.Text.unpack #-}

-- Showing builtin types

postulate
  printNat : ℕ → String
  printInt : ℤ → String
  printDouble : Float → String

{-# COMPILE GHC printNat    = \ i -> Data.Text.pack (show (i :: Integer)) #-}
{-# COMPILE GHC printInt    = \ i -> Data.Text.pack (show (i :: Integer)) #-}
{-# COMPILE GHC printDouble = \ d -> Data.Text.pack (show (d :: Double )) #-}

printBool : Bool → String
printBool true  = "true"
printBool false = "false"

-- -}
-- -}
-- -}

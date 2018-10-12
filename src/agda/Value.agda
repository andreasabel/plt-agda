-- Common definitions for operational semantics and interpreter.

module Value where

open import Library
open import WellTypedSyntax

-- Well-typed values.

-- Well-typed programs don't go wrong, but this is not the case for C--.
-- We have the following sources of undefinedness:
--
-- 1. Uninitialized variables:
--    can be handled on the level of environment.
--
-- 2. Functions terminating without returning a value:
--    can be handled at the point of function call.
--
-- 3. Division by zero:
--    Let it crash!

Val` : Ty → Set
Val` int    = ℤ
Val` double = Float
Val` bool   = Bool

Val : Type → Set
Val (` t)  = Val` t
Val void   = ⊤

Vals = List.All Val`

printVal` : ∀ t → Val` t → String
printVal` int    i = printInt i
printVal` double d = printDouble d
printVal` bool   b = printBool b

printVal : ∀ t → Val t → String
printVal (` t)  v = printVal` t v
printVal void   _ = "undefined"

-- Results of evaluating a statement

data Res (t : Type) : Set where
  ret : (v : Val t) → Res t
  cont : Res t

-- Environments.

-- An environment entry can be undefined,
-- but cannot be of type void.

Entry : Ty → Set
Entry t = Maybe (Val` t)

-- An environment is a list of frames.

Frame : Block → Set
Frame = List.All Entry

Env : Cxt → Set
Env = List⁺.All Frame

push : ∀{t} (v : Entry t) {Γ} (γ : Env Γ) → Env (Γ ▷ just t)
push v (δ ∷ γ) = (v ∷ δ) ∷ γ

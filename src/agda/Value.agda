-- Common definitions for operational semantics and interpreter.

module Value where

open import Library

-- Variables cannot have type void.

data Ty : Set where
  int double bool : Ty

-- Return types may be void.

data Type : Set where
  `_ : (t : Ty) → Type
  void : Type

infixr 100 `_

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

defaultVal` : ∀ t → Val` t
defaultVal` int    = + 0
defaultVal` double = 0.0
defaultVal` bool   = false

defaultVal : ∀ t → Val t
defaultVal (` t) = defaultVal` t
defaultVal void  = _

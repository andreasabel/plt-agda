-- Petterson-Synek trees
-- Set of commands and responses is fixed.

-- The `later` action of the Delay monad can be simulated by
-- a command with response set ⊤.

-- Uncatchable exceptions that like `exitFailure` can be simulated by
-- commands with response set ⊥.  They will stall the process, since
-- there can never be a response.  A translation to actual I/O
-- can interpret such commands by premature program termination.

{-# OPTIONS --sized-types #-}

module IOTree {c} {r} (Command : Set c) (Response : Command → Set r) where

open import Level using (_⊔_)
open import Size
open import Data.Unit
open import Function
open import IO.Primitive using () renaming (IO to OS)

mutual
  record IO (i : Size) {a} (A : Set a) : Set (a ⊔ c ⊔ r) where
    coinductive; constructor delay
    field
      force : {j : Size< i} → IO' j A

  data IO' (i : Size) {a} (A : Set a) : Set (a ⊔ c ⊔ r) where
    return' : (a : A) → IO' i A
    exec'   : (c : Command) (f : Response c → IO i A) → IO' i A

open IO public

-- Interpreting an IO tree in IO.Primitive, given an interpretation
-- of the individual commands.

module Run (runCmd : (c : Command) → OS (Response c)) where

  open IO.Primitive using (return; _>>=_)

  {-# TERMINATING #-}
  runIO : ∀ {A : Set} → IO ∞ A → OS A
  runIO m = case m .force of λ where
    (return' a) → return a
    (exec' c f) → runCmd c >>= runIO ∘ f

open Run public

-- Return in IO.

return : ∀{i} {a} {A : Set a} (a : A) → IO i A
return a .force = return' a

-- Execute in IO.

exec : ∀{i} {a} {A : Set a} (c : Command) (f : Response c → IO i A) → IO i A
exec c f .force = exec' c f

exec! : ∀{i} (c : Command) → IO i (Response c)
exec! c = exec c return

-- Monad.

infixl 2 _>>=_ _>>='_ _>>_

mutual
  _>>='_ : ∀{i a b} {A : Set a} {B : Set b} (m : IO' i A) (k : A → IO (↑ i) B) → IO' i B
  exec' c f >>=' k = exec' c λ r → f r >>= k
  return' a >>=' k = k a .force

  _>>=_ : ∀{i a b} {A : Set a} {B : Set b} (m : IO i A) (k : A → IO i B) → IO i B
  (m >>= k) .force = m .force >>=' k

_>>_ : ∀{i}{b} {B : Set b} (m : IO i ⊤) (k : IO i B) → IO i B
m >> k = m >>= λ _ → k

-- Functoriality.

_<$>'_ : ∀{i a b} {A : Set a} {B : Set b} (f : A → B) (m : IO' i A) → IO' i B
f <$>' m = m >>=' λ a → return (f a)

_<$>_ : ∀{i a b} {A : Set a} {B : Set b} (f : A → B) (m : IO i A) → IO i B
f <$> m = m >>= λ a → return (f a)

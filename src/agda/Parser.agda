module Parser where

open import Library using (List; Char; String)
open import AST using (Program)

{-# FOREIGN GHC import qualified Data.Text  #-}

{-# FOREIGN GHC import CPP.Abs  (Program)           #-}
{-# FOREIGN GHC import CPP.ErrM (Err (..))          #-}
{-# FOREIGN GHC import CPP.Par  (myLexer, pProgram) #-}

-- Error monad of BNFC

data Err (A : Set) : Set where
  ok   : A → Err A
  bad  : List Char → Err A

{-# COMPILE GHC Err = data Err ( Ok | Bad ) #-}

postulate
  parse : String → Err Program

{-# COMPILE GHC parse = pProgram . myLexer . Data.Text.unpack #-}

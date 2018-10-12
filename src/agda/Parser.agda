module Parser where

open import Library
open import AST using (Program)

{-# FOREIGN GHC import qualified Data.Text  #-}

{-# FOREIGN GHC import CPP.Abs  #-}
{-# FOREIGN GHC import CPP.ErrM #-}
{-# FOREIGN GHC import CPP.Lex  #-}
{-# FOREIGN GHC import CPP.Par  #-}

-- Error monad of BNFC

data Err (A : Set) : Set where
  ok   : A → Err A
  bad  : List Char → Err A

{-# COMPILE GHC Err = data Err ( Ok | Bad ) #-}

postulate
  parse : String → Err Program

{-# COMPILE GHC parse = pProgram . myLexer . Data.Text.unpack #-}

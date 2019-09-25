
module lab3 where

open import Library
open import CPP.AST     using (Program; printProgram)
open import CPP.Parser  using (Err; ok; bad; parseProgram)
open import TypeChecker using (printError; module CheckProgram)
open import BasicBlocks using (compileProgram)
open import ToJasmin    using (programToJVM)

check : String → String → String → IO ⊤
check dir name contents = do
  case parseProgram contents of λ where
    (bad cs) → do
      putStrLn "SYNTAX ERROR"
      putStrLn (String.fromList cs)
      exitFailure
    (Err.ok prg) → do
      case checkProgram prg of λ where
        (fail err) → do
          putStrLn "TYPE ERROR"
          putStrLn (printProgram prg)
          putStrLn "The type error is:"
          putStrLn (printError err)
          exitFailure
        (ErrorMonad.ok (Σ , funNames , prg')) → do
          let class = programToJVM name funNames $ compileProgram prg'
          _ ← mapM putStrLn class
          let jfile = name String.++ ".j"
              jtext = List.foldr (λ s s' → s String.++ "\n" String.++ s') "" class
          writeFile jfile jtext
          callProcess "jasmin" $ "-d" ∷ dir ∷ jfile ∷ []
          return _
  where
  open IOMonad
  open CheckProgram using (checkProgram)
  open ErrorMonad using (fail; ok)
  open List.TraversableM record{ IOMonad }

-- Display usage information and exit

usage : IO ⊤
usage = do
  putStrLn "Usage: lab3 <SourceFile>"
  exitFailure
  where open IOMonad

-- Parse command line argument and pass file contents to check.

lab3 : IO ⊤
lab3 = do
  file ∷ [] ← getArgs where _ → usage
  check (takeDirectory file) (takeBaseName file) =<< readFiniteFile file
  where open IOMonad

main = lab3

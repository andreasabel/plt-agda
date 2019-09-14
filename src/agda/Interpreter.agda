-- An unverified interpreter into I/O trees.

module Interpreter where

open import Library renaming (IO to OS)

open import WellTypedSyntax
open import Value
open import Environment
import IOTree

-- Commands for the interaction.

data Command : Set where
  cRuntimeError : Command  -- premature termination
  cTick         : Command  -- a sign of life "still running" (for general recursion)
  cPrintInt     : (i : ℤ) → Command
  cPrintDouble  : (d : Float) → Command
  cReadInt      : Command
  cReadDouble   : Command

-- Responses by the system.

Response : Command → Set
Response cRuntimeError    = ⊥      -- no response possible, OS is not coming back
Response cTick            = ⊤      -- trivial response without content
Response (cPrintInt    _) = ⊤
Response (cPrintDouble _) = ⊤
Response cReadInt         = ℤ      -- value input by the user
Response cReadDouble      = Float

open module IOT = IOTree Command Response using (IO; IO')

-- Guard a computation under a tick.

tick : ∀{i} {a} {A : Set a} → IO i A → IO' i A
tick m = IOT.exec' cTick λ _ → m

-- Arithmetics.

-- Increment and decrement for int and double.

incrDecr : ∀ {t} → IncrDecr t → Val` t → Val` t
incrDecr (incr int)    i = i Integer.+ + 1
incrDecr (decr int)    i = i Integer.- + 1
incrDecr (incr double) d = d +ᵈ 1ᵈ
incrDecr (decr double) d = d -ᵈ 1ᵈ

-- Division by zero is not handled.

arithmetic : ∀ {t} (op : ArithOp t) (v w : Val` t) → Val` t
arithmetic (plus  int)    i j  = i Integer.+ j
arithmetic (minus int)    i j  = i Integer.- j
arithmetic (times int)    i j  = i Integer.* j
arithmetic (div   int)    i j  = Integer.div i j
arithmetic (plus  double) d d' = d +ᵈ d'
arithmetic (minus double) d d' = d -ᵈ d'
arithmetic (times double) d d' = d *ᵈ d'
arithmetic (div   double) d d' = d /ᵈ d'

-- Comparison operators.

comparison : ∀ {t} (op : CmpOp t) (v w : Val` t)  → Val` bool
comparison (lt   int)    i j  = not (j Integer.<= i)
comparison (gt   int)    i j  = not (i Integer.<= j)
comparison (ltEq int)    i j  = i Integer.<= j
comparison (gtEq int)    i j  = j Integer.<= i
comparison {int} (eq)    i j  = i Integer.== j
comparison {int}(nEq)    i j  = not (i Integer.== j)
comparison (lt   double) d d' = d <?ᵈ d'
comparison (gt   double) d d' = d' <?ᵈ d
comparison (ltEq double) d d' = not (d' <?ᵈ d)
comparison (gtEq double) d d' = not (d <?ᵈ d')
comparison {double} eq   d d' = d ==?ᵈ d'
comparison {double} nEq  d d' = not (d ==?ᵈ d')
comparison {bool}   eq   b b' = b Bool.== b'
comparison {bool}   nEq  b b' = b xor b'

-- Manipulating the environment.

lookupFun : ∀{Σ ft} (f : Fun Σ ft) (prg : Prg Σ Σ) → Def Σ ft
lookupFun f prg = List.All.lookup prg f

lookupVar : ∀{Γ t} (x : Var Γ t) (γ : Env Γ) → Entry` t
lookupVar (var Δ∈Γ t∈Δ) γ = lookup (lookup γ Δ∈Γ) t∈Δ
  where open List.All

updateVar : ∀{Γ t} (x : Var Γ t) (v : Val` t) (γ : Env Γ) → Env Γ
updateVar (var Δ∈Γ t∈Δ) v = updateAt Δ∈Γ (updateAt t∈Δ (λ _ → just v))
  where open List.All


-- The program is fixed in the interpreter.

module Interpret {Σ : Sig} (prg : Program Σ) where

  -- Forward declaration of callFun (big mutual recursion!).
  -- This is called from the expression evaluator
  -- and calls the statement evaluator.

  callFun : ∀{rt i Δ} (f : Fun Σ (funType Δ rt)) (vs : Vals Δ) → IO i (Res rt)

  -- During evaluation of expressions, the program and the shape Γ
  -- of the environment remain fixed.

  module InterpretExpressions {Γ : Cxt} where

    -- The evaluation monad is basically λ i A → StateT (Env Γ) (IO i) A.

    record Eval (i : Size) (A : Set) : Set where
      field
        runEval : (γ : Env Γ) → IO i (A × Env Γ)
    open Eval public

    -- Monad.

    return : ∀{i A} (a : A) → Eval i A
    return a .runEval γ = IOT.return (a , γ)

    _>>=_ : ∀{i A B} (m : Eval i A) (k : A → Eval i B) → Eval i B
    (m >>= k) .runEval γ = m .runEval γ IOT.>>= λ where
      (a , γ') → k a .runEval γ'

    _=<<_ : ∀{i A B} (k : A → Eval i B) (m : Eval i A) → Eval i B
    k =<< m = m >>= k

    _>>_ : ∀{i B} (m : Eval i ⊤) (k : Eval i B) → Eval i B
    m >> m' = m >>= λ _ → m'

    -- Functoriality

    _<$>_ : ∀{i A B} (f : A → B) (m : Eval i A) → Eval i B
    f <$> m = m >>= λ a → return (f a)

    -- Accessing I/O.

    lift : ∀{i A} (m : IO i A) → Eval i A
    lift m . runEval γ = (_, γ) IOT.<$> m

    exec : ∀{i A} (c : Command) (f : Response c → Eval i A) → Eval i A
    exec c f .runEval γ = IOT.exec c λ r → f r .runEval γ

    exec! : ∀{i} (c : Command) → Eval i (Response c)
    exec! c = exec c return

    die : ∀{i A} → Eval i A
    die = exec cRuntimeError λ()

    -- Accessing the environment.

    get : ∀{i} → Eval i (Env Γ)
    get .runEval γ = IOT.return (γ , γ)

    modify : ∀{i} (f : Env Γ → Env Γ) → Eval i ⊤
    modify f .runEval γ = IOT.return (_ , f γ)

    -- The interpreter for expressions.

    -- Run a builtin function.

    evalBuiltin : ∀{i t ts} (f : Builtin (funType ts t)) (vs : Vals ts) → Eval i (Val t)
    evalBuiltin bReadInt    []        = exec! cReadInt
    evalBuiltin bReadDouble []        = exec! cReadDouble
    evalBuiltin bPrintInt    (i ∷ []) = exec! (cPrintInt i)
    evalBuiltin bPrintDouble (d ∷ []) = exec! (cPrintDouble d)

    -- Look up a variable. Crash if its value is undefined.

    evalVar : ∀{i t} (x : Var Γ t) → Eval i (Val` t)
    evalVar x = do
      just v ← lookupVar x <$> get
        where nothing → die
      return v

    -- Return nothing, which is only legal for type void.
    -- At other types, crash with runtime error.

    returnVoid : ∀{i} (rt : Type) → Eval i (Val rt)
    returnVoid void = return _
    returnVoid _    = die

    mutual

      -- Short-cutting logical operators.

      -- The second argument is only evaluated if the first
      -- does not determine the outcome alone.

      logical : ∀{i} (op : LogicOp) (v : Val` bool) (e : Exp` Σ Γ bool) → Eval i (Val` bool)
      logical and false e = return false
      logical and true  e = evalExp e
      logical or  true  e = return true
      logical or  false e = evalExp e

      -- Evaluate an expression.
      -- Includes expressions of type void.

      evalExp : ∀{i t} (e : Exp Σ Γ t) → Eval i (Val t)
      evalExp (eConst v)  = return v
      evalExp (eVar x)    = evalVar x
      evalExp (eApp {t = rt} f es) = do
        vs    ← evalExps es
        ret v ← lift $ callFun f vs
          where cont → returnVoid rt
        return v

      evalExp (eBuiltin f es) = evalBuiltin f =<< evalExps es

      evalExp (eIncrDecr p k x) = do
        v ← evalVar x
        let v' = incrDecr k v
        modify $ updateVar x v'
        return $ ifPost p then v else v'

      evalExp (eOp (arith op) e e') = do
        v  ← evalExp e
        v' ← evalExp e'
        return (arithmetic op v v')

      evalExp (eOp (cmp op) e e') = do
        v  ← evalExp e
        v' ← evalExp e'
        return (comparison op v v')

      evalExp (eOp (logic op) e e') = do
        v  ← evalExp e
        logical op v e'

      evalExp (eAss x e)     = do
        v ← evalExp e
        modify $ updateVar x v
        return v

      -- Evaluate a list of expressions (function arguments).
      -- This could be implemented with a mapM function for List.All.

      evalExps : ∀{i ts} (es : Exps Σ Γ ts) → Eval i (Vals ts)
      evalExps []       = return []
      evalExps (e ∷ es) = do
        v  ← evalExp e
        vs ← evalExps es
        return (v ∷ vs)

  -- During evaluation of statements the program is fixed.

  -- Return is modeled as exception which discards the environment.
  -- This is necessary, since we cannot statically predict the shape of the
  -- environment when a return happens before all local variables
  -- have been allocated.

  module InterpretStatements where

    open ErrorMonad using (fail; ok)

    record Eval (i : Size) (rt : Type) (Γ Γ' : Cxt) (A : Set) : Set where
      field
        runEval : (γ : Env Γ) → IO i (Val rt ⊎ (A × Env Γ'))
    open Eval public

    -- Monad.

    return : ∀{i rt Γ A} (a : A) → Eval i rt Γ Γ A
    return a .runEval γ = IOT.return (ok (a , γ))

    _>>=_ : ∀{i rt Γ Γ′ Γ″ A B}
      (m :     Eval i rt Γ  Γ′ A)
      (k : A → Eval i rt Γ′ Γ″ B)
             → Eval i rt Γ  Γ″ B
    (m >>= k) .runEval γ = m .runEval γ IOT.>>= λ where
      (ok (a , γ')) → k a .runEval γ'
      (fail v)      → IOT.return (fail v)

    _=<<_ : ∀{i rt Γ Γ′ Γ″ A B}
      (k : A → Eval i rt Γ′ Γ″ B)
      (m :     Eval i rt Γ  Γ′ A)
             → Eval i rt Γ  Γ″ B
    k =<< m = m >>= k

    _>>_ : ∀{i rt Γ Γ′ Γ″ B}
     (m : Eval i rt Γ  Γ′ ⊤)
     (k : Eval i rt Γ′ Γ″ B)
        → Eval i rt Γ  Γ″ B
    m >> m' = m >>= λ _ → m'

    -- Functoriality

    _<$>_ : ∀{i rt Γ Γ′ A B} (f : A → B) (m : Eval i rt Γ Γ′ A) → Eval i rt Γ Γ′ B
    f <$> m = m >>= λ a → return (f a)

    -- Accessing I/O.

    -- lift : ∀{i rt Γ A} (m : IO i A) → Eval i rt Γ Γ A
    -- lift m . runEval γ = (λ a → ok (a , γ)) IOT.<$> m

    -- exec : ∀{i rt Γ Γ' A} (c : Command) (f : Response c → Eval i rt Γ Γ' A) → Eval i rt Γ Γ' A
    -- exec c f .runEval γ = IOT.exec c λ r → f r .runEval γ

    -- die : ∀{i rt Γ A} → Eval i rt Γ Γ A
    -- die = exec cRuntimeError λ()

    -- Accessing the environment.

    -- get : ∀{i rt Γ} → Eval i rt Γ Γ (Env Γ)
    -- get .runEval γ = IOT.return (ok (γ , γ))

    -- Updating the environment.

    modify : ∀{i rt Γ Γ'} (f : Env Γ → Env Γ') → Eval i rt Γ Γ' ⊤
    modify f .runEval γ = IOT.return (ok (_ , f γ))

    -- Exception.

    throwError : ∀{i rt Γ Γ' A} (v : Val rt) → Eval i rt Γ Γ' A
    throwError v .runEval γ = IOT.return (fail v)

    -- Evaluate an expression.

    evalExp : ∀{Γ i rt t} (e : Exp Σ Γ t) → Eval i rt Γ Γ (Val t)
    evalExp {Γ} e .runEval γ = ok IOT.<$> M.evalExp e .M.runEval γ
      where module M = InterpretExpressions {Γ}

    mutual

      -- Executing a single statement.
      -- It returns the value of the new environment entry,
      -- should the statement be a declaration.

      evalStm : ∀{Γ rt i t} (s : Stm Σ rt Γ t) → Eval i rt Γ Γ (Entry t)

      evalStm (sReturn e) = throwError =<< evalExp e
      evalStm (sExp e)    = _ <$> evalExp e

      evalStm (sInit nothing) = return nothing

      evalStm (sInit (just e)) = just <$> evalExp e

      evalStm (sBlock ss) = do
        modify ([] ∷_)         -- push empty frame
        evalStms ss
        modify List.All.tail   -- pop frame

      evalStm (sWhile e s) = do
        true ← evalExp e where
          false → return _
        evalStm s
        -- The recursive call needs to be guarded:
        λ{ .runEval γ .IO.force → tick $ evalStm (sWhile e s) .runEval γ }

      evalStm (sIfElse e s s') = do
        b ← evalExp e
        if b then evalStm s else evalStm s'

      --     evalWhile : ∀{i} (e : Exp` Σ Γ bool) (s : Stm Σ rt Γ nothing) → Eval i rt Γ Γ ⊤
      --     evalWhile e s = do
      --       true ← evalExp e where
      --         vVoid → die
      --         false → return _
      --       evalStm s
      --       -- The recursive call needs to be guarded:
      --       -- λ{ .runEval γ .IO.force → tick $ evalWhile e s .runEval γ } -- POSSIBLE, but recurse is more readable
      --       recurse
      --       where
      --       recurse : ∀{i} → Eval i rt Γ Γ ⊤
      --       -- recurse .runEval γ .IO.force = tick $ evalStm (sWhile e s) .runEval γ
      --       recurse .runEval γ .IO.force = tick $ evalWhile e s .runEval γ

      -- Executing a list of statments.

      evalStms : ∀{i rt Γ Δ Δ'} (ss : Stms Σ rt Γ Δ Δ') → Eval i rt (Δ ∷ Γ) (Δ' ∷ Γ) ⊤
      evalStms []       = return _
      evalStms (s ∷ ss) = do
        v ← evalStm s
        modify (push v)
        evalStms ss

  -- end module InterpretStatements


  -- Calling a function.
  -- callFun : ∀{i rt Δ} (vs : Vals Δ) (f : Fun Σ (funType Δ rt)) → IO i (Res rt)

  -- We emit a tick since recursion is possibly non-terminating.
  -- (The function body is not structurally smaller than the function name.)

  callFun {rt} f vs .IOT.force = tick do

    -- Get the statements of the function.
    let (_ , ss) = lookupFun f (thePrg prg)

    -- Run them in the environment constructed from the arguments.
    let δ = List.All.map just vs
    evalStms ss .runEval (δ ∷ []) IOT.>>= λ where
      (fail v) → IOT.return (ret v)
      (ok _  ) → IOT.return cont

    where
    open InterpretStatements using (evalStms; runEval)
    open ErrorMonad using (fail; ok)

-- Evalulating a program.

evalProgram : ∀{i Σ} (prg : Program Σ) → IO i ⊤
evalProgram prg = _ IOT.<$> callFun (theMain prg) []
  where open Interpret prg

-- Run IO-trees in actual IO (Operating System)

module RunIO where

  open import IO.Primitive using (return; _>>=_)

  runCmd : (c : Command) → OS (Response c)
  runCmd cReadInt         = readInt
  runCmd cReadDouble      = readDouble
  runCmd (cPrintInt i)    = putStrLn (printInt    i)
  runCmd (cPrintDouble d) = putStrLn (printDouble d)
  runCmd cTick            = return _
  runCmd cRuntimeError    = do
    _ ← putStrLn ("INTERPRETER ERROR")
    _ ← putStrLn ("undefined value")
    exitFailure

open RunIO

-- Entry point: interpret program using native I/O interaction.

runProgram : ∀{Σ} (prg : Program Σ) → OS ⊤
runProgram prg = IOT.runIO runCmd (evalProgram prg)

-- -}
-- -}
-- -}
-- -}

module TypeChecker where

open import Data.String.Unsafe using (_≟_)

open import Library
open AssocList
open AssocList.DecidableRange _≟_

-- Use qualifiers A and I for abstract and internal syntax.

import AST as A

open import WellTypedSyntax hiding (Exp; Exp`)
private
  module I where
    open import WellTypedSyntax public using (Exp; Exp`)

-- Type errors.
--
-- Currently, these errors do not carry evidence that
-- something is wrong.  The type checker does not produce
-- evidence of ill-typedness in case of failure,
-- only of well-typedness in case of success.

data TypeError : Set where
  unboundVariable        : _
  unboundFunction        : _
  shadowedFunction       : _
  arithmeticTypeExpected : _
  voidExpression         : _
  typeMismatch           : _
  tooFewArguments        : _
  tooManyArguments       : _
  voidDeclaration        : _
  shadowingDeclaration   : _
  shadowingBuiltin       : _
  duplicateDefinition    : _
  duplicateParameter     : _
  noMain                 : _
  mainHasParameters      : _
  mainNoReturnInt        : _

printError : TypeError → String
printError = λ where
  unboundVariable        → "unbound variable"
  unboundFunction        → "unbound function"
  shadowedFunction       → "shadowed function"
  arithmeticTypeExpected → "arithmetic type expected"
  voidExpression         → "void expression detected"
  typeMismatch           → "type mismatch"
  tooFewArguments        → "too few arguments"
  tooManyArguments       → "too many arguments"
  voidDeclaration        → "cannot declare variable of type void"
  shadowingDeclaration   → "shadowing declaration"
  shadowingBuiltin       → "definition shadowing builtin"
  duplicateDefinition    → "duplicate definition"
  duplicateParameter     → "duplicate parameter"
  noMain                 → "main function missing"
  mainHasParameters      → "the main function may not have expect parameters"
  mainNoReturnInt        → "the main function must return int"

-- Names as coming from the abstract syntax are just strings.

Name = String

idToName : A.Id → Name
idToName (A.mkId x) = String.fromList x

-- Decorating list elements with unique identifiers.
--
-- NameDecorated xs is a decoration of the elements
-- of list xs with unique Names.

record NameDecorated {A : Set} (xs : List A) : Set where
  field
    scope : AssocList Name xs
    uniq  : UniqueRange scope
open NameDecorated

-- The empty list has the empty decoration.

[]ⁿ : ∀{A} → NameDecorated {A} []
[]ⁿ .scope = []
[]ⁿ .uniq  = []ᵘ

-- Signature of builtins.

BuiltinSig = NameDecorated builtins

-- NB.  The following decoration of the builtins list is a bit brittle,
-- as we do not see the abstract (names) and internal (indices) identifiers
-- side-by-side.

builtinSig : BuiltinSig
builtinSig .scope = "readInt" ∷ "readDouble" ∷ "printInt" ∷ "printDouble" ∷ []
-- Diagonal
builtinSig .uniq here                         here                         = refl , refl
builtinSig .uniq (there here)                 (there here)                 = refl , refl
builtinSig .uniq (there (there here))         (there (there here))         = refl , refl
builtinSig .uniq (there (there (there here))) (there (there (there here))) = refl , refl
-- Off the diagonal
builtinSig .uniq here                               (there (there (there (there ()))))
builtinSig .uniq (there (there (there (there ())))) here
builtinSig .uniq (there here)                       (there (there (there (there ()))))
builtinSig .uniq (there (there (there (there ())))) (there here)
builtinSig .uniq (there (there here))               (there (there (there (there ()))))
builtinSig .uniq (there (there (there (there ())))) (there (there here))
builtinSig .uniq (there (there (there here)))       (there (there (there (there ()))))
builtinSig .uniq (there (there (there (there ())))) (there (there (there here)))
builtinSig .uniq (there (there (there (there ())))) (there (there (there (there ()))))

-- Global signature for the type checker.

-- The type checking signature is a unique name-decoration of
-- the internal signature Σ that does not conflict with
-- the names of the builtins.

record TCSig (Σ : Sig) : Set where
  constructor mkTCSig
  field
    theSig         : NameDecorated {FunType} Σ
    noClashBuiltin :
      ∀ {x : Name} {ft : FunType} {f : Fun Σ ft} {b : ∃ Builtin} {b∈ : b ∈ builtins}
      (p : f ↦ x ∈ scope theSig) (q : b∈ ↦ x ∈ scope builtinSig) → ⊥
open TCSig

-- The empty signature is clash-free.

emptyTCSig : TCSig []
emptyTCSig .theSig = []ⁿ
emptyTCSig .noClashBuiltin ()

-- Local context for the type checker.

-- The type checking context is organized into blocks,
-- which are unique decorations of internal blocks.

TCBlock : (Δ : Block) → Set
TCBlock = NameDecorated {Ty}

-- Possibly empty list of blocks.

TCCxt⁻ : (Γ : Cxt⁻) → Set
TCCxt⁻ = List.All TCBlock

-- Non-empty list of blocks.

TCCxt : (Γ : Cxt) → Set
TCCxt = List⁺.All TCBlock

-- Querying the local context.

-- y ↦ x ∈Γ γ  states that index y points to identifier x in type checking context γ.

_↦_∈Γ_ : ∀{t Γ} (y : Var⁻ Γ t) (x : Name) (γ : TCCxt⁻ Γ) → Set
(var Δ∈Γ t∈Δ) ↦ x ∈Γ γ = ∃ λ δ → (Δ∈Γ ↦ δ ∈ γ) × (t∈Δ ↦ x ∈ scope δ)

-- x ∈?Γ γ  tests whether identifier x is bound in type checking environment γ.

_∈?Γ_ : ∀{Γ} (x : Name) (γ : TCCxt⁻ Γ) → Dec (∃₂ λ t (y : Var⁻ Γ t) → y ↦ x ∈Γ γ)
x ∈?Γ []      = no λ{(_ , var () _ , _)}
x ∈?Γ (δ ∷ γ) =
  case ?↦ x ∈ scope δ of λ where
    (yes (t , t∈Δ , p)) → yes (t , var (here refl) t∈Δ , δ , here , p)
    (no ¬p)             → case x ∈?Γ γ of λ where
      (yes (t , var Δ∈Γ t∈Δ , δ' , z , v)) → yes (t , var (there Δ∈Γ) t∈Δ , δ' , there z , v)
      (no ¬q)                              → no  λ where
        (t , var (here refl) t∈Δ , δ  , here    , p) → ¬p (t , t∈Δ , p)
        (t , var (there Δ∈Γ) t∈Δ , δ' , there z , v) → ¬q (t , var Δ∈Γ t∈Δ , δ' , z , v )

-- Type checking environment contains global signature and local context.

record TCEnv⁻ (Σ : Sig) (Γ : Cxt⁻) : Set where
  constructor tcEnv
  field
    tcSig : TCSig Σ
    tcCxt : TCCxt⁻ Γ
open TCEnv⁻

TCEnv : (Σ : Sig) (Γ : Cxt) → Set
TCEnv Σ Γ = TCEnv⁻ Σ (List⁺.toList Γ)

-- Type error monad

open ErrorMonad {E = TypeError} using (Error; fail; ok)

-- Conversion of types

type : A.Type → Type
type A.bool   = ` bool
type A.int    = ` int
type A.double = ` double
type A.void   = void

-- Checking expressions
---------------------------------------------------------------------------

-- During checking of expressions, the environment is fixed.

module CheckExpressions {Σ : Sig} {Γ : Cxt} (ξ : TCEnv Σ Γ) where

  -- The monad and its services.

  M = Error
  open ErrorMonad {E = TypeError} hiding (Error; fail; ok)

  -- Environment.

  lookupVar : (x : Name) → M (∃ λ t → Var Γ t)
  lookupVar x =
    case x ∈?Γ (tcCxt ξ) of λ where
      (yes (t , x' , _)) → return (t , x')
      (no ¬p)            → throwError unboundVariable

  lookupFun : (x : Name) → M (∃ λ ft → Builtin ft ⊎ Fun Σ ft)
  lookupFun x = do
    -- Check that function is not shadowed by a variable.
    catchError (do _ ← lookupVar x; throwError shadowedFunction) λ where
      unboundVariable → do
        -- If not, check for builtin function.
        case ?↦ x ∈ scope builtinSig of λ where
          (yes ((ft , b) , _ )) → return (ft , inj₁ b)
          (no _) → do
            -- Finally, look in the function signature.
            let σ = theSig (tcSig ξ)
            case ?↦ x ∈ scope σ of λ where
              (yes (ft , f , _)) → return (ft , inj₂ f)
              (no _)             → throwError unboundFunction
      err → throwError err

  -- The expression checker.

  -- The type of expressions is fixed.
  Exp  = I.Exp Σ Γ
  Exp` = I.Exp` Σ Γ

  -- Inference returns an expression and its type.
  Infer  = M (∃ λ (t : Type) → Exp t)
  Infer` = M (∃ λ (t : Ty)  → Exp` t)

  mutual

    -- Type inference.

    inferExp : (e : A.Exp) → Infer

    inferExp A.eTrue       = return (` bool   , eConst true)
    inferExp A.eFalse      = return (` bool   , eConst false)
    inferExp (A.eInt i)    = return (` int    , eConst i)
    inferExp (A.eDouble d) = return (` double , eConst d)

    inferExp (A.eId x) = do
      (t , x') ← lookupVar (idToName x)
      return (` t , eVar x')

    inferExp (A.eApp x es) = do
      (funType Δ t , k) ← lookupFun (idToName x)
      es' ← checkExps es Δ
      case k of λ where
        (inj₁ b) → return (t , eBuiltin b es')
        (inj₂ f) → return (t , eApp f es')

    inferExp (A.ePostIncr x)  = inferIncrDecr post incr x
    inferExp (A.ePostDecr x)  = inferIncrDecr post decr x
    inferExp (A.ePreIncr  x)  = inferIncrDecr pre  incr x
    inferExp (A.ePreDecr  x)  = inferIncrDecr pre  decr x

    inferExp (A.eTimes e₁ e₂) = inferArith times e₁ e₂
    inferExp (A.eDiv   e₁ e₂) = inferArith div   e₁ e₂
    inferExp (A.ePlus  e₁ e₂) = inferArith plus  e₁ e₂
    inferExp (A.eMinus e₁ e₂) = inferArith minus e₁ e₂

    inferExp (A.eLt    e₁ e₂) = inferCmp lt   e₁ e₂
    inferExp (A.eGt    e₁ e₂) = inferCmp gt   e₁ e₂
    inferExp (A.eLtEq  e₁ e₂) = inferCmp ltEq e₁ e₂
    inferExp (A.eGtEq  e₁ e₂) = inferCmp gtEq e₁ e₂

    inferExp (A.eEq    e₁ e₂) = inferEq eq  e₁ e₂
    inferExp (A.eNEq   e₁ e₂) = inferEq nEq e₁ e₂

    inferExp (A.eAnd   e₁ e₂) = (` bool ,_) <$> checkLogic and e₁ e₂
    inferExp (A.eOr    e₁ e₂) = (` bool ,_) <$> checkLogic or  e₁ e₂

    inferExp (A.eAss x e) = do
      (t , x') ← lookupVar (idToName x)
      e' ← checkExp` e t
      return (` t , eAss x' e')

    -- Infer the type of an expression and check that it is not void.

    inferExp` : (e : A.Exp) → Infer`
    inferExp` e = do
      (` t , e') ← inferExp e
        where _ → throwError voidExpression
      return (t , e')

    -- Type checking.
    -- Calls inference and checks inferred type against given type.

    checkExp : (e : A.Exp) (t : Type) → M (Exp t)
    checkExp e t = do
      (t' , e') ← inferExp e
      case t' TypeEq.≟ t of λ where
        (yes t'≡t) → return (subst Exp t'≡t e')
        (no t'≢t)  → throwError typeMismatch

    checkExp` : (e : A.Exp) (t : Ty) → M (Exp` t)
    checkExp` e t = checkExp e (` t)

    -- Check a list of function arguments.

    checkExps : (es : List A.Exp) (Δ : Block) → M (Exps Σ Γ Δ)
    checkExps []       []      = return []
    checkExps []       (t ∷ Δ) = throwError tooFewArguments
    checkExps (e ∷ es) []      = throwError tooManyArguments
    checkExps (e ∷ es) (t ∷ Δ) = do
      e'  ← checkExp` e t
      es' ← checkExps es Δ
      return (e' ∷ es')

    -- Operators.

    -- Infer the type of an expression and ensure that it is numerical

    inferArithExp : (e : A.Exp) → M (∃₂ λ t (a : ArithType t) → Exp` t)
    inferArithExp e = do
      (t , e') ← inferExp` e
      case arithType? t of λ where
        (yes a) → return (t , a , e')
        (no ¬a) → throwError arithmeticTypeExpected

    -- Type inference for increment/decrement expressions.

    inferIncrDecr : (p : PrePost) (k : ∀ {t} (a : ArithType t) → IncrDecr t) (x : A.Id) → Infer
    inferIncrDecr p k x = do
      (t , x') ← lookupVar (idToName x)
      case arithType? t of λ where
        (yes a) → return (` t , eIncrDecr p (k a) x')
        (no ¬a) → throwError arithmeticTypeExpected

    -- Type inference for binary operators.

    -- Arithmetical operators.

    inferArith : (op : ∀{t} (a : ArithType t) → ArithOp t) (e₁ e₂ : A.Exp) → Infer
    inferArith op e₁ e₂ = do
      (t , a , e₁') ← inferArithExp e₁
      e₂' ← checkExp` e₂ t
      return (` t , eOp (arith (op a)) e₁' e₂')

    -- Comparison operators.

    inferCmp : (op : ∀{t} (a : ArithType t) → CmpOp t) (e₁ e₂ : A.Exp) → Infer
    inferCmp op e₁ e₂ = do
      (t , a , e₁') ← inferArithExp e₁
      e₂' ← checkExp` e₂ t
      return (` bool , eOp (cmp (op a)) e₁' e₂')

    -- Equality operators.

    inferEq : (op : ∀{t} → CmpOp t) (e₁ e₂ : A.Exp) → Infer
    inferEq op e₁ e₂ = do
      (t , e₁') ← inferExp` e₁
      e₂' ← checkExp` e₂ t
      return (` bool , eOp (cmp op) e₁' e₂')

    -- Logical operators (not overloaded).

    checkLogic : (op : LogicOp) (e₁ e₂ : A.Exp) → M (Exp` bool)
    checkLogic op e₁ e₂ = liftM2 (eOp (logic op)) (checkExp` e₁ bool) (checkExp` e₂ bool)

-- The statement checker calls the expression checker.
-- Exported interface of expression checker:

-- Monad for checking expressions

record TCExp Σ Γ (A : Set) : Set where
  field
    runTCExp : TCEnv Σ Γ → Error A
open TCExp

inferExp : ∀{Σ Γ} (e : A.Exp) → TCExp Σ Γ (∃ λ (t : Type) → I.Exp Σ Γ t)
inferExp e .runTCExp ξ = CheckExpressions.inferExp ξ e

checkExp : ∀{Σ Γ} (e : A.Exp) (t : Type) → TCExp Σ Γ (I.Exp Σ Γ t)
checkExp e t .runTCExp ξ = CheckExpressions.checkExp ξ e t

checkExp` : ∀{Σ Γ} (e : A.Exp) (t : Ty) → TCExp Σ Γ (I.Exp` Σ Γ t)
checkExp` e t .runTCExp ξ = CheckExpressions.checkExp` ξ e t

-- Checking statements.
---------------------------------------------------------------------------

-- Monad for checking statements.

-- Variable declarations can be inserted into the top block, thus,
-- we need to treat the top block as mutable state.

record TCStm Σ Γ Δ Δ' (A : Set) : Set where
  field
    runTCStm : TCEnv⁻ Σ Γ → TCBlock Δ → Error (A × TCBlock Δ')

-- Signature and return type stay fixed during checking of expressions.

module CheckStatements {Σ : Sig} {rt : Type} where
  open TCStm public

  -- TCStm is a monad.

  -- Return.

  return : ∀{Γ Δ A} (a : A) → TCStm Σ Γ Δ Δ A
  return a .runTCStm ξ δ = ok (a , δ)

  -- Bind.

  _>>=_ : ∀{Γ Δ Δ′ Δ″ A B}
    (m :     TCStm Σ Γ Δ  Δ′ A)
    (k : A → TCStm Σ Γ Δ′ Δ″ B)
           → TCStm Σ Γ Δ  Δ″ B

  (m >>= k) .runTCStm ξ δ =
    case m .runTCStm ξ δ of λ where
      (fail err)    → fail err
      (ok (a , δ')) → k a .runTCStm ξ δ'

  -- Sequence.

  _>>_  : ∀{Γ Δ Δ′ Δ″ B}
    (m  : TCStm Σ Γ Δ  Δ′ ⊤)
    (m' : TCStm Σ Γ Δ′ Δ″ B)
        → TCStm Σ Γ Δ  Δ″ B
  m >> m' = m >>= λ _ → m'

  -- Map.

  _<$>_ : ∀{Γ Δ Δ' A B} (f : A → B) → TCStm Σ Γ Δ Δ' A → TCStm Σ Γ Δ Δ' B
  f <$> m = m >>= (return ∘′ f)

  -- Error raising.

  throwError : ∀{Γ Δ Δ' A} → TypeError → TCStm Σ Γ Δ Δ' A
  throwError err .runTCStm ξ δ = fail err

  -- Lifting a TCExp computation into TCStm.

  lift : ∀{Γ Δ A} (m : TCExp Σ (Δ ∷ Γ) A) → TCStm Σ Γ Δ Δ A
  lift m .runTCStm (tcEnv σ γ) δ =
    case m .runTCExp (tcEnv σ (δ ∷ γ)) of λ where
      (fail err) → fail err
      (ok a)     → ok (a , δ)

  -- Service functions for the top block.

  -- Start a new block.

  newBlock : ∀{Γ Δ Δ' A B} (f : A → B) (m : TCStm Σ (Δ ∷ Γ) [] Δ' A) → TCStm Σ Γ Δ Δ B
  newBlock f m .runTCStm (tcEnv σ γ) δ =

    -- Add the top block to the context
    -- and run the subcomputation in an empty block.

    case m .runTCStm (tcEnv σ (δ ∷ γ)) []ⁿ of λ where
      (fail err)   → fail err  -- Here, err changes into a different context.
      (ok (a , _)) → ok (f a , δ)

  -- Add a variable declaration.

  addVar : ∀{Γ Δ} (x : Name) t → TCStm Σ Γ Δ (t ∷ Δ) ⊤
  addVar {Δ = Δ} x t .runTCStm ξ δ =
    -- Try to uniquely extend the top block.
    case t ↦ x ∷ᵘ? uniq δ of λ where
      (yes us) → ok (_ , record { uniq = us })
      (no _)  → fail shadowingDeclaration

  -- Checking expressions.

  -- Signature and return type stay fixed for checking statements.

  CheckStm = λ Γ Δ Δ' → TCStm Σ Γ Δ Δ' (Stms Σ rt Γ Δ Δ')

  returnStm : ∀ {Γ Δ} (s : Stm Σ rt (Δ ∷ Γ) void) → CheckStm Γ Δ Δ
  returnStm s = return (s ∷ [])

  -- Predicting the next shape of the top block.

  Next : (Δ : Block) (s : A.Stm) → Block
  Next Δ (A.sExp e)          = Δ
  Next Δ (A.sDecls t xs)     = case type t of λ where
    (` t') → List.foldl (λ Δ _ → t' ∷ Δ) Δ xs
    void   → Δ
  Next Δ (A.sInit t x e)     = case type t of λ where
    (` t') → t' ∷ Δ
    void   → Δ
  Next Δ (A.sReturn e)       = Δ
  Next Δ (A.sWhile e s)      = Δ
  Next Δ (A.sBlock ss)       = Δ
  Next Δ (A.sIfElse e s s₁)  = Δ

  Nexts : (Δ : Block) (ss : List A.Stm) → Block
  Nexts = List.foldl Next

  mutual

    -- Checking a single statement.
    -- Results in a list of statements due to the desugaring of sDecls.

    checkStm : ∀ {Γ Δ} (s : A.Stm) → CheckStm Γ Δ (Next Δ s)

    checkStm (A.sExp e) = do
      (t , e') ← lift $ inferExp e
      returnStm (sExp e')

    checkStm (A.sReturn e) = do
      e' ← lift $ checkExp e rt
      returnStm (sReturn e')

    checkStm (A.sInit t x e) with type t
    ... | void = throwError voidDeclaration
    ... | ` t' = do
      e' ← lift $ checkExp` e t'
      addVar (idToName x) t'
      return (sInit (just e') ∷ [])

    checkStm (A.sDecls t xs)  with type t
    ... | void = throwError voidDeclaration
    ... | ` t' = checkDecls t' xs

    checkStm (A.sWhile e s) = do
      e' ← lift $ checkExp` e bool
      s' ← newBlock sBlock $ checkStm s
      returnStm (sWhile e' s')

    checkStm (A.sIfElse e s₁ s₂) = do
      e' ← lift $ checkExp` e bool
      s₁' ← newBlock sBlock $ checkStm s₁
      s₂' ← newBlock sBlock $ checkStm s₂
      returnStm (sIfElse e' s₁' s₂')

    checkStm (A.sBlock ss) =
      (_∷ []) <$> newBlock sBlock (checkStms ss)

    -- Checking a list of statements.

    checkStms : ∀ {Γ Δ} (ss : List A.Stm) → CheckStm Γ Δ (Nexts Δ ss)
    checkStms []       = return []
    checkStms (s ∷ ss) = do
      ss' ← checkStm s
      (ss' ++ˢ_) <$> checkStms ss

    -- Adding a list of uninitialized variable bindings.

    checkDecls : ∀ {Γ Δ}
       (t : Ty) (xs : List A.Id) → CheckStm Γ Δ (List.foldl (λ Δ _ → t ∷ Δ) Δ xs)
    checkDecls t []       = return []
    checkDecls t (x ∷ xs) = do
      addVar (idToName x) t
      (sInit nothing ∷_) <$> checkDecls t xs

-- Checking the program.
---------------------------------------------------------------------------

module CheckProgram where

  -- We work in the error monad.

  open ErrorMonad {E = TypeError} hiding (Error; ok; fail)

  -- We store the definitions to check in a todo-list.

  -- A definition we need to work on (check the body).

  record WDef (ft : FunType) : Set where
    constructor wdef
    field
      wPars : TCBlock (FunType.dom ft)  -- named function parameters
      wBody : List (A.Stm)              -- function body: statements we need to check

  -- The list of all definitions to check.

  WDefs : (Σ : Sig) → Set
  WDefs = List.All WDef

  -- This worklist is built by pass 1 (check signature).

  record Worklist : Set where
    constructor worklist
    field
      {Σ} : Sig
      wTcSig : TCSig Σ
      wDefs  : WDefs Σ

  initWorklist : Worklist
  initWorklist = record { wTcSig = emptyTCSig; wDefs = [] }

  -- Helpers for pass 1:

  -- Checking the function parameters.

  -- We need to be careful not to reverse the order of function parameters.
  -- During function calls, we match the arguments left-to-right with
  -- the parameters.

  -- Thus, the first argument needs to remain first in the list
  -- (de Bruijn index 0).  We proceed in foldr manner.

  checkArgs : (args : List A.Arg) → Error (∃ λ Δ → TCBlock Δ)
  checkArgs [] = return ([] , []ⁿ)
  checkArgs (A.aDecl t x ∷ args) = do
    case type t of λ where
      void   → throwError voidDeclaration
      (` t') → do
        -- Handle the args in right-to-left manner
        (Δ , δ) ← checkArgs args
        case t' ↦ idToName x ∷ᵘ? uniq δ of λ where
          (no  _) → throwError duplicateParameter
          (yes u) → return (_ , record { uniq = u })

  addFun : ∀ (x : Name) (ft : FunType) {Σ} (σ : TCSig Σ) → Error (TCSig (ft ∷ Σ))
  addFun x ft σ = do
    case ?↦ x ∈ scope builtinSig of λ where
      (yes _) → throwError shadowingBuiltin
      (no ¬b) → case ft ↦ x ∷ᵘ? uniq (theSig σ) of λ where
         (no  _) → throwError duplicateDefinition
         (yes u) → return $ mkTCSig record{ uniq = u } λ where
           here      b → ¬b (_ , _ , b)
           (there p) b → noClashBuiltin σ p b

  -- Pass 1: check function headers.
  -- The first function in the file will end up last in the signature
  -- (due to the accumulator/foldl like structure).

  checkSignature : ∀ (ds : List A.Def) → Worklist → Error Worklist
  checkSignature [] w = return w
  checkSignature (A.dFun t x args ss ∷ ds) (worklist {Σ} σ wds) = do
    (Δ , δ) ← checkArgs args
    σ' ← addFun (idToName x) (funType Δ (type t)) σ
    checkSignature ds (worklist σ' (wdef δ ss ∷ wds))

  -- Pass 2: check function bodies.

  checkBody : ∀{Σ t} (σ : TCSig Σ) {Δ} (δ : TCBlock Δ) (ss : List A.Stm)
    → Error (Def Σ (funType Δ t))
  checkBody {Σ} {t} σ δ ss = do
    (ss' , _) ← checkStms ss .runTCStm (tcEnv σ []) δ
    return (_ , ss')
    where open CheckStatements {Σ} {t} using (checkStms; runTCStm)

  -- Make sure we start with the innermost definition (last in the list).

  checkDefs : ∀{Σ} (σ : TCSig Σ) {Σ'} (ds : WDefs Σ') → Error (Prg Σ Σ')
  checkDefs σ [] = return []
  checkDefs σ (wdef δ ss ∷ ds) = do
    ds' ← checkDefs σ ds
    (_∷ ds') <$> checkBody σ δ ss

  -- Step 3: check main function for existence and correct type.

  checkMain : ∀{Σ} (σ : TCSig Σ) → Error (Fun Σ mainType)
  checkMain σ = do
    case ?↦ "main" ∈ scope (theSig σ) of λ where
      (yes (mainType , f , _)) → return f
      (yes (funType [] _ , _)) → throwError mainNoReturnInt
      (yes _)                  → throwError mainHasParameters
      (no  _)                  → throwError noMain

  -- Entry point.  Performs the 3 steps.

  checkProgram : (prg : A.Program) → Error (∃ λ Σ → Program Σ)
  checkProgram (A.pDefs ds) = do
    worklist {Σ} σ ds' ← checkSignature ds initWorklist
    prg  ← checkDefs {Σ} σ {Σ} ds'
    main ← checkMain σ
    return (Σ , program prg main)

-- -}
-- -}
-- -}
-- -}
-- -}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module TypeChecker where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Functor
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NEList

import CPP.Abs
import CPP.Print
import CPP.ErrM

type NEList = NEList.NonEmpty

-- | The signature maps function identifiers to the list of their parameters and the return type.
type Sig     = Map Id FunType
data FunType = FunType { funRet :: Type, funPars :: [Type] }

-- | The state consists of the local context and the return type of the function.
data St = St
  { stCxt :: Cxt   -- ^ Variable bindings.
  , stRet :: Type  -- ^ Return type.
  }

-- | The local context is a stack of typing environments.
type Cxt   = NEList Block
type Block = Map Id Type

-- | Type errors are just strings.
type TypeError = String

-- | The type checking monad
type Check = ReaderT Sig (StateT St (Except TypeError))

-- | Builtin-functions
builtin :: [(Id, FunType)]
builtin =
  [ (Id "readInt"    , FunType Type_int    [])
  , (Id "readDouble" , FunType Type_double [])
  , (Id "printInt"   , FunType Type_void [Type_int])
  , (Id "printDouble", FunType Type_void [Type_double])
  ]
-- | Entry point of type checker.
typecheck :: Program -> Err ()
typecheck prg@(PDefs defs) = do
  -- Prepare signature.
  let sig = builtin ++ map mkF defs
      mkF (DFun t f args ss) = (f, FunType t $ map (\ (ADecl t _) -> t) args)
  -- Check for duplicate function definitions.
  case firstDuplicate $ map fst sig of
    Nothing -> return ()
    Just f  -> Bad $ "function " ++ printTree f ++ " is defined twice"
  -- Prepare the initial state.
  let st = error "no state yet"
  -- Run the type checker.
  case runExcept (evalStateT (runReaderT (checkProgram prg) (Map.fromList sig)) st) of
    Left s   -> Bad s
    Right () -> return ()

checkProgram :: Program -> Check ()
checkProgram (PDefs defs) = do
  mapM_ checkDef defs
  checkMain

checkMain :: Check ()
checkMain = (Map.lookup (Id "main") <$> ask) >>= \case
  Nothing -> throwError "main function missing"
  Just (FunType t pars) -> do
    unless (t == Type_int) $ throwError "main function should return an int"
    unless (null pars) $ throwError "main function takes no parameters"

checkDef :: Def -> Check ()
checkDef (DFun t f args ss) = do
  -- Set initial context and return type.
  put $ St (Map.empty :| []) t
  -- Add function parameters to the context.
  mapM_ (\ (ADecl t x) -> newVar x t) args
  -- Check function body.
  mapM_ checkStm ss

checkStm :: Stm -> Check ()
checkStm = \case
    SExp e         -> () <$ inferExp e
    SDecls t xs    -> mapM_ (`newVar` t) xs
    SInit t x e    -> do
      checkExp e t
      newVar x t
    SReturn e      -> checkExp e =<< gets stRet
    SWhile e s     -> do
      checkExp e Type_bool
      inNewBlock $ checkStm s
    SBlock ss      -> inNewBlock $ mapM_ checkStm ss
    SIfElse e s s' -> do
      checkExp e Type_bool
      inNewBlock $ checkStm s
      inNewBlock $ checkStm s'

inferExp :: Exp -> Check Type
inferExp = \case
    ETrue     -> return Type_bool
    EFalse    -> return Type_bool
    EInt _    -> return Type_int
    EDouble _ -> return Type_double
    EId x     -> lookupVar x
    EApp f es -> (Map.lookup f <$> ask) >>= \case
      Nothing -> throwError $ "unbound function " ++ printTree f
      Just (FunType t args) -> do
        checkExps es args
        return t
    EPostIncr x  -> numericType =<< lookupVar x
    EPostDecr x  -> numericType =<< lookupVar x
    EPreIncr  x  -> numericType =<< lookupVar x
    EPreDecr  x  -> numericType =<< lookupVar x
    ETimes e1 e2 -> inferArith e1 e2
    EDiv   e1 e2 -> inferArith e1 e2
    EPlus  e1 e2 -> inferArith e1 e2
    EMinus e1 e2 -> inferArith e1 e2
    ELt    e1 e2 -> inferComp True  e1 e2
    EGt    e1 e2 -> inferComp True  e1 e2
    ELtEq  e1 e2 -> inferComp True  e1 e2
    EGtEq  e1 e2 -> inferComp True  e1 e2
    EEq    e1 e2 -> inferComp False e1 e2
    ENEq   e1 e2 -> inferComp False e1 e2
    EAnd   e1 e2 -> inferLogic e1 e2
    EOr    e1 e2 -> inferLogic e1 e2
    EAss   x  e  -> do
      t <- lookupVar x
      checkExp e t
      return t

checkExp :: Exp -> Type -> Check ()
checkExp e t = do
  t' <- inferExp e
  unless (t == t') $ throwError $
    "expected type " ++ printTree t ++ ", but inferred type " ++ printTree t'

-- | Check function arguments against their expected types.
checkExps :: [Exp] -> [Type] -> Check ()
checkExps []     []     = return ()
checkExps (e:es) (t:ts) = checkExp e t >> checkExps es ts
checkExps []     _      = throwError $ "too few function arguments"
checkExps _      []     = throwError $ "too many function arguments"

-- | Infer type of arithmetical operation.
inferArith :: Exp -> Exp -> Check Type
inferArith e e' = do
  t <- numericType =<< inferExp e
  checkExp e' t
  return t

-- | Infer type of comparison operation.
inferComp :: Bool -> Exp -> Exp -> Check Type
inferComp ineq e e' = do
  t <- notVoid =<< inferExp e
  checkExp e' t
  when (t == Type_bool && ineq) $ throwError $ "illegal boolean comparison"
  return Type_bool

-- | Infer type of logical operation.
inferLogic :: Exp -> Exp -> Check Type
inferLogic e e' = do
  checkExp e  Type_bool
  checkExp e' Type_bool
  return Type_bool

-- * Variable handling

-- | Return the first duplicate in a list, if any.
firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = loop Set.empty where
  loop s [] = Nothing
  loop s (a:as) = if Set.member a s then Just a else loop (Set.insert a s) as

-- | Update the typing context.
modifyCxt :: (Cxt -> Cxt) -> Check ()
modifyCxt f = modify $ \ (St bs t) -> St (f bs) t

-- | Add a new binding and make sure it is unique in the top context block.
newVar :: Id -> Type -> Check ()
newVar x t = do
  when (t == Type_void) $
    throwError $ "type void of variable " ++ printTree x ++ " is illegal"
  (b :| bs) <- gets stCxt
  let (found, b') = Map.insertLookupWithKey (\ _ t _ -> t) x t b
  unless (isNothing found) $ throwError $ "duplicate variable binding " ++ printTree x
  modifyCxt $ const (b' :| bs)

-- | Add a new block and pop it afterwards
inNewBlock :: Check a -> Check a
inNewBlock cont = do
  modifyCxt $ NEList.cons Map.empty
  r <- cont
  modifyCxt $ NEList.fromList . NEList.tail
  return r

-- | Lookup the type of a variable in the context.
lookupVar :: Id -> Check Type
lookupVar x = loop . NEList.toList =<< gets stCxt
  where
  loop []     = throwError $ "unbound variable " ++ printTree x
  loop (b:bs) = case Map.lookup x b of
    Just t  -> return t
    Nothing -> loop bs

-- | Check that the given expression is a variable.
isVar :: Exp -> Check Id
isVar (EId x) = return x
isVar e = throwError $ "expected variable, but found " ++ printTree e

-- | Check that the given type is numeric.
numericType :: Type -> Check Type
numericType t = case t of
  Type_int    -> return t
  Type_double -> return t
  _ -> throwError $ "expected numeric expression, but found something of type " ++ printTree t

-- | Check that the given type is not void.
notVoid :: Type -> Check Type
notVoid Type_void = throwError $ "unexpected void expression"
notVoid t = return t

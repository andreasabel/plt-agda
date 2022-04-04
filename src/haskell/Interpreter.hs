{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Interpreter where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State

import Data.Functor
import Data.Foldable (foldMap)
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid

import CPP.Abs
import CPP.Print

-- | The monad for the interpreter.
type Eval = ReaderT Sig (StateT Env IO)

-- | Function signature maps function identifiers to argument lists and statement list.
type Sig = Map Id FunDef
data FunDef = FunDef { funParams :: [Id], funBody :: [Stm] }

-- | Environment is a stack of blocks, mapping variable identifiers to values.
type Env = [Block]
type Block = Map Id Val

data Val
  = VBool   Bool
  | VInt    Integer
  | VDouble Double
  | VVoid           -- ^ Also used for uninitialized variable.

-- | Entry point

interpret :: Program -> IO ()
interpret (PDefs defs) = do
  -- Prepare the signature.
  let sig = Map.fromList $ map (\ (DFun _ f args ss) -> (f, FunDef (map (\ (ADecl _ x) -> x) args) ss)) defs
  -- Find the entry point ("main" function)
  let ss = maybe (error "no main") funBody $ Map.lookup (Id "main") sig
  -- The initial environment has one empty block
  let env = [Map.empty]
  -- Run the statements in the initial environment
  () <$ evalStateT (runReaderT (evalStms ss) sig) env

-- | Statements evaluate to a result, which is either the return value of the function
--   or "continue".
data Res
  = Ret Val
  | Cont

-- | Execute from left to right until a 'Ret' is returned.
instance Semigroup (Eval Res) where
  (<>) = semicolon

instance Monoid (Eval Res) where
  mempty  = return Cont
  mappend = (<>)

-- | Run the second computation unless the first returns 'Ret'.
semicolon :: Eval Res -> Eval Res -> Eval Res
semicolon m m' = m >>= \case
  Ret v -> return $ Ret v
  Cont  -> m'

-- | Execute from left to right until a 'Ret' is returned.
evalStms :: [Stm] -> Eval Res
evalStms = foldMap evalStm

evalStm :: Stm -> Eval Res
evalStm s0 = case s0 of
    SExp e      -> Cont <$ evalExp e
    SDecls _ xs -> Cont <$ do forM_ xs $ \ x -> newVar x VVoid
    SInit _ x e -> Cont <$ do newVar x =<< evalExp e
    SReturn e   -> Ret <$> evalExp e
    SWhile e s  -> ifExp e
      {-then-} (inNewBlock (evalStm s) `semicolon` evalStm s0)
      {-else-} (return Cont)
    SBlock ss   -> inNewBlock $ evalStms ss
    SIfElse e s s' -> ifExp e
      {-then-} (inNewBlock $ evalStm s)
      {-else-} (inNewBlock $ evalStm s')

-- | If the expression evaluates to 'VBool True', run the first computation,
--   if to 'VBool False', run the second computation.

ifExp :: Exp -> Eval a -> Eval a -> Eval a
ifExp e m m' = evalExp' e >>= \case
  VBool True  -> m
  VBool False -> m'

evalExp :: Exp -> Eval Val
evalExp = \case
    ETrue     -> return $ VBool True
    EFalse    -> return $ VBool False
    EInt i    -> return $ VInt i
    EDouble d -> return $ VDouble d
    EId x     -> lookupEnv' x
    EApp f es0 -> handlePrimitive f es $ do
      vs <- mapM evalExp es
      FunDef xs ss <- fromMaybe (error $ "unbound function" ++ printTree f) . Map.lookup f <$> ask
      guard $ length xs == length vs
      inNewBlock $ do
        zipWithM_ newVar xs vs
        fromRet <$> evalStms ss
      where
      es = expsToList es0
      fromRet (Ret v) = v
      fromRet Cont    = VVoid
    EPostIncr x -> do
      v <- lookupEnv' x
      assignVar x $ successor v
      return v
    EPostDecr x -> do
      v <- lookupEnv' x
      assignVar x $ predecessor v
      return v
    EPreIncr x -> do
      v <- successor <$> lookupEnv' x
      assignVar x v
      return v
    EPreDecr x -> do
      v <- predecessor <$> lookupEnv' x
      assignVar x v
      return v
    ETimes e e' -> arith (*) <$> evalExp' e <*> evalExp' e'
    EPlus  e e' -> arith (+) <$> evalExp' e <*> evalExp' e'
    EMinus e e' -> arith (-) <$> evalExp' e <*> evalExp' e'
    EDiv   e e' -> divide    <$> evalExp' e <*> evalExp' e'
    ELt    e e' -> comp  (<) <$> evalExp' e <*> evalExp' e'
    EGt    e e' -> comp  (>) <$> evalExp' e <*> evalExp' e'
    ELtEq  e e' -> comp (<=) <$> evalExp' e <*> evalExp' e'
    EGtEq  e e' -> comp (>=) <$> evalExp' e <*> evalExp' e'
    EEq    e e' -> comp (==) <$> evalExp' e <*> evalExp' e'
    ENEq   e e' -> comp (/=) <$> evalExp' e <*> evalExp' e'
    EAnd   e e' -> ifExp e (evalExp e') (return $ VBool False)
    EOr    e e' -> ifExp e (return $ VBool True) (evalExp e')
    EAss x e -> do
      v <- evalExp e
      assignVar x v
      return v

-- | Raises an error if value is 'VVoid', else returns the value.
ensureDefined :: Val -> Eval Val
ensureDefined = \case
  VVoid -> error $ "uninitialized variable"
  v     -> return v

lookupEnv' :: Id -> Eval Val
lookupEnv' x = ensureDefined =<< lookupEnv x

evalExp' :: Exp -> Eval Val
evalExp' e = ensureDefined =<< evalExp e

-- * Variable handling

-- | Insert binding into top environment block.

newVar :: Id -> Val -> Eval ()
newVar x v = modify $ \case
  b:bs -> Map.insert x v b : bs

-- | Push an empty block and pop it after computation.

inNewBlock :: Eval a -> Eval a
inNewBlock cont = do
  modify $ (Map.empty :)
  a <- cont
  modify $ tail
  return a

-- | Look up variable in environment.

lookupEnv :: Id -> Eval Val
lookupEnv x = lookupBlock x <$> get

-- | Return the first binding for a variable in the stack of blocks.

lookupBlock :: Id -> [Block] -> Val
lookupBlock x [] = error $ "unbound: " ++ printTree x
lookupBlock x (b:bs)
  | Just v <- Map.lookup x b = v
  | otherwise                = lookupBlock x bs

-- | Update value of existing variable.

assignVar :: Id -> Val -> Eval ()
assignVar x v = modify $ updateBlocks x v

-- | Update the first binding for a variable in the stack of blocks.

updateBlocks :: Id -> Val -> Env -> Env
updateBlocks x v []     = error $ "unbound: " ++ printTree x
updateBlocks x v (b:bs) = case found of
   Nothing -> b  : updateBlocks x v bs
   Just{}  -> b' : bs
  where
  (found, b') = Map.updateLookupWithKey (\ _ _ -> Just v) x b

-- * Operations

successor :: Val -> Val
successor (VInt    i) = VInt    $ i + 1
successor (VDouble d) = VDouble $ d + 1.0

predecessor :: Val -> Val
predecessor (VInt    i) = VInt    $ i - 1
predecessor (VDouble d) = VDouble $ d - 1.0

arith :: (forall a. Num a => a -> a -> a) -> Val -> Val -> Val
arith op (VInt i)    (VInt i')    = VInt    $ op i i'
arith op (VDouble d) (VDouble d') = VDouble $ op d d'

divide :: Val -> Val -> Val
divide (VInt i)    (VInt i')    = VInt    $ i `div` i'
divide (VDouble d) (VDouble d') = VDouble $ d / d'

comp :: (forall a. Ord a => a -> a -> Bool) -> Val -> Val -> Val
comp op (VInt    i) (VInt    i') = VBool $ op i i'
comp op (VDouble d) (VDouble d') = VBool $ op d d'
comp op (VBool   b) (VBool   b') = VBool $ op b b'

-- * Primitive functions

handlePrimitive :: Id -> [Exp] -> Eval Val -> Eval Val
handlePrimitive (Id f) es fallback =
  case f of
    "readInt"    -> VInt . read <$> liftIO getLine
    "readDouble" -> VDouble . read <$> liftIO getLine
    "printInt"   -> do
      VInt i <- evalExp $ head es
      liftIO $ putStrLn $ show i
      return VVoid
    "printDouble"-> do
      VDouble d <- evalExp $ head es
      liftIO $ putStrLn $ show d
      return VVoid
    _ -> fallback

-- * AST utils

-- Convert Snoc-list to cons list

expsToList :: Exps -> [Exp]
expsToList = loop []
  where
  loop acc ENil         = acc
  loop acc (ESnoc es e) = loop (e : acc) es

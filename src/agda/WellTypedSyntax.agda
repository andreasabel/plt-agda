-- Intrinsically well-typed C-- syntax.

-- Variables are represented by de Bruijn indices into the context,
-- which is structured as a list of blocks.
-- We do not need weakening.

-- Functions are represented by de Bruijn indices into the signature.

module WellTypedSyntax where

open import Library
open import Value public

-- Typing contexts are lists of blocks.
-- There is at least one block, which can be empty.
-- A block is a list of types.

Block = List Ty
Cxt⁻ = List Block
Cxt = List⁺ Block

-- Variables are pairs of pointers.
-- The first picks a block, the second an entry in this block.

record Var⁻ (Γ : Cxt⁻) (t : Ty) :  Set where
  no-eta-equality
  constructor var
  field
    {Δ} : Block
    Δ∈Γ : Δ ∈ Γ
    t∈Δ : t ∈ Δ

Var : (Γ : Cxt) (t : Ty) → Set
Var Γ t = Var⁻ (List⁺.toList Γ) t

-- Block extension

_▷ᵇ_ : Block → Type → Block
Δ ▷ᵇ void = Δ
Δ ▷ᵇ ` t  = t ∷ Δ

-- Context extensions.

_▷_ : Cxt → Type → Cxt
(Δ ∷ Γ) ▷ t  = (Δ ▷ᵇ t) ∷ Γ

_▷ᵈ_ : Cxt → Block → Cxt
(Δ ∷ Γ) ▷ᵈ Δ'  = (Δ' ++ Δ) ∷ Γ

vzero : ∀{Γ Δ t} → Var ((t ∷ Δ) ∷ Γ) t
vzero = var (here refl) (here refl)

-- Rank-1 function types

record FunType : Set where
  constructor funType
  field
    dom   : Block
    coDom : Type
open FunType public

-- Unfortunately, the standard library does not have a proper finite map type.
-- There is Data.AVL, but it does not provide properties like membership.
-- Thus, we just use an association list for the signature.

Sig = List FunType

-- A function is an index into the signature.

Fun : (Σ : Sig) (ft : FunType) → Set
Fun Σ ft = ft ∈ Σ

-- Builtin functions

data Builtin : FunType → Set where
  bReadInt     : Builtin (funType [] (` int))
  bReadDouble  : Builtin (funType [] (` double))
  bPrintInt    : Builtin (funType (int    ∷ []) void)
  bPrintDouble : Builtin (funType (double ∷ []) void)

-- Types that support arithmetic operations

data ArithType : Ty → Set where
  int    : ArithType int
  double : ArithType double

-- Arithmetical operators

data ArithOp (t : Ty) : Set where
  plus minus times div : (a : ArithType t) → ArithOp t

-- Comparison operators

data CmpOp (t : Ty) : Set where
  lt gt ltEq gtEq : (a : ArithType t) → CmpOp t
  eq nEq : CmpOp t

-- Logical operators

data LogicOp : Set where
  and or : LogicOp

-- Binary Operators

data Op : (t t' : Ty) → Set where
  arith : ∀{t} (op : ArithOp t) → Op t t
  cmp   : ∀{t} (op : CmpOp t) → Op t bool
  logic : (op : LogicOp) → Op bool bool

-- For compact representation of increment/decrement operators:

data IncrDecr (t : Ty) : Set where
  incr decr : (a : ArithType t) → IncrDecr t

-- Prefix or postfix?

data PrePost : Set where
  pre post : PrePost

ifPost_then_else_ : PrePost → ∀{a} {A : Set a} → A → A → A
ifPost post then x else y = x
ifPost pre  then x else y = y

-- The signature is fixed in both expressions and statements.

-- Well-typed expressions: context is fixed.

module _ (Σ : Sig) (Γ : Cxt) where
  mutual
    data Exp : Type → Set
    Exp` = λ t → Exp (` t)
    Exps = List.All Exp`

    data Exp where
      eConst     : ∀{t}    (v : Val` t)                                 → Exp` t
      eVar       : ∀{t}    (x : Var Γ t)                                → Exp` t
      eApp       : ∀{t ts} (f : Fun Σ (funType ts t)) (es : Exps ts)    → Exp t
      eBuiltin   : ∀{t ts} (f : Builtin (funType ts t)) (es : Exps ts)  → Exp t
      eIncrDecr  : ∀{t}    (p : PrePost) (k : IncrDecr t) (x : Var Γ t) → Exp` t
      eOp        : ∀{t t'} (op : Op t t') (e e' : Exp` t)               → Exp` t'
      eAss       : ∀{t}    (x : Var Γ t) (e : Exp` t)                   → Exp` t

-- Well-typed statements (might extend the context)

module _ (Σ : Sig) (returnType : Type) where
  mutual
    data Stm (Γ : Cxt) : Type → Set where
      sReturn : (e : Exp Σ Γ returnType)                   → Stm Γ void
      sExp    : ∀{t} (e : Exp Σ Γ t)                       → Stm Γ void
      sInit   : ∀{t} (e : Maybe (Exp` Σ Γ t))              → Stm Γ (` t)
      -- sDecls has been desugared into sInits.
      sBlock  : ∀{Δ} (ss : Stms (List⁺.toList Γ) [] Δ)     → Stm Γ void
      -- The bodies of sWhile and sIfElse do not permit scope extensions here.
      -- The type checker will possibly insert sBlock constructors to ensure
      -- no scope extension happens.
      sWhile  : (e : Exp` Σ Γ bool) (s : Stm Γ void)    → Stm Γ void
      sIfElse : (e : Exp` Σ Γ bool) (s s' : Stm Γ void) → Stm Γ void

    -- We expose the top block Δ, which can be extended by statements.

    data Stms (Γ : List Block) (Δ : Block) : Block → Set where
      []  : Stms Γ Δ Δ
      _∷_ : ∀{t} (s : Stm (Δ ∷ Γ) t) {Δ′} (ss : Stms Γ (Δ ▷ᵇ t) Δ′) → Stms Γ Δ Δ′

-- Stms can be concatenated.

_++ˢ_ : ∀{Σ t Γ Δ Δ' Δ''} → Stms Σ t Γ Δ Δ' → Stms Σ t Γ Δ' Δ'' → Stms Σ t Γ Δ Δ''
[]       ++ˢ ss' = ss'
(s ∷ ss) ++ˢ ss' = s ∷ (ss ++ˢ ss')

-- Well-typed definitions are lists of well-typed statements
-- with the correct return type in the initial environment
-- given by the function parameters.

Def : (Σ : Sig) (ft : FunType) → Set
Def Σ (funType Δ t) = ∃ λ Δ′ → Stms Σ t [] Δ Δ′

-- Well-typed programs.

Prg : (Σ Σ' : Sig) → Set
Prg Σ = List.All (Def Σ)

-- A program has an entry point: int main().

pattern mainType = funType [] (` int)

record Program' (Prg : (Σ Σ' : Sig) → Set) (Σ : Sig) : Set where
  constructor program
  field
    thePrg  : Prg Σ Σ
    theMain : Fun Σ mainType
open Program' public

Program : (Σ : Sig) → Set
Program = Program' Prg

-- Testing types

arithType? : ∀ t → Dec (ArithType t)
arithType? int    = yes int
arithType? double = yes double
arithType? bool   = no λ()

module TyEq where

  _≟_ : (t t' : Ty) → Dec (t ≡ t')
  bool   ≟ bool   = yes refl
  bool   ≟ int    = no λ()
  bool   ≟ double = no λ()
  int    ≟ bool   = no λ()
  int    ≟ int    = yes refl
  int    ≟ double = no λ()
  double ≟ bool   = no λ()
  double ≟ int    = no λ()
  double ≟ double = yes refl

module TypeEq where

  `-injective : ∀ {t t'} → ` t ≡ ` t' → t ≡ t'
  `-injective refl = refl

  _≟_ : (t t' : Type) → Dec (t ≡ t')
  void   ≟ void   = yes refl
  ` _    ≟ void   = no λ()
  void   ≟ ` _    = no λ()
  ` t    ≟ ` t'   with t TyEq.≟ t'
  ... | yes refl  = yes refl
  ... | no ¬eq    = no (¬eq ∘ `-injective)


-- Builtins

Builtins = List (∃ Builtin)

builtins : Builtins
builtins =
  (_ , bReadInt    ) ∷
  (_ , bReadDouble ) ∷
  (_ , bPrintInt   ) ∷
  (_ , bPrintDouble) ∷
  []

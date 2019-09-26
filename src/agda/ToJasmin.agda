module ToJasmin where

open import Library; open String renaming (_++_ to _<>_); open List using ([_])
open import Library.AllExt

open import Value
open import WellTypedSyntax
open import FlowChart
open import BasicBlocks

-- cat2 : String → String → String
-- cat2 = String._++_

parens : String → String
parens s = "(" <> s <> ")"

sep2By : String → String → String → String
sep2By sep s s' = s <> sep <> s'

infixl 6 _<+>_ _<t>_ _<u>_

_<+>_ : String → String → String
_<+>_ = sep2By " "

_<t>_ : String → String → String
_<t>_ = sep2By "\t"

_<u>_ : String → String → String
_<u>_ = sep2By "_"

_</>_ : String → String → String
_</>_ = sep2By "/"

vsep : List (List String) → List String
vsep = List.foldr (λ xs ys → xs ++ "" ∷ ys) []

isByte : ℤ → Bool
isByte i = (i <= + 127) Bool.∧ (-[1+ 127 ] <= i)
  where open Integer

-- Printing monad

iconstToJVM : ℤ → String
iconstToJVM (+_ 0) = "iconst_0"
iconstToJVM (+_ 1) = "iconst_1"
iconstToJVM (+_ 2) = "iconst_2"
iconstToJVM (+_ 3) = "iconst_3"
iconstToJVM (+_ 4) = "iconst_4"
iconstToJVM (+_ 5) = "iconst_5"
iconstToJVM (-[1+ 0 ]) = "iconst_m1"
iconstToJVM i = (if isByte i then "bipush" else "ldc") <t> printInt i

constToJVM : ∀ t → Val` t → String
constToJVM int        = iconstToJVM
constToJVM double v   = "ldc2_w" <t> printDouble v
constToJVM bool false = "iconst_0"
constToJVM bool true  = "iconst_1"

dupToJVM : Ty → String
dupToJVM double = "dup2"
dupToJVM int    = "dup"
dupToJVM bool   = "dup"

popToJVM : Type → Maybe String
popToJVM void       = nothing
popToJVM (` double) = just "pop2"
popToJVM (` int)    = just "pop"
popToJVM (` bool)   = just "pop"

tyPrefix : Ty → String
tyPrefix double = "d"
tyPrefix int    = "i"
tyPrefix bool   = "i"

typePrefix : Type → String → String
typePrefix (` t) = tyPrefix t <>_
typePrefix void  = id

arithToJVM : ∀ t → ArithOp t → String
arithToJVM int    (plus  _) = "iadd"
arithToJVM int    (minus _) = "isub"
arithToJVM int    (times _) = "imul"
arithToJVM int    (div   _) = "idiv"
arithToJVM double (plus  _) = "dadd"
arithToJVM double (minus _) = "dsub"
arithToJVM double (times _) = "dmul"
arithToJVM double (div   _) = "ddiv"

stackIToJVM : ∀{Φ Φ'} → StackI Φ Φ' → Maybe String
stackIToJVM (const v)     = just $ constToJVM _ v
stackIToJVM (dup {t = t}) = just $ dupToJVM t
stackIToJVM (pop {t = t}) = popToJVM t
stackIToJVM (arith op)    = just $ arithToJVM _ op

remainingCxt : ∀{a} {A : Set a} {x : A} {xs : List A} → x ∈ xs → List A
remainingCxt (here {xs = xs} _) = xs
remainingCxt (there i)          = remainingCxt i

tyMemSize : Ty → ℕ
tyMemSize double = 2
tyMemSize int    = 1
tyMemSize bool   = 1

blockMemSize : Block → ℕ
blockMemSize = List.sum ∘ List.map tyMemSize

offsetAddr : ∀ {t} {Δ : Block} → t ∈ Δ → ℕ
offsetAddr = blockMemSize ∘ remainingCxt

cxtMemSize : List Block → ℕ
cxtMemSize = List.sum ∘ List.map blockMemSize

blockAddr : ∀ {Γ} {Δ : Block} → Δ ∈ List⁺.toList Γ → ℕ
blockAddr = cxtMemSize ∘ remainingCxt

varToAddr : ∀{Γ t} → Var Γ t → ℕ
varToAddr (var Δ∈Γ t∈Δ) = blockAddr Δ∈Γ + offsetAddr t∈Δ

accessToJVM : String → ℕ → String
accessToJVM s 0 = s <u> "0"
accessToJVM s 1 = s <u> "1"
accessToJVM s 2 = s <u> "2"
accessToJVM s 3 = s <u> "3"
accessToJVM s n = s <t> printNat n

incDecToJVM : IncDec → String
incDecToJVM inc = "1"
incDecToJVM dec = "-1"

storeIToJVM : ∀{Γ Φ Φ'} → StoreI Γ Φ Φ' → String
storeIToJVM (store {t = t} x) = tyPrefix t <> accessToJVM "store" (varToAddr x)
storeIToJVM (load {t = t}  x) = tyPrefix t <> accessToJVM "load" (varToAddr x)
storeIToJVM (incDec b x) = "iinc" <t> printNat (varToAddr x) <+> incDecToJVM b

tyToJVM : Ty → String
tyToJVM int    = "I"
tyToJVM double = "D"
tyToJVM bool   = "Z"

typeToJVM : Type → String
typeToJVM (` t) = tyToJVM t
typeToJVM void = "V"

typesToJVM : Block → String
typesToJVM = String.concat ∘ List.map tyToJVM

funTypeToJVM : FunType → String
funTypeToJVM (funType Δ t) = parens (typesToJVM Δ) <> typeToJVM t

builtinToJVM' : ∀{t} → Builtin t → String
builtinToJVM' bReadInt     = "readInt"
builtinToJVM' bReadDouble  = "readDouble"
builtinToJVM' bPrintInt    = "printInt"
builtinToJVM' bPrintDouble = "printDouble"

builtinToJVM : ∀ t → Builtin t → String
builtinToJVM ft b = builtinToJVM' b <> funTypeToJVM ft

cmpOpToJVM : ∀{t} → CmpOp t → String
cmpOpToJVM (lt _)   = "lt"
cmpOpToJVM (gt -)   = "gt"
cmpOpToJVM (ltEq _) = "le"
cmpOpToJVM (gtEq _) = "ge"
cmpOpToJVM eq       = "eq"
cmpOpToJVM nEq      = "ne"

icmpToJVM : String → CmpOp int → String
icmpToJVM l op = "if_icmp" <> cmpOpToJVM op <t> l

dcmpToJVM : String → ∀{t} → CmpOp t → List String
dcmpToJVM l (lt   a) = "iconst_m1" ∷ icmpToJVM l eq  ∷ []  -- check for -1
dcmpToJVM l (gtEq a) = "iconst_m1" ∷ icmpToJVM l nEq ∷ []  -- check not -1
dcmpToJVM l (gt   a) = "iconst_1"  ∷ icmpToJVM l eq  ∷ []  -- check for 1
dcmpToJVM l (ltEq a) = "iconst_1"  ∷ icmpToJVM l nEq ∷ []  -- check not 1
dcmpToJVM l eq       = [ "ifeq" <t> l ]                    -- check for 0
dcmpToJVM l nEq      = [ "ifne" <t> l ]                    -- check not 0

cmpToJVM : String → ∀ t → CmpOp t → List String
cmpToJVM l int   op  = [ icmpToJVM l op  ]
cmpToJVM l bool  eq  = [ icmpToJVM l eq  ]
cmpToJVM l bool  nEq = [ icmpToJVM l nEq ]
cmpToJVM l double op = "dcmpg" ∷ dcmpToJVM l op  -- dcmpg returns sign of subtraction (one of -1,0,1)

condToJVM : String → ∀ {Φ Φ'} → Cond Φ Φ' → List String
condToJVM l (eqBool false) = [ "ifeq" <t> l ]
condToJVM l (eqBool true ) = [ "ifne" <t> l ]
condToJVM l (eqZero true ) = [ "ifeq" <t> l ]
condToJVM l (eqZero false) = [ "ifne" <t> l ]
condToJVM l (cmp op) = cmpToJVM l _ op

record BBToJVM : Set where
  constructor _∙_∙_
  field
    maxStore : ℕ
    maxStack : ℕ
    code     : List String

emit : (Ξ : MT) → List String → BBToJVM
emit (Γ , Φ) ss = cxtMemSize (List⁺.toList Γ) ∙ blockMemSize Φ ∙ List.map ("\t" <>_) ss

_◇_ : (c c' : BBToJVM) → BBToJVM
(maxStore₁ ∙ maxStack₁ ∙ code₁) ◇ (maxStore₂ ∙ maxStack₂ ∙ code₂)
  = (maxStore₁ ℕ.⊔ maxStore₂)
  ∙ (maxStack₁ ℕ.⊔ maxStack₂)
  ∙ (code₁ ++ code₂)


module MethodsToJVM {Σ : Sig} (funNames : AssocList String Σ) where

  funToJVM : ∀ {ft : FunType} → ft ∈ Σ → String
  funToJVM = List.All.lookup funNames

  jfToJVM : ∀ {Ξ Ξ'} → JF Σ Ξ Ξ' → List String
  jfToJVM (stackI j)   = List.fromMaybe $ stackIToJVM j
  jfToJVM (storeI j)   = [ storeIToJVM j ]
  jfToJVM (scopeI adm) = []
  jfToJVM (call f)     = [ "invokestatic" <t> funToJVM f ]
  jfToJVM (builtin b)  = [ "invokestatic" <t> "Runtime/" <> builtinToJVM _ b ]

  module MethodToJVM (rt : Type) {Λ : Labels} (labelNames : AssocList String Λ) where

    labelToJVM : ∀{Ξ} (l : Ξ ∈ Λ) → String
    labelToJVM = List.All.lookup labelNames

    bbToJVM : ∀ Ξ (bb : BB Σ rt Λ Ξ) → BBToJVM
    bbToJVM Ξ (bbExec j bb) = emit Ξ (jfToJVM j) ◇ bbToJVM _ bb
    bbToJVM Ξ (bbGoto l)    = emit Ξ [ "goto" <t> labelToJVM l ]
    bbToJVM Ξ bbReturn      = emit Ξ [ typePrefix rt "return" ]
    bbToJVM Ξ (bbIf c l bb) = emit Ξ (condToJVM (labelToJVM l) c) ◇ bbToJVM _ bb
    bbToJVM Ξ (bbIfElse c bb bb₁) = impossible where postulate impossible : _


    -- -- bbsToJVM : ∀{Λ′} → List.All (BB Σ rt Λ) Λ′ → BBToJVM
    -- bbsToJVM : ∀{Λ′} {τ : [] ⊆ Λ′} → AllExt (BB Σ rt Λ) τ → BBToJVM
    -- bbsToJVM [] = 0 ∙ 0 ∙ []
    -- bbsToJVM (bb ∷ bbs) = bbToJVM _ bb ◇ bbsToJVM bbs

  -- crToJVM : ∀ rt {Ξ} → CompRes Σ rt Ξ [] → BBToJVM
  -- crToJVM rt (_ ∙ bbs ∙ bb) = bbToJVM _ (gotoToBB Σ rt bb ⊆-refl) ◇ bbsToJVM (bbs ⊆-refl)
  --   where
  --   labelNames : AssocList String _
  --   labelNames = List.All.tabulate {!!}
  --   open MethodToJVM rt labelNames

  methToJVM : ∀ rt {Δ} → Meth Σ (funType Δ rt) → BBToJVM
  methToJVM rt (bbMethod Λ entry blocks) = bbToJVM _ entry ◇ blocksToJVM
    where

    labelNames : AssocList String Λ
    labelNames = List.All.tabulate (("L" <>_) ∘ printNat ∘ List.Any.toℕ)

    open MethodToJVM rt labelNames

    blockToJVM : ∀{Ξ} → String × BB Σ rt Λ Ξ → BBToJVM
    blockToJVM (l , bb) = record out { code = (l <> ":") ∷ BBToJVM.code out }
      where out = bbToJVM _ bb

    blocksToJVM : BBToJVM
    blocksToJVM = List.foldr _◇_ (0 ∙ 0 ∙ []) $ List.All.reduce blockToJVM $ List.All.zip (labelNames , blocks)

  methodToJVM : ∀{ft} → String × Meth Σ ft → List String
  methodToJVM (name , meth) with methToJVM _ meth
  ... | storeLimit ∙ stackLimit ∙ code = vsep $ prologue ∷ code ∷ epilogue ∷ []
    where
    prologue
      = ".method public static" <+> name
      ∷ ".limit locals" <+> printNat storeLimit
      ∷ ".limit stack"  <+> printNat stackLimit
      ∷ []
    epilogue = ".end method" ∷ []

FunNames : Sig → Set
FunNames = AssocList String

methodsToJVM : String → ∀ {Σ} → FunNames Σ → Meths Σ Σ → List String
methodsToJVM className funNames meths = vsep $ List.All.reduce methodToJVM $ List.All.zip (methodNames , meths)
  where
  methodNames : AssocList String _
  methodNames = List.All.map (λ {ft} x → x <> funTypeToJVM ft) funNames
  qualMethodNames : AssocList String _
  qualMethodNames = List.All.map (className </>_) methodNames
  open MethodsToJVM qualMethodNames

programToJVM : String → ∀ {Σ} → FunNames Σ → Class Σ → List String
programToJVM className funNames (program meths _) = vsep $ header ∷ init ∷ main ∷ methodsToJVM className funNames meths ∷ []
  where
  header
    = ".class public" <+> className
    ∷ ".super java/lang/Object"
    ∷ []
  init
    = ".method public <init>()V"
    ∷ ""
    ∷ "  aload_0"
    ∷ "  invokespecial java/lang/Object/<init>()V"
    ∷ "  return"
    ∷ ""
    ∷ ".end method"
    ∷ []
  main
    = ".method public static main([Ljava/lang/String;)V"
    ∷ ".limit locals 1"
    ∷ ""
    ∷ ("  invokestatic" <+> className <> "/main()I")
    ∷ "  pop"
    ∷ "  return"
    ∷ ""
    ∷ ".end method"
    ∷ []

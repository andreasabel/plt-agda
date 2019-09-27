-- Convert WellTypedSyntax to AST

module InternalToAbstract where

open import Library
open import WellTypedSyntax
import CPP.AST as A

reifyVar : ∀{Γ t} (x : Var Γ t) → A.Id
reifyVar (var x _ _) = A.id x

reifyBuiltin : ∀ {t ts} → Builtin (funType ts t) → Name
reifyBuiltin bReadInt     = "readInt"
reifyBuiltin bReadDouble  = "readDouble"
reifyBuiltin bPrintInt    = "printInt"
reifyBuiltin bPrintDouble = "printDouble"

reifyTy : (t : Ty) → A.Type
reifyTy int    = A.type-int
reifyTy double = A.type-double
reifyTy bool   = A.type-bool

reifyType : (t : Type) → A.Type
reifyType (` t) = reifyTy t
reifyType void  = A.type-void

module _ {Σ : Sig} {Γ : Cxt}  where

  mutual

    reifyExp : ∀{t} → Exp Σ Γ t → A.Exp
    reifyExp (eConst {int} v)             = A.eInt v
    reifyExp (eConst {double} v)          = A.eDouble v
    reifyExp (eConst {bool} false)        = A.eFalse
    reifyExp (eConst {bool} true)         = A.eTrue
    reifyExp (eVar x)                     = A.eId (reifyVar x)
    reifyExp (eApp (fun x _) es)          = A.eApp (A.id x) (reifyExps es)
    reifyExp (eBuiltin f es)              = A.eApp (A.id (reifyBuiltin f)) (reifyExps es)
    reifyExp (eIncrDecr pre (incr a) x)   = A.ePreIncr (reifyVar x)
    reifyExp (eIncrDecr post (incr a) x)  = A.ePostIncr (reifyVar x)
    reifyExp (eIncrDecr pre (decr a) x)   = A.ePreDecr (reifyVar x)
    reifyExp (eIncrDecr post (decr a) x)  = A.ePostDecr (reifyVar x)
    reifyExp (eOp (arith (plus a)) e e')  = A.ePlus (reifyExp e) (reifyExp e')
    reifyExp (eOp (arith (minus a)) e e') = A.eMinus (reifyExp e) (reifyExp e')
    reifyExp (eOp (arith (times a)) e e') = A.eTimes (reifyExp e) (reifyExp e')
    reifyExp (eOp (arith (div a)) e e')   = A.eDiv (reifyExp e) (reifyExp e')
    reifyExp (eOp (cmp (lt a)) e e')      = A.eLt (reifyExp e) (reifyExp e')
    reifyExp (eOp (cmp (gt a)) e e')      = A.eGt (reifyExp e) (reifyExp e')
    reifyExp (eOp (cmp (ltEq a)) e e')    = A.eLtEq (reifyExp e) (reifyExp e')
    reifyExp (eOp (cmp (gtEq a)) e e')    = A.eGtEq (reifyExp e) (reifyExp e')
    reifyExp (eOp (cmp eq) e e')          = A.eEq (reifyExp e) (reifyExp e')
    reifyExp (eOp (cmp nEq) e e')         = A.eNEq (reifyExp e) (reifyExp e')
    reifyExp (eOp (logic and) e e')       = A.eAnd (reifyExp e) (reifyExp e')
    reifyExp (eOp (logic or) e e')        = A.eOr (reifyExp e) (reifyExp e')
    reifyExp (eAss x e)                   = A.eAss (reifyVar x) (reifyExp e)

    reifyExps : ∀{t} → Exps Σ Γ t → A.Exps
    reifyExps []       = A.eNil
    reifyExps (e ∷ es) = A.eSnoc (reifyExps es) (reifyExp e)

module _ {Σ : Sig} {rt : Type} where

  mutual

    reifyStm : ∀{Γ mt} → Stm Σ rt Γ mt → A.Stm
    reifyStm (sReturn e)            = A.sReturn (reifyExp e)
    reifyStm (sExp e)               = A.sExp (reifyExp e)
    reifyStm (sInit {t} x nothing)  = A.sDecls (reifyTy t) [ A.id x ]
    reifyStm (sInit {t} x (just e)) = A.sInit (reifyTy t) (A.id x) (reifyExp e)
    reifyStm (sBlock ss)            = A.sBlock (reifyStms ss)
    reifyStm (sWhile e s)           = A.sWhile (reifyExp e) (reifyStm s)
    reifyStm (sIfElse e s s')       = A.sIfElse (reifyExp e) (reifyStm s) (reifyStm s')

    reifyStms : ∀{Γ Δ Δ'} → Stms Σ rt Γ Δ Δ' → List A.Stm
    reifyStms []       = []
    reifyStms (s ∷ ss) = reifyStm s ∷ reifyStms ss

printVar : ∀{Γ t} (x : Var Γ t) → String
printVar (var x _ _) = x

printBuiltin : ∀ {t ts} → Builtin (funType ts t) → String
printBuiltin = reifyBuiltin

printTy : (t : Ty) → String
printTy = A.printType ∘ reifyTy

printType : (t : Type) → String
printType = A.printType ∘ reifyType

printExp : ∀{Σ Γ t} → Exp Σ Γ t → String
printExp = A.printExp ∘ reifyExp

printExps : ∀{Σ Γ t} → Exps Σ Γ t → String
printExps [] = ""
printExps (e ∷ []) = printExp e
printExps (e ∷ e' ∷ es) = printExps (e' ∷ es) <,> printExp e
-- printExps = A.printExps ∘ reifyExps

printStm : ∀{Σ rt Γ mt} → Stm Σ rt Γ mt → String
printStm = A.printStm ∘ reifyStm

printStms : ∀{Σ rt Γ Δ Δ'} → Stms Σ rt Γ Δ Δ' → String
printStms = A.printListStm ∘ reifyStms

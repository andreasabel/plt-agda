Type-preserving compilation via dependently typed syntax in Agda
================================================================

- Andreas Abel
- Winter meeting FP division
- 10 January 2020

C-- to JVM: Architecture of compiler
------------------------------------

- AST, parser and printer (Haskell) for C-- generated by BNFC
- Agda bindings to AST, parser and printer generated by BNFC
- Type checker produces well-typed syntax trees
- Compiler produces well-typed JVM-like code
- Printed to Jasmin syntax
- Jasmin generates ``.class`` file


Intrinsically well-typed C--
----------------------------

Types (simplified)

    a : ATy ::= int | double
    t : Ty  ::= a | bool

    Γ : Cxt = List Ty

Indices  ``x : a ∈ Γ``

                            i : a ∈ Γ
    ----------- here     -------------- there
    0 : a ∈ Γ,a          1+ i : a ∈ Γ,b

Expressions (simplified), fixed Γ

    data Exp (t : Ty) : Set where
      _+_  : (e₁ e₂ : Exp a)    → Exp a
      _<_  : (e₁ e₂ : Exp a)    → Exp bool
      _&&_ : (e₁ e₂ : Exp bool) → Exp bool
      var  : (x : t ∈ Γ)        → Exp t
      lit  : (v : Val t)        → Exp t

Statements (simplified)

    data Stm : Set where
      assign : (x : t ∈ Γ) (e : Exp t)      → Stm
      ifElse : (e : Exp bool) (s₁ s₂ : Stm) → Stm
      while  : (e : Exp bool) (s : Stm)     → Stm
      block  : (ss : List Stm)              → Stm


Compilation target: JVM
-----------------------

JVM manages memory: stack, heap, function calls

Each method runs with

- own local variable store
- own local stack

Byte-code verifier checks correct memory access.


Compilation schemes
-------------------

Taught to students in class Programming Language Technology.

Expressions: (leave value on the stack)

    ⟦ v : int ⟧ = iconst v
    ⟦ x : int ⟧ = iload x
    ⟦ e₁ + e₂ ⟧ = ⟦e₁⟧; ⟦e₂⟧; iadd

Statements: (leave nothing on the stack)

    ⟦ x = e ⟧ = ⟦e⟧; istore x

    ⟦ if (e) s₁ else s₂ ⟧ =
      L_else, L_end ← newLabel
               ⟦e⟧
               ifeq L_else
               ⟦s₁⟧
               goto L_end
      L_else:  ⟦s₂⟧
      L_end:

    ⟦ while (e) s ⟧ =
      L_start, L_end ← newLabel
      L_start: ⟦e⟧
               ifeq L_end
               ⟦s⟧
               goto L_start
      L_end:


Intrinsically well-typed JVM
----------------------------

We can produce statically well-typed JVM code.

- context Γ types variable store
- context Φ types stack

Jump-free instructions (simplified):

- variable store type Γ fixed
- stack can shrink and grow: Φ ⊸ Φ'

      data JF Φ Φ'
        iadd                 : JF (Φ,int,int)       (Φ,int)
        iload  (x : int ∈ Γ) : JF Φ                 (Φ,int)
        iconst (v : val int) : JF Φ                 (Φ,int)
        dmul                 : JF (Φ,double,double) (Φ,double)

Control: jump to label l.

- label l should be guaranteed to exist
- expected stack type Φ at label l should match current Φ
- each label l maps to a stack type Φ
- labels are de Bruijn indices into a list of stack types

      Λ : Labels = List Cxt

Flowcharts
----------

High-level control structures: flowcharts.

Compilation to flow charts  (``let`` and ``fix``):

    ⟦ if (e) s₁ else s₂ ; s ⟧ =
      let L_end  = ⟦s⟧
      let L_then = ⟦s₁⟧; goto L_end
      let L_else = ⟦s₂⟧; goto L_end
      ⟦e⟧
      branch L_then L_else


    ⟦ while (e) s₀ ; s ⟧ =
      let L_end = ⟦s⟧
      fix L_start.
        let L_body = ⟦s₀⟧; goto L_start
        ⟦e⟧
        branch L_body L_end


Intrinsically typed flowcharts
------------------------------

Typed by initial stack.

    data FC Λ Φ
      _∷_    (c : JF Φ Φ') (fc : FC Λ Φ')       : FC Λ Φ
      goto   (l : Φ ∈ Λ)                        : FC Λ Φ
      branch (l₁ l₂ : Φ ∈ Λ)                    : FC Λ (Φ,bool)
      let    (fc₁ : FC Λ Φ) (fc₂ : FC (Λ,Φ) Φ') : FC Λ Φ'
      fix    (fc  : FC (Λ,Φ) Φ)                 : FC Λ Φ

Labels are locally defined.


Compilation to flow charts
--------------------------

Compiling statements:

    ⟦ if (e) s₁ else s₂ ⟧(k) =
      let k
      let ⟦s₁⟧(goto 0)
      let ⟦s₂⟧(goto 1)
      ⟦e⟧(1,0)


    ⟦ while (e) s₀ ⟧(k) =
      let k
      fix
        let ⟦s₀⟧(goto 0)
        ⟦e⟧(0,2)

Compiling conditions:

    ⟦ true    ⟧(l₁,l₂) = goto l₁
    ⟦ e <  e' ⟧(l₁,l₂) = ⟦e⟧(⟦e'⟧(icmplt ∷ branch l₁ l₂))
    ⟦ e && e' ⟧(l₁,l₂) = let ⟦e'⟧(l₁,l₂) ⟦e⟧(1+l₁,0)

Compiling arithmetic expressions:

    ⟦ v     ⟧(k) = iconst v ∷ k
    ⟦ e + e'⟧(k) = ⟦e⟧(⟦e'⟧(iadd ∷ k))


Basic blocks
------------

Basic blocks are FCs without label definition (let,fix).

    flat : FC Λ Φ → Σ (τ : Λ' ⊇ Λ) (bbs : BBs Λ' τ) (bb : BB Λ' Φ)

    BBs Λ τ = AllExt (BB Λ) τ

``BBs`` provides one basic block for each new label in ``τ : Λ' ⊇ Λ``.
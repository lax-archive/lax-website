-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FinCases

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax624099.Problems
section
namespace Lax624099
end Lax624099

namespace Lax624099.Problems
end Lax624099.Problems

namespace Lax624099.Problems.DecisionProblem
end Lax624099.Problems.DecisionProblem

namespace Lax624099.Problems.DecisionProblem.ofPred
end Lax624099.Problems.DecisionProblem.ofPred
end

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Interpretations.FOInterpretation
end Lax904597.Interpretations.FOInterpretation

namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.Relativized.RelFOInterpretation
end Lax904597.Relativized.RelFOInterpretation

namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction
end

-- Lax904597.SecondOrder
section
namespace Lax904597.SecondOrder.SORealize
end Lax904597.SecondOrder.SORealize

namespace Lax904597.SecondOrder.soLang
end Lax904597.SecondOrder.soLang

namespace Lax904597.SecondOrder

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A second-order quantifier block: finitely many relation variables, with
given arities. The index type is arbitrary rather than an initial segment of
`ℕ`, so that constructions on blocks can build their natural index types. -/
structure SOBlock : Type 1 where
  /-- The index type of the relation variables of the block. -/
  ι : Type
  /-- A block has finitely many relation variables. -/
  [ιFinite : Finite ι]
  /-- The arity of each relation variable. -/
  arity : ι → ℕ

attribute [instance] SOBlock.ιFinite

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax624099.FiniteSatisfiability
section
namespace Lax624099.FiniteSatisfiability.FinSat.gval
end Lax624099.FiniteSatisfiability.FinSat.gval

namespace Lax624099.FiniteSatisfiability

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of encoded first-order sentences in
negation normal form. -/
inductive finsatRel : ℕ → Type
  /-- `le x y`: the order of the syntax. -/
  | le : finsatRel 2
  /-- `andN g`: the node `g` is the conjunction of its children. -/
  | andN : finsatRel 1
  /-- `orN g`: the node `g` is the disjunction of its children. -/
  | orN : finsatRel 1
  /-- `allN g`: the node `g` universally quantifies its bound variable. -/
  | allN : finsatRel 1
  /-- `exN g`: the node `g` existentially quantifies its bound variable. -/
  | exN : finsatRel 1
  /-- `child g c`: the node `c` is one of the children of the node `g`. -/
  | child : finsatRel 2
  /-- `bind g x`: the quantifier node `g` binds the variable `x`. -/
  | bind : finsatRel 2
  /-- `eqL g x y`: the node `g` is the literal `x = y`. -/
  | eqL : finsatRel 3
  /-- `neqL g x y`: the node `g` is the literal `x ≠ y`. -/
  | neqL : finsatRel 3
  /-- `posL g s`: the node `g` is a positive atom of the relation symbol
  `s`. -/
  | posL : finsatRel 2
  /-- `negL g s`: the node `g` is a negated atom of the relation symbol
  `s`. -/
  | negL : finsatRel 2
  /-- `arg g p x`: the argument of the atom `g` at position `p` is the
  variable `x`. -/
  | arg : finsatRel 3
  /-- `sig s p`: the relation symbol `s` has an argument position `p`. -/
  | sig : finsatRel 2
  /-- `root g`: the node `g` is the root of the encoded sentence. -/
  | root : finsatRel 1
  deriving DecidableEq

/-- The relational vocabulary of encoded first-order sentences: a parse DAG in
negation normal form, ordered by the order of its own syntax. -/
def finsat : Language :=
  ⟨fun _ => Empty, finsatRel⟩

/-- The order symbol of the syntax. -/
abbrev finsatLeSym : finsat.Relations 2 := .le

/-- The symbol of the child relation of the parse DAG. -/
abbrev finsatChildSym : finsat.Relations 2 := .child

/-- The symbol of positive atoms. -/
abbrev finsatPosSym : finsat.Relations 2 := .posL

/-- The symbol of negated atoms. -/
abbrev finsatNegSym : finsat.Relations 2 := .negL

/-- The symbol giving the arguments of an atom. -/
abbrev finsatArgSym : finsat.Relations 3 := .arg

/-- The symbol giving the signature of a relation symbol. -/
abbrev finsatSigSym : finsat.Relations 2 := .sig

open FirstOrder

open Language Structure

namespace FinSat

section Reading

variable {A : Type} [finsat.Structure A]

/-- `x` precedes `y` in the order of the syntax. -/
def Ord (x y : A) : Prop := RelMap finsatLeSym ![x, y]

/-- `x` strictly precedes `y` in the order of the syntax. -/
def OrdLt (x y : A) : Prop := Ord x y ∧ x ≠ y

/-- The node `c` is a child of the node `g`. -/
def ChildG (g c : A) : Prop := RelMap finsatChildSym ![g, c]

/-- The node `g` is a positive atom of the symbol `s`. -/
def PosG (g s : A) : Prop := RelMap finsatPosSym ![g, s]

/-- The node `g` is a negated atom of the symbol `s`. -/
def NegG (g s : A) : Prop := RelMap finsatNegSym ![g, s]

/-- The argument of the atom `g` at position `p` is the variable `x`. -/
def ArgG (g p x : A) : Prop := RelMap finsatArgSym ![g, p, x]

/-- The symbol `s` has an argument position `p`. -/
def SigG (s p : A) : Prop := RelMap finsatSigSym ![s, p]

end Reading

/-- **Well-formedness of an encoded sentence**: the order symbol is a linear
order and the parse DAG descends along it. -/
structure IsWF (A : Type) [finsat.Structure A] : Prop where
  /-- The order of the syntax is reflexive. -/
  ord_refl : ∀ x : A, Ord x x
  /-- The order of the syntax is transitive. -/
  ord_trans : ∀ x y z : A, Ord x y → Ord y z → Ord x z
  /-- The order of the syntax is antisymmetric. -/
  ord_antisymm : ∀ x y : A, Ord x y → Ord y x → x = y
  /-- The order of the syntax is total. -/
  ord_total : ∀ x y : A, Ord x y ∨ Ord y x
  /-- Children come strictly earlier: the parse DAG is acyclic. -/
  child_lt : ∀ g c : A, ChildG g c → OrdLt c g
  /-- An atom has at most one argument at each position. -/
  arg_fun : ∀ g p x x' : A, ArgG g p x → ArgG g p x' → x = x'
  /-- An atom has at most one relation symbol. -/
  atom_sym : ∀ g s s' : A, (PosG g s ∨ NegG g s) → (PosG g s' ∨ NegG g s') → s = s'
  /-- An atom only has arguments at the positions of its symbol's signature. -/
  arg_sig : ∀ g s p x : A, (PosG g s ∨ NegG g s) → ArgG g p x → SigG s p
  /-- An atom has an argument at every position of its symbol's signature. -/
  arg_tot : ∀ g s p : A, (PosG g s ∨ NegG g s) → SigG s p → ∃ x, ArgG g p x

section Semantics

variable {A M : Type} [finsat.Structure A]

end Semantics

end FinSat

open Lax904597.Problems Lax624099.Problems

end Lax624099.FiniteSatisfiability
end

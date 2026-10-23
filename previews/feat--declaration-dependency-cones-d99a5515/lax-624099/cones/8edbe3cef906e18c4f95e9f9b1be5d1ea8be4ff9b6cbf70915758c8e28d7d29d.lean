-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
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

-- Lax624099.ValueInvention
section
namespace Lax624099
end Lax624099

namespace Lax624099.ValueInvention
end Lax624099.ValueInvention

namespace Lax624099.ValueInvention.IsOld
end Lax624099.ValueInvention.IsOld

namespace Lax624099.ValueInvention.oldMarkStructure
end Lax624099.ValueInvention.oldMarkStructure

namespace Lax624099.ValueInvention.oldRel
end Lax624099.ValueInvention.oldRel

namespace Lax624099.ValueInvention.oldRel.old
end Lax624099.ValueInvention.oldRel.old
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

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax624099.ClassRE
section
namespace Lax624099.ClassRE
end Lax624099.ClassRE

namespace Lax624099.ClassRE.DecisionProblem
end Lax624099.ClassRE.DecisionProblem
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

-- Lax624099.CodeHalting
section
namespace Lax624099.CodeHalting
end Lax624099.CodeHalting

namespace Lax624099.CodeHalting.DecodesTo
end Lax624099.CodeHalting.DecodesTo

namespace Lax624099.CodeHalting.codeRel
end Lax624099.CodeHalting.codeRel

namespace Lax624099.CodeHalting.codeRel.carg1
end Lax624099.CodeHalting.codeRel.carg1

namespace Lax624099.CodeHalting.codeRel.carg2
end Lax624099.CodeHalting.codeRel.carg2

namespace Lax624099.CodeHalting.codeRel.ccomp
end Lax624099.CodeHalting.codeRel.ccomp

namespace Lax624099.CodeHalting.codeRel.cleft
end Lax624099.CodeHalting.codeRel.cleft

namespace Lax624099.CodeHalting.codeRel.cpair
end Lax624099.CodeHalting.codeRel.cpair

namespace Lax624099.CodeHalting.codeRel.cprec
end Lax624099.CodeHalting.codeRel.cprec

namespace Lax624099.CodeHalting.codeRel.crfind
end Lax624099.CodeHalting.codeRel.crfind

namespace Lax624099.CodeHalting.codeRel.cright
end Lax624099.CodeHalting.codeRel.cright

namespace Lax624099.CodeHalting.codeRel.croot
end Lax624099.CodeHalting.codeRel.croot

namespace Lax624099.CodeHalting.codeRel.csucc
end Lax624099.CodeHalting.codeRel.csucc

namespace Lax624099.CodeHalting.codeRel.czero
end Lax624099.CodeHalting.codeRel.czero
end

-- Lax624099.FiniteSatisfiability
section
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

/-- The symbol marking conjunction nodes. -/
abbrev finsatAndSym : finsat.Relations 1 := .andN

/-- The symbol marking disjunction nodes. -/
abbrev finsatOrSym : finsat.Relations 1 := .orN

/-- The symbol marking universal quantifier nodes. -/
abbrev finsatAllSym : finsat.Relations 1 := .allN

/-- The symbol marking existential quantifier nodes. -/
abbrev finsatExSym : finsat.Relations 1 := .exN

/-- The symbol of the child relation of the parse DAG. -/
abbrev finsatChildSym : finsat.Relations 2 := .child

/-- The symbol binding a variable to a quantifier node. -/
abbrev finsatBindSym : finsat.Relations 2 := .bind

/-- The symbol of positive equality literals. -/
abbrev finsatEqSym : finsat.Relations 3 := .eqL

/-- The symbol of negated equality literals. -/
abbrev finsatNeqSym : finsat.Relations 3 := .neqL

/-- The symbol of positive atoms. -/
abbrev finsatPosSym : finsat.Relations 2 := .posL

/-- The symbol of negated atoms. -/
abbrev finsatNegSym : finsat.Relations 2 := .negL

/-- The symbol giving the arguments of an atom. -/
abbrev finsatArgSym : finsat.Relations 3 := .arg

/-- The symbol giving the signature of a relation symbol. -/
abbrev finsatSigSym : finsat.Relations 2 := .sig

/-- The symbol marking the root node. -/
abbrev finsatRootSym : finsat.Relations 1 := .root

open FirstOrder

open Language Structure

namespace FinSat

section Reading

variable {A : Type} [finsat.Structure A]

/-- `x` precedes `y` in the order of the syntax. -/
def Ord (x y : A) : Prop := RelMap finsatLeSym ![x, y]

/-- `x` strictly precedes `y` in the order of the syntax. -/
def OrdLt (x y : A) : Prop := Ord x y ∧ x ≠ y

/-- The node `g` is a conjunction. -/
def AndG (g : A) : Prop := RelMap finsatAndSym ![g]

/-- The node `g` is a disjunction. -/
def OrG (g : A) : Prop := RelMap finsatOrSym ![g]

/-- The node `g` is a universal quantifier. -/
def AllG (g : A) : Prop := RelMap finsatAllSym ![g]

/-- The node `g` is an existential quantifier. -/
def ExG (g : A) : Prop := RelMap finsatExSym ![g]

/-- The node `c` is a child of the node `g`. -/
def ChildG (g c : A) : Prop := RelMap finsatChildSym ![g, c]

/-- The quantifier node `g` binds the variable `x`. -/
def BindG (g x : A) : Prop := RelMap finsatBindSym ![g, x]

/-- The node `g` is the literal `x = y`. -/
def EqG (g x y : A) : Prop := RelMap finsatEqSym ![g, x, y]

/-- The node `g` is the literal `x ≠ y`. -/
def NeqG (g x y : A) : Prop := RelMap finsatNeqSym ![g, x, y]

/-- The node `g` is a positive atom of the symbol `s`. -/
def PosG (g s : A) : Prop := RelMap finsatPosSym ![g, s]

/-- The node `g` is a negated atom of the symbol `s`. -/
def NegG (g s : A) : Prop := RelMap finsatNegSym ![g, s]

/-- The argument of the atom `g` at position `p` is the variable `x`. -/
def ArgG (g p x : A) : Prop := RelMap finsatArgSym ![g, p, x]

/-- The symbol `s` has an argument position `p`. -/
def SigG (s p : A) : Prop := RelMap finsatSigSym ![s, p]

/-- The node `g` is the root of the encoded sentence. -/
def RootG (g : A) : Prop := RelMap finsatRootSym ![g]

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

open Classical in
/-- Updating an environment at one variable. (Classical: the instance is a
bare type, with no decidable equality.) -/
noncomputable def upd {A M : Type} (v : A → M) (x : A) (d : M) : A → M :=
  fun z => if z = x then d else v z

section Semantics

variable {A M : Type} [finsat.Structure A]

/-- **One unfolding of the truth definition**: the value of the node `g` under
the environment `v`, given the values `rec` of the nodes below it. A
conjunction node holds when all its children do, a disjunction node when one
of them does, a quantifier node when all (respectively one) of the values of
its bound variable make all (one of) its children hold; a literal reads the
environment, an atom the interpretation `I`, on an assignment `w` of the
argument positions matching the environment on the arguments of the atom. -/
noncomputable def gstep (I : A → (A → M) → Prop) (rec : (A → M) → A → Prop)
    (v : A → M) (g : A) : Prop :=
  (AndG g ∧ ∀ c, ChildG g c → rec v c) ∨
  (OrG g ∧ ∃ c, ChildG g c ∧ rec v c) ∨
  (AllG g ∧ ∀ x, BindG g x → ∀ d : M, ∀ c, ChildG g c → rec (upd v x d) c) ∨
  (ExG g ∧ ∃ x, BindG g x ∧ ∃ d : M, ∃ c, ChildG g c ∧ rec (upd v x d) c) ∨
  (∃ x y, EqG g x y ∧ v x = v y) ∨
  (∃ x y, NeqG g x y ∧ v x ≠ v y) ∨
  (∃ s, PosG g s ∧ ∃ w : A → M, (∀ p x, ArgG g p x → w p = v x) ∧ I s w) ∨
  (∃ s, NegG g s ∧ ∃ w : A → M, (∀ p x, ArgG g p x → w p = v x) ∧ ¬I s w)

/-- **Satisfaction, by iteration**: `gval I k v g` is the `k`-th approximant of
the truth of the node `g` under the environment `v`. -/
noncomputable def gval (I : A → (A → M) → Prop) : ℕ → (A → M) → A → Prop
  | 0 => fun _ _ => False
  | k + 1 => gstep I (gval I k)

/-- **The node `g` holds under the environment `v`**: the least fixed point of
the truth definition, reached because a finite parse DAG has finite depth. -/
def Gval (I : A → (A → M) → Prop) (v : A → M) (g : A) : Prop :=
  ∃ k, gval I k v g

/-- An interpretation is **local** when the value of a symbol depends only on
the arguments its signature declares. -/
def Local (I : A → (A → M) → Prop) : Prop :=
  ∀ (s : A) (w w' : A → M), (∀ p, SigG s p → w p = w' p) → (I s w ↔ I s w')

end Semantics

/-- **The encoded sentence has a finite model**: the instance is well-formed
and there is a finite nonempty universe with a local interpretation of the
relation symbols under which every environment satisfies the root – that is, a
finite model of the universal closure of the encoded formula. -/
def FinSatOn (A : Type) [finsat.Structure A] : Prop :=
  IsWF A ∧ ∃ (M : Type) (_ : Finite M) (_ : Nonempty M) (I : A → (A → M) → Prop),
    Local I ∧ ∀ (v : A → M) (g : A), RootG g → Gval I v g

end FinSat

open Lax904597.Problems Lax624099.Problems

end Lax624099.FiniteSatisfiability
end

-- Lax904597.Machines
section
namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Machines.Config
end Lax904597.Machines.Config

namespace Lax904597.Machines.TMData
end Lax904597.Machines.TMData

namespace Lax904597.Machines.turingRel
end Lax904597.Machines.turingRel

namespace Lax904597.Machines.Config.ext
end Lax904597.Machines.Config.ext

namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines.turingRel.acc
end Lax904597.Machines.turingRel.acc

namespace Lax904597.Machines.turingRel.blank
end Lax904597.Machines.turingRel.blank

namespace Lax904597.Machines.turingRel.inp
end Lax904597.Machines.turingRel.inp

namespace Lax904597.Machines.turingRel.le
end Lax904597.Machines.turingRel.le

namespace Lax904597.Machines.turingRel.posn
end Lax904597.Machines.turingRel.posn

namespace Lax904597.Machines.turingRel.right
end Lax904597.Machines.turingRel.right

namespace Lax904597.Machines.turingRel.start
end Lax904597.Machines.turingRel.start

namespace Lax904597.Machines.turingRel.tdst
end Lax904597.Machines.turingRel.tdst

namespace Lax904597.Machines.turingRel.tr
end Lax904597.Machines.turingRel.tr

namespace Lax904597.Machines.turingRel.tread
end Lax904597.Machines.turingRel.tread

namespace Lax904597.Machines.turingRel.tsrc
end Lax904597.Machines.turingRel.tsrc

namespace Lax904597.Machines.turingRel.twrite
end Lax904597.Machines.turingRel.twrite
end

-- Lax624099.ConcreteInstances
section
namespace Lax624099.ConcreteInstances
end Lax624099.ConcreteInstances

namespace Lax624099.ConcreteInstances.DecisionProblem
end Lax624099.ConcreteInstances.DecisionProblem

namespace Lax624099.ConcreteInstances.FinStruct
end Lax624099.ConcreteInstances.FinStruct

namespace Lax624099.ConcreteInstances.FinVocab
end Lax624099.ConcreteInstances.FinVocab

namespace Lax624099.ConcreteInstances.tupleIdx
end Lax624099.ConcreteInstances.tupleIdx

namespace Lax624099.ConcreteInstances.FinStruct.equivProd
end Lax624099.ConcreteInstances.FinStruct.equivProd
end

-- Lax624099.Halting
section
namespace Lax624099.Halting
end Lax624099.Halting

namespace Lax624099.Halting.ConfigU
end Lax624099.Halting.ConfigU

namespace Lax624099.Halting.TMData
end Lax624099.Halting.TMData

namespace Lax624099.Halting.ConfigU.ext
end Lax624099.Halting.ConfigU.ext

namespace Lax624099.Halting.TMData.StepsInU
end Lax624099.Halting.TMData.StepsInU
end

-- Lax624099.PostCorrespondence
section
namespace Lax624099.PostCorrespondence
end Lax624099.PostCorrespondence

namespace Lax624099.PostCorrespondence.Pcp
end Lax624099.PostCorrespondence.Pcp

namespace Lax624099.PostCorrespondence.pcpRel
end Lax624099.PostCorrespondence.pcpRel

namespace Lax624099.PostCorrespondence.Pcp.IsWF
end Lax624099.PostCorrespondence.Pcp.IsWF

namespace Lax624099.PostCorrespondence.pcpRel.dom
end Lax624099.PostCorrespondence.pcpRel.dom

namespace Lax624099.PostCorrespondence.pcpRel.le
end Lax624099.PostCorrespondence.pcpRel.le

namespace Lax624099.PostCorrespondence.pcpRel.uAt
end Lax624099.PostCorrespondence.pcpRel.uAt

namespace Lax624099.PostCorrespondence.pcpRel.vAt
end Lax624099.PostCorrespondence.pcpRel.vAt
end

-- Lax624099.FiniteSatisfiabilityInvariance
section
namespace Lax624099.FiniteSatisfiabilityInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes

open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE

open Lax624099.FiniteSatisfiability

open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence

open Lax624099.ConcreteInstances

/-- The property `FinSat.FinSatOn` is isomorphism-invariant. -/
axiom finSatOn_iso : ∀ {A B : Type} [finsat.Structure A] [finsat.Structure B],
  (A ≃[finsat] B) → (FinSat.FinSatOn A ↔ FinSat.FinSatOn B)

end Lax624099.FiniteSatisfiabilityInvariance
end

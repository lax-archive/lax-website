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
namespace Lax624099.FiniteSatisfiability.FinSat.IsWF
end Lax624099.FiniteSatisfiability.FinSat.IsWF

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

open FirstOrder

open Language Structure

namespace FinSat

section Reading

variable {A : Type} [finsat.Structure A]

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

end Reading

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

end Semantics

end FinSat

open Lax904597.Problems Lax624099.Problems

end Lax624099.FiniteSatisfiability
end

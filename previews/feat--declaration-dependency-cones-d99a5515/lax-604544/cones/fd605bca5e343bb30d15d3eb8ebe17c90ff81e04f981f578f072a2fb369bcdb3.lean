-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
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

-- Lax485149.Complement
section
namespace Lax485149
end Lax485149

namespace Lax485149.Complement
end Lax485149.Complement

namespace Lax485149.Complement.DecisionProblem
end Lax485149.Complement.DecisionProblem
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

-- Lax485149.SecondOrderAtoms
section
namespace Lax485149
end Lax485149

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax485149.SecondOrderAtoms.SOAtom
end Lax485149.SecondOrderAtoms.SOAtom
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

-- Lax485149.KromFragment
section
namespace Lax485149.KromFragment
end Lax485149.KromFragment

namespace Lax485149.KromFragment.KromClause
end Lax485149.KromFragment.KromClause

namespace Lax485149.KromFragment.KromLit
end Lax485149.KromFragment.KromLit

namespace Lax485149.KromFragment.KromProgram
end Lax485149.KromFragment.KromProgram
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

-- Lax485149.ClassNL
section
namespace Lax485149.ClassNL
end Lax485149.ClassNL
end

-- Lax485149.Problems
section
namespace Lax485149
end Lax485149

namespace Lax485149.Problems
end Lax485149.Problems

namespace Lax485149.Problems.DecisionProblem
end Lax485149.Problems.DecisionProblem

namespace Lax485149.Problems.DecisionProblem.ofPred
end Lax485149.Problems.DecisionProblem.ofPred
end

-- Lax904597.Sat
section
namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.Sat.satRel
end Lax904597.Sat.satRel

namespace Lax904597.Sat.satRel.isClause
end Lax904597.Sat.satRel.isClause

namespace Lax904597.Sat.satRel.negIn
end Lax904597.Sat.satRel.negIn

namespace Lax904597.Sat.satRel.posIn
end Lax904597.Sat.satRel.posIn
end

-- Lax485149.TwoSat
section
namespace Lax485149.TwoSat
end Lax485149.TwoSat

namespace Lax485149.TwoSat.SatOcc
end Lax485149.TwoSat.SatOcc
end

-- Lax535992.HornFragment
section
namespace Lax535992
end Lax535992

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.HornFragment.HornClause
end Lax535992.HornFragment.HornClause

namespace Lax535992.HornFragment.HornProgram
end Lax535992.HornFragment.HornProgram
end

-- Lax535992.ClassPTIME
section
namespace Lax535992.ClassPTIME
end Lax535992.ClassPTIME
end

-- Lax535992.HornSat
section
namespace Lax535992
end Lax535992

namespace Lax535992.HornSat
end Lax535992.HornSat
end

-- Lax564036.Hierarchy
section
namespace Lax564036
end Lax564036

namespace Lax564036.Hierarchy
end Lax564036.Hierarchy

namespace Lax564036.Hierarchy.SigmaP
end Lax564036.Hierarchy.SigmaP
end

-- Lax564036.Tautology
section
namespace Lax564036
end Lax564036

namespace Lax564036.Tautology
end Lax564036.Tautology
end

-- Lax604544.RelationIsomorphism
section
namespace Lax604544.RelationIsomorphism

section Generic

variable {A : Type}

/-- Some map is a bijection of the `PV`-vertices onto the `HV`-vertices
carrying `PE`-edges to `HE`-edges *and back*: an isomorphism of the two marked
graphs. -/
def RelIsoOn (PV HV : A → Prop) (PE HE : A → A → Prop) : Prop :=
  ∃ f : A → A, (∀ x, PV x → HV (f x)) ∧
    (∀ x y, PV x → PV y → f x = f y → x = y) ∧
    (∀ y, HV y → ∃ x, PV x ∧ f x = y) ∧
    ∀ x y, PV x → PV y → (PE x y ↔ HE (f x) (f y))

end Generic

end Lax604544.RelationIsomorphism
end

-- Lax604544.DagIsomorphism
section
namespace Lax604544.DagIsomorphism
end Lax604544.DagIsomorphism

namespace Lax604544.DagIsomorphism.twoDagsRel
end Lax604544.DagIsomorphism.twoDagsRel

namespace Lax604544.DagIsomorphism.twoDagsRel.hostArc
end Lax604544.DagIsomorphism.twoDagsRel.hostArc

namespace Lax604544.DagIsomorphism.twoDagsRel.hostLt
end Lax604544.DagIsomorphism.twoDagsRel.hostLt

namespace Lax604544.DagIsomorphism.twoDagsRel.hostV
end Lax604544.DagIsomorphism.twoDagsRel.hostV

namespace Lax604544.DagIsomorphism.twoDagsRel.patArc
end Lax604544.DagIsomorphism.twoDagsRel.patArc

namespace Lax604544.DagIsomorphism.twoDagsRel.patLt
end Lax604544.DagIsomorphism.twoDagsRel.patLt

namespace Lax604544.DagIsomorphism.twoDagsRel.patV
end Lax604544.DagIsomorphism.twoDagsRel.patV
end

-- Lax604544.Degrees
section
namespace Lax604544
end Lax604544

namespace Lax604544.Degrees
end Lax604544.Degrees
end

-- Lax799700.Problems
section
namespace Lax799700
end Lax799700

namespace Lax799700.Problems
end Lax799700.Problems

namespace Lax799700.Problems.DecisionProblem
end Lax799700.Problems.DecisionProblem

namespace Lax799700.Problems.DecisionProblem.ofPred
end Lax799700.Problems.DecisionProblem.ofPred
end

-- Lax799700.SubgraphIso
section
namespace Lax799700.SubgraphIso

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive twoGraphsRel : ℕ → Type where
/-- `patV a`: `a` is a vertex of the pattern graph. -/
  | patV : twoGraphsRel 1
/-- `hostV a`: `a` is a vertex of the host graph. -/
  | hostV : twoGraphsRel 1
/-- `patE a b`: there is an edge of the pattern from `a` to `b`. -/
  | patE : twoGraphsRel 2
/-- `hostE a b`: there is an edge of the host from `a` to `b`. -/
  | hostE : twoGraphsRel 2
  deriving DecidableEq

/-- The relational language of pattern-and-host graphs: two graphs sharing a
universe, each with its own vertex mark and adjacency relation. -/
def twoGraphs : FirstOrder.Language :=
  ⟨fun _ => Empty, twoGraphsRel⟩

/-- `patV a`: `a` is a vertex of the pattern graph. -/
abbrev tgPatV : twoGraphs.Relations 1 :=
  .patV

/-- `hostV a`: `a` is a vertex of the host graph. -/
abbrev tgHostV : twoGraphs.Relations 1 :=
  .hostV

/-- `patE a b`: there is an edge of the pattern from `a` to `b`. -/
abbrev tgPatE : twoGraphs.Relations 2 :=
  .patE

/-- `hostE a b`: there is an edge of the host from `a` to `b`. -/
abbrev tgHostE : twoGraphs.Relations 2 :=
  .hostE

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Generic

variable {A : Type}

end Generic

section Problem

section Shorthands

variable {A : Type} [twoGraphs.Structure A]

/-- `patV a`: `a` is a vertex of the pattern graph.  -/
def TGPatV {A : Type} [twoGraphs.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgPatV ![a0]

/-- `hostV a`: `a` is a vertex of the host graph.  -/
def TGHostV {A : Type} [twoGraphs.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgHostV ![a0]

/-- `patE a b`: there is an edge of the pattern from `a` to `b`.  -/
def TGPatE {A : Type} [twoGraphs.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgPatE ![a0, a1]

/-- `hostE a b`: there is an edge of the host from `a` to `b`.  -/
def TGHostE {A : Type} [twoGraphs.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap tgHostE ![a0, a1]

end Shorthands

variable (A : Type) [twoGraphs.Structure A]

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.SubgraphIso
end

-- Lax604544.GraphIsomorphism
section
namespace Lax604544.GraphIsomorphism

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Classes Lax485149.Problems Lax799700.SubgraphIso

open Lax604544.RelationIsomorphism Lax604544.Degrees

section Problem

variable (A : Type) [twoGraphs.Structure A]

/-- The two marked graphs of the instance are isomorphic. -/
def HasDigraphIso : Prop :=
  Finite A ∧ RelIsoOn (TGPatV (A := A)) TGHostV TGPatE TGHostE

end Problem

section Generic

variable {A : Type}

end Generic

section Problem

variable (A : Type) [twoGraphs.Structure A]

end Problem

end Lax604544.GraphIsomorphism
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

-- Lax624099.FiniteSatisfiability
section
namespace Lax624099.FiniteSatisfiability
end Lax624099.FiniteSatisfiability

namespace Lax624099.FiniteSatisfiability.FinSat
end Lax624099.FiniteSatisfiability.FinSat

namespace Lax624099.FiniteSatisfiability.finsatRel
end Lax624099.FiniteSatisfiability.finsatRel

namespace Lax624099.FiniteSatisfiability.FinSat.IsWF
end Lax624099.FiniteSatisfiability.FinSat.IsWF

namespace Lax624099.FiniteSatisfiability.FinSat.gval
end Lax624099.FiniteSatisfiability.FinSat.gval

namespace Lax624099.FiniteSatisfiability.finsatRel.allN
end Lax624099.FiniteSatisfiability.finsatRel.allN

namespace Lax624099.FiniteSatisfiability.finsatRel.andN
end Lax624099.FiniteSatisfiability.finsatRel.andN

namespace Lax624099.FiniteSatisfiability.finsatRel.arg
end Lax624099.FiniteSatisfiability.finsatRel.arg

namespace Lax624099.FiniteSatisfiability.finsatRel.bind
end Lax624099.FiniteSatisfiability.finsatRel.bind

namespace Lax624099.FiniteSatisfiability.finsatRel.child
end Lax624099.FiniteSatisfiability.finsatRel.child

namespace Lax624099.FiniteSatisfiability.finsatRel.eqL
end Lax624099.FiniteSatisfiability.finsatRel.eqL

namespace Lax624099.FiniteSatisfiability.finsatRel.exN
end Lax624099.FiniteSatisfiability.finsatRel.exN

namespace Lax624099.FiniteSatisfiability.finsatRel.le
end Lax624099.FiniteSatisfiability.finsatRel.le

namespace Lax624099.FiniteSatisfiability.finsatRel.negL
end Lax624099.FiniteSatisfiability.finsatRel.negL

namespace Lax624099.FiniteSatisfiability.finsatRel.neqL
end Lax624099.FiniteSatisfiability.finsatRel.neqL

namespace Lax624099.FiniteSatisfiability.finsatRel.orN
end Lax624099.FiniteSatisfiability.finsatRel.orN

namespace Lax624099.FiniteSatisfiability.finsatRel.posL
end Lax624099.FiniteSatisfiability.finsatRel.posL

namespace Lax624099.FiniteSatisfiability.finsatRel.root
end Lax624099.FiniteSatisfiability.finsatRel.root

namespace Lax624099.FiniteSatisfiability.finsatRel.sig
end Lax624099.FiniteSatisfiability.finsatRel.sig
end

-- Lax604544.IsomorphismInvariance
section
namespace Lax604544.IsomorphismInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes

open Lax904597.Sat Lax799700.SubgraphIso

open Lax485149.Problems Lax485149.TwoSat Lax485149.ClassNL Lax535992.HornSat Lax535992.ClassPTIME

open Lax564036.Hierarchy Lax564036.Tautology Lax624099.ClassRE Lax624099.FiniteSatisfiability

open Lax604544.Degrees Lax604544.RelationIsomorphism

open Lax604544.GraphIsomorphism Lax604544.DagIsomorphism

/-- Having isomorphic marked graphs is isomorphism-invariant. -/
axiom hasDigraphIso_iso : ∀ {A B : Type} [twoGraphs.Structure A] [twoGraphs.Structure B],
  (A ≃[twoGraphs] B) → (HasDigraphIso A ↔ HasDigraphIso B)

end Lax604544.IsomorphismInvariance
end

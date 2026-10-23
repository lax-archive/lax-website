-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Group.Even
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.SetTheory.Cardinal.Finite

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction

namespace Lax904597.Interpretations

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A tagged `dim`-dimensional first-order interpretation of `L'` in `L`:
the defining `L`-formula of each relation symbol of `L'`, for each tuple of
tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
argument tuple. -/
structure FOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) where
  /-- The defining `L`-formula of each relation symbol of `L'`, for each tuple
  of tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
  argument tuple. -/
  relFormula : ∀ {n : ℕ}, L'.Relations n → (Fin n → Tag) → L.Formula (Fin n × Fin dim)

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end FOInterpretation

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

end Ordered

end Lax904597.Interpretations
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

/-- The relational vocabulary of a block: one relation symbol per relation
variable. -/
def SOBlock.lang (B : SOBlock) : Language :=
  ⟨fun _ => Empty, fun n => {i : B.ι // B.arity i = n}⟩

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax535992.InflationaryFixedPoint
section
namespace Lax535992
end Lax535992

namespace Lax535992.InflationaryFixedPoint
end Lax535992.InflationaryFixedPoint

namespace Lax535992.InflationaryFixedPoint.SOBlock
end Lax535992.InflationaryFixedPoint.SOBlock

namespace Lax535992.InflationaryFixedPoint.StepDef
end Lax535992.InflationaryFixedPoint.StepDef
end

-- Lax134656.PartialFixedPoint
section
namespace Lax134656
end Lax134656

namespace Lax134656.PartialFixedPoint
end Lax134656.PartialFixedPoint

namespace Lax134656.PartialFixedPoint.StepDef
end Lax134656.PartialFixedPoint.StepDef
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

-- Lax485149.TransitiveClosure
section
namespace Lax485149.TransitiveClosure

open Lax904597.Problems

open FirstOrder

open Language

/-- A single-`TC` definition: the transition formula of a graph on `k`-tuples,
together with formulas for the admissible start and end tuples. All three are
first-order over the ordered expansion of the vocabulary, so that they may
mention the linear order, as the ordered setting of the capture theorem
allows. -/
structure TCSpec (L : Language.{0, 0}) where
  /-- The *modes*: a finite amount of state the walk carries besides its tuple
  of elements. Tuples of elements cannot hold finite data of their own – a
  one-element universe has only one tuple – so, exactly as tags replace the
  order-encoded sorts of a textbook interpretation in `FOInterpretation`, a
  mode carries what the tuple cannot. -/
  Mode : Type
  /-- Modes are finite. -/
  [modeFinite : Finite Mode]
  /-- The arity: the walk runs on `k`-tuples of elements. -/
  k : ℕ
  /-- The transition formula, one per pair of modes, with two `k`-tuples of
  free variables: the current tuple on the left, the next one on the right. -/
  step : Mode → Mode → (L.sum Language.order).Formula (Fin k ⊕ Fin k)
  /-- The formula defining the admissible starting tuples, per mode. -/
  src : Mode → (L.sum Language.order).Formula (Fin k)
  /-- The formula defining the accepting tuples, per mode. -/
  tgt : Mode → (L.sum Language.order).Formula (Fin k)

attribute [instance] TCSpec.modeFinite

namespace TCSpec

section Semantics

variable {L : Language.{0, 0}} (spec : TCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

end Semantics

end TCSpec

end Lax485149.TransitiveClosure
end

-- Lax485149.DeterministicTransitiveClosure
section
namespace Lax485149.DeterministicTransitiveClosure
end Lax485149.DeterministicTransitiveClosure

namespace Lax485149.DeterministicTransitiveClosure.TCSpec
end Lax485149.DeterministicTransitiveClosure.TCSpec
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction

namespace Lax904597.Relativized

open FirstOrder FirstOrder.Language Lax904597.Problems Lax904597.Interpretations

/-- A relativized interpretation: an interpretation together with the domain
formula of each tag. -/
structure RelFOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ)
    extends FOInterpretation L L' Tag dim where
  /-- The domain formula of each tag: a tagged tuple `(t, ā)` belongs to the
  target universe iff `domFormula t` holds of `ā`. -/
  domFormula : Tag → L.Formula (Fin dim)

namespace RelFOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end RelFOInterpretation

end Lax904597.Relativized
end

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax485149.ClassL
section
namespace Lax485149.ClassL
end Lax485149.ClassL
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

-- Lax485149.ClassNL
section
namespace Lax485149.ClassNL
end Lax485149.ClassNL
end

-- Lax485149.FirstOrderDefinability
section
namespace Lax485149
end Lax485149

namespace Lax485149.FirstOrderDefinability
end Lax485149.FirstOrderDefinability
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

-- Lax895169.BitPredicate
section
namespace Lax895169
end Lax895169

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax895169.BitPredicate.prefixHolds
end Lax895169.BitPredicate.prefixHolds
end

-- Lax895169.ArithmeticLogic
section
namespace Lax895169.ArithmeticLogic
end Lax895169.ArithmeticLogic

namespace Lax895169.ArithmeticLogic.arithRel
end Lax895169.ArithmeticLogic.arithRel

namespace Lax895169.ArithmeticLogic.arithStructure
end Lax895169.ArithmeticLogic.arithStructure

namespace Lax895169.ArithmeticLogic.arithRel.le
end Lax895169.ArithmeticLogic.arithRel.le

namespace Lax895169.ArithmeticLogic.arithRel.plus
end Lax895169.ArithmeticLogic.arithRel.plus

namespace Lax895169.ArithmeticLogic.arithRel.times
end Lax895169.ArithmeticLogic.arithRel.times
end

-- Lax945089.EhrenfeuchtGames
section
namespace Lax945089.EhrenfeuchtGames.qdepth
end Lax945089.EhrenfeuchtGames.qdepth

namespace Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- A **legal position** of the Ehrenfeucht–Fraïssé game: two tuples of equal
length, one on each side, satisfying the same equalities between their
coordinates and the same base relations at every selection of coordinates.
Equivalently, matching coordinate to coordinate is a partial isomorphism. -/
def PartialIso (L : Language.{0, 0}) {M N : Type} [L.Structure M] [L.Structure N] {j : ℕ}
    (a : Fin j → M) (b : Fin j → N) : Prop :=
  (∀ i i' : Fin j, a i = a i' ↔ b i = b i') ∧
    ∀ (l : ℕ) (R : L.Relations l) (g : Fin l → Fin j),
      ((RelMap R fun p => a (g p)) ↔ RelMap R fun p => b (g p))

/-- **The stages of the Ehrenfeucht–Fraïssé refinement**: `efStage L n a b`
says that from the position `(a, b)` the duplicator survives `n` further
rounds – the position is legal, and whichever element the spoiler appends on
either side, the duplicator can append one on the other and survive `n - 1`
more rounds. -/
def efStage (L : Language.{0, 0}) {M N : Type} [L.Structure M] [L.Structure N] :
    ℕ → ∀ {j : ℕ}, (Fin j → M) → (Fin j → N) → Prop
  | 0, _, a, b => PartialIso L a b
  | n + 1, _, a, b =>
      PartialIso L a b ∧
        (∀ c : M, ∃ d : N, efStage L n (Fin.snoc a c) (Fin.snoc b d)) ∧
        (∀ d : N, ∃ c : M, efStage L n (Fin.snoc a c) (Fin.snoc b d))

/-- **`n`-round equivalence**: the duplicator survives `n` rounds of the
Ehrenfeucht–Fraïssé game on `M` and `N` played from the empty position. -/
def EFEquiv (L : Language.{0, 0}) (M N : Type) [L.Structure M] [L.Structure N] (n : ℕ) : Prop :=
  efStage L n (default : Fin 0 → M) (default : Fin 0 → N)

end Lax945089.EhrenfeuchtGames
end

-- Lax945089.Even
section
namespace Lax945089
end Lax945089

namespace Lax945089.Even
end Lax945089.Even
end

-- Lax945089.OrderFreeFirstOrder
section
namespace Lax945089
end Lax945089

namespace Lax945089.OrderFreeFirstOrder
end Lax945089.OrderFreeFirstOrder
end

-- Lax945089.Parity
section
namespace Lax945089
end Lax945089

namespace Lax945089.Parity
end Lax945089.Parity

namespace Lax945089.Parity.markedSetRel
end Lax945089.Parity.markedSetRel

namespace Lax945089.Parity.markedSetRel.mark
end Lax945089.Parity.markedSetRel.mark
end

-- Lax945089.PebbleGames
section
namespace Lax945089.PebbleGames
end Lax945089.PebbleGames

namespace Lax945089.PebbleGames.PebbleRel₂
end Lax945089.PebbleGames.PebbleRel₂

namespace Lax945089.PebbleGames.RelsIn
end Lax945089.PebbleGames.RelsIn

namespace Lax945089.PebbleGames.StepDef
end Lax945089.PebbleGames.StepDef

namespace Lax945089.PebbleGames.blockRelsExtend
end Lax945089.PebbleGames.blockRelsExtend

namespace Lax945089.PebbleGames.pebbleStage₂
end Lax945089.PebbleGames.pebbleStage₂
end

-- Lax945089.TransitiveClosureReductions
section
namespace Lax945089.TransitiveClosureReductions.DTCReduction
end Lax945089.TransitiveClosureReductions.DTCReduction

namespace Lax945089.TransitiveClosureReductions.ParamTCSpec.detVar
end Lax945089.TransitiveClosureReductions.ParamTCSpec.detVar

namespace Lax945089.TransitiveClosureReductions

open Lax904597.Problems Lax904597.Relativized Lax904597.SecondOrder

open Lax535992.InflationaryFixedPoint

open FirstOrder

open Language Structure

/-- A **parameterized transitive-closure specification**: a walk on `k`-tuples
carrying a finite mode, whose step formula may mention `par` parameters beside
the current and the next tuple. It has no source and target formulas: what it
defines is the reachability *relation*. -/
structure ParamTCSpec (L : Language.{0, 0}) : Type 1 where
  /-- The modes: the finite control the walk carries beside its tuple. -/
  Mode : Type
  /-- Modes are finite. -/
  [modeFinite : Finite Mode]
  /-- The walk runs on `k`-tuples of elements. -/
  k : ℕ
  /-- The number of parameters the step formula may mention. -/
  par : ℕ
  /-- The step formula, one per pair of modes: the current tuple, the next
  tuple, then the parameters. -/
  step : Mode → Mode → L.Formula ((Fin k ⊕ Fin k) ⊕ Fin par)

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : ParamTCSpec L) {A : Type} [L.Structure A]

attribute [instance] modeFinite

end ParamTCSpec

/-- A finite family of parameterized walks. Its relation variables – one per
walk and ordered pair of that walk's modes – are what an FO(TC) reduction's
formulas may read. -/
structure TCFamily (L : Language.{0, 0}) : Type 1 where
  /-- The index type of the family. -/
  Ix : Type
  /-- The family is finite. -/
  [ixFinite : Finite Ix]
  /-- The walk of each index. -/
  spec : Ix → ParamTCSpec L

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily L)

attribute [instance] ixFinite

/-- The block of relation variables of a family: one variable per walk and
ordered pair of modes, of arity “two tuples and the parameters”. -/
def block : SOBlock where
  ι := Σ i : F.Ix, (F.spec i).Mode × (F.spec i).Mode
  arity := fun q => (F.spec q.1).k + (F.spec q.1).k + (F.spec q.1).par

variable {F} {A : Type} [L.Structure A]

end TCFamily

open FirstOrder

open Language Structure

/-- An **FO(TC) interpretation**: a relativized first-order interpretation
whose formulas may read the reachability relations of a finite family of
first-order walks over the base structure.

Over an ordered base (`L := L₀.sum Language.order`) this is Immerman's FO(TC)
reduction, the logical form of a logarithmic-space reduction. -/
structure TCInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) : Type 1 where
  /-- The walks whose reachability relations the formulas may read. -/
  fam : TCFamily L
  /-- The interpretation, over the base vocabulary expanded by the walks'
  relation variables. -/
  toRel : RelFOInterpretation (L.sum fam.block.lang) L' Tag dim

namespace TCInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : TCInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end TCInterpretation

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : ParamTCSpec L)

end ParamTCSpec

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily L)

end TCFamily

end Lax945089.TransitiveClosureReductions
end

-- Lax945089.GamesOnLinearOrders
section
namespace Lax945089.GamesOnLinearOrders

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes

open Lax485149.Problems Lax485149.FirstOrderDefinability Lax485149.TransitiveClosure

open Lax485149.DeterministicTransitiveClosure Lax485149.ClassNL Lax485149.ClassL

open Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME

open Lax134656.PartialFixedPoint Lax895169.ArithmeticLogic

open Lax945089.OrderFreeFirstOrder Lax945089.EhrenfeuchtGames Lax945089.PebbleGames

open Lax945089.Even Lax945089.Parity

open Lax945089.TransitiveClosureReductions

/-- Two linear orders with at least `2 ^ n` elements are `n`-round equivalent. -/
axiom efEquiv_linearOrder :
  ∀ {A B : Type} [Language.empty.Structure A] [Language.empty.Structure B] [LinearOrder A]
    [LinearOrder B]
  [Finite A] [Finite B] (n : ℕ), 2 ^ n ≤ Nat.card A → 2 ^ n ≤ Nat.card B →
    EFEquiv (Language.empty.sum Language.order) A B n

end Lax945089.GamesOnLinearOrders
end

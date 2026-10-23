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
namespace Lax945089.EhrenfeuchtGames.efStage
end Lax945089.EhrenfeuchtGames.efStage

namespace Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- The quantifier depth of a bounded formula: the number of pebbles the
invariance argument spends on it. -/
def qdepth {L : Language.{0, 0}} {α : Type*} : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f₁ f₂ => max (qdepth f₁) (qdepth f₂)
  | _, .all f => qdepth f + 1

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
namespace Lax945089.PebbleGames.StepDef
end Lax945089.PebbleGames.StepDef

namespace Lax945089.PebbleGames.blockRelsExtend
end Lax945089.PebbleGames.blockRelsExtend

namespace Lax945089.PebbleGames

open Lax904597.SecondOrder Lax535992.InflationaryFixedPoint Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- The relation symbols of a bounded formula all lie in the family `S`. -/
def RelsIn {L : Language.{0, 0}} (S : Set (Σ n, L.Relations n)) {α : Type*} :
    ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | _, .falsum => True
  | _, .equal _ _ => True
  | _, .rel R _ => ⟨_, R⟩ ∈ S
  | _, .imp f₁ f₂ => RelsIn S f₁ ∧ RelsIn S f₂
  | _, .all f => RelsIn S f

/-- A relation between `k`-tuples of two types: the positions of the
two-structure `k`-pebble game. -/
abbrev PebbleRel₂ (M N : Type) (k : ℕ) : Type :=
  (Fin k → M) → (Fin k → N) → Prop

variable {M N : Type} {k : ℕ}

/-- The back-and-forth condition of the two-structure `k`-pebble game: the
pebble the spoiler moves, on either structure, can be answered on the other. -/
def PebbleBackForth₂ (E : PebbleRel₂ M N k) : PebbleRel₂ M N k :=
  fun a b => ∀ i : Fin k,
    (∀ c : M, ∃ d : N, E (Function.update a i c) (Function.update b i d)) ∧
    (∀ d : N, ∃ c : M, E (Function.update a i c) (Function.update b i d))

/-- One round of refinement. -/
def pebbleRefine₂ (E₀ E : PebbleRel₂ M N k) : PebbleRel₂ M N k :=
  fun a b => E₀ a b ∧ PebbleBackForth₂ E a b

/-- The descending refinement chain. -/
def pebbleStage₂ (E₀ : PebbleRel₂ M N k) : ℕ → PebbleRel₂ M N k
  | 0 => fun _ _ => True
  | n + 1 => pebbleRefine₂ E₀ (pebbleStage₂ E₀ n)

/-- **`k`-pebble equivalence between two structures**: the limit of the
refinement chain. -/
def EquivK₂ (E₀ : PebbleRel₂ M N k) : PebbleRel₂ M N k :=
  fun a b => ∀ n, pebbleStage₂ E₀ n a b

/-- Agreement on the atomic type between tuples of two structures: the same
equalities between coordinates, and the same base relations of the family `S`
at every selection of coordinates. -/
def atomicAgreeOn₂ {L : Language.{0, 0}} (S : Set (Σ n, L.Relations n)) (M N : Type)
    [L.Structure M] [L.Structure N]
    (k : ℕ) : PebbleRel₂ M N k :=
  fun v w =>
    (∀ i j : Fin k, v i = v j ↔ w i = w j) ∧
    ∀ {l : ℕ} (R : L.Relations l), ⟨l, R⟩ ∈ S → ∀ g : Fin l → Fin k,
      ((RelMap R fun p => v (g p)) ↔ RelMap R fun p => w (g p))

end Lax945089.PebbleGames
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

-- Lax945089.PebbleInvariance
section
namespace Lax945089.PebbleInvariance

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

/-- A formula within `k` variables cannot separate `k`-pebble equivalent tuples. -/
axiom realize_equivK₂ :
  ∀ {L : Language.{0, 0}} {M N : Type} {k : ℕ} [L.IsRelational] [L.Structure M] [L.Structure N]
  [Finite M] [Finite N] {S : Set ((n : ℕ) × L.Relations n)} {α : Type} [Fintype α] {n : ℕ}
  (φ : L.BoundedFormula α n) (g : α → Fin k) (h : Fin n → Fin k), Function.Injective h →
  (∀ (i : α) (j : Fin n), g i ≠ h j) →
  (Finset.image g Finset.univ ∪ Finset.image h Finset.univ).card + qdepth φ ≤ k →
  RelsIn S φ → ∀ (v : Fin k → M) (w : Fin k → N), EquivK₂ (atomicAgreeOn₂ S M N k) v w →
    ((φ.Realize (fun i => v (g i)) fun j => v (h j)) ↔
      φ.Realize (fun i => w (g i)) fun j => w (h j))

end Lax945089.PebbleInvariance
end

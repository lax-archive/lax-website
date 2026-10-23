-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Order.Basic

-- Lax904597.Problems
section
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

instance instCoeFun : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

end DecisionProblem

end Lax904597.Problems
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

/-- The universe of the structure interpreted in `A`: tagged `dim`-tuples. -/
protected def Map (_I : FOInterpretation L L' Tag dim) (A : Type) : Type :=
  Tag × (Fin dim → A)

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The `L'`-structure interpreted in the `L`-structure `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2

end FOInterpretation

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

instance sumOrderOrderedStructure : (L.sum Language.order).OrderedStructure A :=
  ⟨fun _ => Iff.rfl⟩

end Ordered

end Lax904597.Interpretations
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

/-- The universe of the relativized interpretation in `A`: the tagged tuples
whose coordinates satisfy their tag's domain formula. -/
protected def MapRel : Type :=
  {x : Tag × (Fin dim → A) // (I.domFormula x.1).Realize x.2}

/-- The `L'`-structure interpreted on the definable subset. -/
instance mapRelStructure [L'.IsRelational] : L'.Structure (I.MapRel A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2

end RelFOInterpretation

end Lax904597.Relativized
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

instance instIsRelationalLang (B : SOBlock) : IsRelational B.lang :=
  fun _ => ⟨fun f => Empty.elim f⟩

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

-- Lax535992.LeastFixedPoint
section
namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax535992.LeastFixedPoint.Derives
end Lax535992.LeastFixedPoint.Derives

namespace Lax535992.LeastFixedPoint.LFPDef
end Lax535992.LeastFixedPoint.LFPDef
end

-- Lax895169.BitPredicate
section
namespace Lax895169.BitPredicate

/-- The rank of an element of a finite linear order: the number of its strict
predecessors. -/
noncomputable def orank {A : Type} [LinearOrder A] (z : A) : ℕ :=
  {y : A | y < z}.ncard

/-- **The number of bit positions** of the ranks of `A`: the ranks are the
numbers below `Nat.card A`, so they are exactly the numbers whose bits live
below `Nat.clog 2 (Nat.card A)`. -/
noncomputable def posCount (A : Type) [LinearOrder A] [Finite A] : ℕ :=
  Nat.clog 2 (Nat.card A)

/-- **The bit of `x` at the index `i`**: the `BIT` of the classical vocabulary
`FO(≤, BIT)`, the position being named by the element whose *rank* is the
exponent. Total, and with no guard – above the bit positions of the universe
every bit is simply clear. -/
def BitIx {A : Type} [LinearOrder A] (i x : A) : Prop :=
  (orank x).testBit (orank i) = true

/-- A quantifier prefix, peeled from the innermost variable outwards: the
variable of index `0` is quantified outermost, existentially when its polarity
is `true`. -/
def prefixHolds {A : Type} : (m : ℕ) → (Fin m → Bool) → ((Fin m → A) → Prop) → Prop
  | 0, _, P => P Fin.elim0
  | m + 1, pol, P =>
      prefixHolds m (fun j => pol j.castSucc)
        (fun v => if pol (Fin.last m) = true then ∃ a, P (Fin.snoc v a)
          else ∀ a, P (Fin.snoc v a))

end Lax895169.BitPredicate
end

-- Lax895169.ArithmeticLogic
section
namespace Lax895169.ArithmeticLogic

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the arithmetic vocabulary. -/
inductive arithRel : ℕ → Type
  /-- `le x y`: the rank of `x` is at most the rank of `y`, i.e., `x ≤ y`. -/
  | le : arithRel 2
  /-- `plus x y z`: the ranks satisfy `orank x + orank y = orank z`. -/
  | plus : arithRel 3
  /-- `times x y z`: the ranks satisfy `orank x * orank y = orank z`. -/
  | times : arithRel 3
  deriving DecidableEq

/-- The relational vocabulary of the numeric predicates: a linear order and the
graphs of addition and multiplication of ranks. Interpreted canonically on every
finite linear order by `arithStructure`. -/
def arith : Language :=
  ⟨fun _ => Empty, arithRel⟩

instance instIsRelationalArith : IsRelational arith := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Structures

variable (A : Type) [LinearOrder A] [Finite A]

/-- **The numeric predicates of a finite linear order**: `≤` is the order, and
`plus`/`times` are the graphs of addition and multiplication of ranks. Both are
truncated: a value that is not the rank of an element of `A` is not related to
anything. -/
instance arithStructure : arith.Structure A where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .le => fun x => x 0 ≤ x 1
    | _, .plus => fun x => orank (x 0) + orank (x 1) = orank (x 2)
    | _, .times => fun x => orank (x 0) * orank (x 1) = orank (x 2)

end Structures

open FirstOrder

open Language

end Lax895169.ArithmeticLogic
end

-- Lax895169.BitLogic
section
namespace Lax895169.BitLogic

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open Language Structure

/-- The atoms of the bit-level logic: the order, the addition of ranks, the bit
of an element at an index, and an input relation at a tuple of variables. -/
inductive BitAtom (L : Language.{0, 0}) (γ : Type) where
  /-- `x ≤ y`. -/
  | le (x y : γ) : BitAtom L γ
  /-- `orank x + orank y = orank z`. -/
  | plus (x y z : γ) : BitAtom L γ
  /-- The bit of `x` at the index `i` is set. -/
  | bit (i x : γ) : BitAtom L γ
  /-- An input relation at a tuple of variables. -/
  | rel {a : ℕ} (R : L.Relations a) (arg : Fin a → γ) : BitAtom L γ

/-- A quantifier-free kernel over the bit-level atoms. -/
inductive BitKernel (L : Language.{0, 0}) (γ : Type) where
  /-- An atom. -/
  | atom (a : BitAtom L γ) : BitKernel L γ
  /-- The constant `true`, so that a trivial relation needs no dummy variable. -/
  | tt : BitKernel L γ
  /-- Negation. -/
  | not (k : BitKernel L γ) : BitKernel L γ
  /-- Conjunction. -/
  | and (k k' : BitKernel L γ) : BitKernel L γ
  /-- Disjunction. -/
  | or (k k' : BitKernel L γ) : BitKernel L γ

/-- **A sentence of the bit-level logic, in prenex form**: a polarity per
variable and a quantifier-free kernel. -/
structure BitSentence (L : Language.{0, 0}) where
  /-- The number of quantified variables. -/
  vars : ℕ
  /-- The quantifier at each variable: `true` existential, `false` universal. -/
  pol : Fin vars → Bool
  /-- The quantifier-free kernel. -/
  kernel : BitKernel L (Fin vars)

namespace BitAtom

variable {L : Language.{0, 0}} {γ : Type}

/-- What an atom says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitAtom L γ → (γ → A) → Prop
  | .le x y, v => v x ≤ v y
  | .plus x y z, v => orank (v x) + orank (v y) = orank (v z)
  | .bit i x, v => BitIx (v i) (v x)
  | .rel R arg, v => RelMap R fun t => v (arg t)

end BitAtom

namespace BitKernel

variable {L : Language.{0, 0}} {γ : Type}

/-- What a kernel says of a valuation. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BitKernel L γ → (γ → A) → Prop
  | .atom a, v => a.Holds v
  | .tt, _ => True
  | .not k, v => ¬ k.Holds v
  | .and k k', v => k.Holds v ∧ k'.Holds v
  | .or k k', v => k.Holds v ∨ k'.Holds v

end BitKernel

namespace BitSentence

/-- What a sentence says of an instance: the prefix, played over the kernel. -/
def Holds {L : Language.{0, 0}} (φ : BitSentence L) (A : Type) [L.Structure A] [LinearOrder A]
    [Finite A] : Prop :=
  prefixHolds (A := A) φ.vars φ.pol fun v => φ.kernel.Holds v

end BitSentence

/-- A decision problem is **bit-definable** when a prenex sentence over the
order, the addition and the bit at an index – `FO(≤, +, BIT)` – decides it on
every nonempty finite ordered structure. -/
def BitDefinable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ φ : BitSentence L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ φ.Holds A

end Lax895169.BitLogic
end

-- Lax895169.LogTimeMachines
section
namespace Lax895169.LogTimeMachines

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open Language Structure

/-- A Boolean expression over bit variables: what a sweep computes in one step,
and what its acceptance condition is. Expressions rather than functions, so that
the translation into a formula is a recursion rather than an enumeration of a
truth table. -/
inductive BitExpr (V : Type) where
  /-- A bit variable. -/
  | var (v : V) : BitExpr V
  /-- The constant `true`. -/
  | tt : BitExpr V
  /-- The constant `false`. -/
  | ff : BitExpr V
  /-- Negation. -/
  | not (e : BitExpr V) : BitExpr V
  /-- Conjunction. -/
  | and (e f : BitExpr V) : BitExpr V
  /-- Disjunction. -/
  | or (e f : BitExpr V) : BitExpr V

namespace BitExpr

variable {V : Type}

/-- The value of an expression under a `Bool`-valued assignment. -/
def eval (val : V → Bool) : BitExpr V → Bool
  | .var v => val v
  | .tt => true
  | .ff => false
  | .not e => !(e.eval val)
  | .and e f => e.eval val && f.eval val
  | .or e f => e.eval val || f.eval val

end BitExpr

/-- A **sweep**: one pass over the bit positions of the universe, from the
lowest to the highest, by a finite automaton with `σ` state bits reading, at
each position, one bit of each of the `ρ` registers. -/
structure Sweep (ρ : ℕ) where
  /-- The number of state bits. -/
  σ : ℕ
  /-- The state before the lowest position. -/
  init : Fin σ → Bool
  /-- The next state: one Boolean expression per state bit, over the old state
  and the register bits at the current position. -/
  step : Fin σ → BitExpr (Fin σ ⊕ Fin ρ)
  /-- The acceptance condition, read from the state after the last position. -/
  acc : BitExpr (Fin σ)

namespace Sweep

variable {ρ : ℕ} {A : Type} [LinearOrder A] [Finite A]

/-- **The state of a sweep before position `i`**: the automaton starts in its
initial state and takes one step per position, reading the bits of the
registers there. -/
noncomputable def state (S : Sweep ρ) (x : Fin ρ → A) : ℕ → (Fin S.σ → Bool)
  | 0 => S.init
  | i + 1 => fun j => (S.step j).eval
      (Sum.elim (state S x i) fun k => (orank (x k)).testBit i)

/-- **A sweep accepts** when its acceptance condition holds of the state left
after the last bit position. -/
def Accepts (S : Sweep ρ) (x : Fin ρ → A) : Prop :=
  S.acc.eval (S.state x (posCount A)) = true

end Sweep

/-- The **deterministic base** of a machine: a Boolean combination of sweeps and
of queries to the instance. Its cost is a constant number of passes over the bit
positions, hence `O(log n)` steps; nothing here evaluates a numeric predicate. -/
inductive BaseTest (L : Language.{0, 0}) (ρ : ℕ) where
  /-- Run a sweep on the registers. -/
  | sweep (S : Sweep ρ) : BaseTest L ρ
  /-- Read a bit: the bit of register `x` at the position named by register
  `i`. The addressing the model has over its own registers, and the one base
  operation that is not a pass over the positions. -/
  | bit (i x : Fin ρ) : BaseTest L ρ
  /-- Query the instance: an input relation at a tuple of registers. -/
  | query {a : ℕ} (R : L.Relations a) (arg : Fin a → Fin ρ) : BaseTest L ρ
  /-- Negation. -/
  | not (t : BaseTest L ρ) : BaseTest L ρ
  /-- Conjunction. -/
  | and (t u : BaseTest L ρ) : BaseTest L ρ
  /-- Disjunction. -/
  | or (t u : BaseTest L ρ) : BaseTest L ρ

namespace BaseTest

variable {L : Language.{0, 0}} {ρ : ℕ}

/-- What a base test says of a tuple of register values. -/
def Holds {A : Type} [L.Structure A] [LinearOrder A] [Finite A] :
    BaseTest L ρ → (Fin ρ → A) → Prop
  | .sweep S, x => S.Accepts x
  | .bit i y, x => BitIx (x i) (x y)
  | .query R arg, x => RelMap R fun t => x (arg t)
  | .not t, x => ¬ t.Holds x
  | .and t u, x => t.Holds x ∧ u.Holds x
  | .or t u, x => t.Holds x ∨ u.Holds x

end BaseTest

/-- **An alternating machine with a logarithmic clock**: a list of registers,
each filled by one of the two players, and a deterministic bit-level test of the
tuple they leave behind. Registers are filled in order, `pol i` telling which
player fills the `i`-th; the number of alternations is the number of changes
of polarity along the list. -/
structure LTMachine (L : Language.{0, 0}) where
  /-- The number of registers, that is, of guessed addresses. -/
  regs : ℕ
  /-- Who fills each register: `true` existentially, `false` universally. -/
  pol : Fin regs → Bool
  /-- The deterministic base test. -/
  base : BaseTest L regs

/-- **The machine accepts** the instance when the two players, filling the
registers in order, leave a tuple passing the base test. -/
def LTMachine.Accepts {L : Language.{0, 0}} (M : LTMachine L) (A : Type) [L.Structure A]
    [LinearOrder A] [Finite A] : Prop :=
  prefixHolds (A := A) M.regs M.pol fun x => M.base.Holds x

/-- A problem is decidable in *constant-alternation logarithmic time* when one
machine decides it on every nonempty finite ordered structure. -/
def LTDecidable {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ M : LTMachine L, ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ M.Accepts A

end Lax895169.LogTimeMachines
end

-- Lax895169.ACZeroIsLogTime
section
namespace Lax895169.ACZeroIsLogTime

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Classes

open Lax485149.Complement Lax485149.FirstOrderDefinability Lax485149.DeterministicTransitiveClosure

open Lax485149.ClassNL Lax485149.ClassL

open Lax535992.LeastFixedPoint Lax535992.InflationaryFixedPoint Lax535992.ClassPTIME

open Lax895169.BitPredicate Lax895169.ArithmeticLogic Lax895169.BitLogic Lax895169.LogTimeMachines

/-- Every bit-definable problem is decidable in logarithmic time. -/
axiom bitDefinable_ltDecidable : ∀ {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L},
  BitDefinable P → LTDecidable P

end Lax895169.ACZeroIsLogTime
end

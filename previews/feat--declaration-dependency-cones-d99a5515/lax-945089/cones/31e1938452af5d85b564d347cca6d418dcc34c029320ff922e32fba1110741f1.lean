-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics

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

/-- An assignment of actual relations on a universe `A` to the relation
variables of a block. -/
def SOBlock.Assignment (B : SOBlock) (A : Type) : Type :=
  ∀ i : B.ι, (Fin (B.arity i) → A) → Prop

/-- The structure over the block's vocabulary determined by an assignment. -/
@[reducible]
def SOBlock.structure (B : SOBlock) {A : Type} (ρ : B.Assignment A) :
    B.lang.Structure A where
  funMap f := isEmptyElim f
  RelMap := fun {_} r x => ρ r.1 fun j => x (Fin.cast r.2 j)

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax535992.InflationaryFixedPoint
section
namespace Lax535992.InflationaryFixedPoint

open Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- The structure over `L` expanded by one copy of a block's vocabulary,
interpreted by an assignment. -/
@[reducible]
def SOBlock.structure₁ {L : Language.{0, 0}} (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ : B.Assignment A) : (L.sum B.lang).Structure A :=
  @sumStructure L B.lang A inst (B.structure ρ)

/-- A simultaneous first-order induction: a block of relation variables, one
first-order step formula per variable – over the base vocabulary expanded by
the block, its free variables the arguments of the variable – and an output
sentence over the same expanded vocabulary, read at the value of the
iteration. The step formulas are *unrestricted*. -/
structure StepDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the iteration. -/
  B : SOBlock
  /-- The step formula of each variable; its free variables are the arguments
  of the variable. -/
  step : ∀ i : B.ι, (L.sum B.lang).Formula (Fin (B.arity i))
  /-- The first-order output, over the expanded vocabulary – unrestricted, in
  particular free to negate fixed-point atoms. -/
  out : (L.sum B.lang).Sentence

namespace StepDef

variable {L : Language.{0, 0}} (d : StepDef L)

section Semantics

variable {A : Type} [L.Structure A]

end Semantics

end StepDef

end Lax535992.InflationaryFixedPoint
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

-- Lax945089.TransitiveClosureReductions
section
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

variable (A) in
/-- A node of the walk: a mode together with a `k`-tuple. -/
abbrev Node : Type := s.Mode × (Fin s.k → A)

/-- One step of the walk, at a valuation of the parameters. -/
def StepAt (z : Fin s.par → A) (a b : s.Node A) : Prop :=
  (s.step a.1 b.1).Realize (Sum.elim (Sum.elim a.2 b.2) z)

/-- Reachability in the walk, at a valuation of the parameters. -/
abbrev ReachAt (z : Fin s.par → A) : s.Node A → s.Node A → Prop :=
  Relation.ReflTransGen (s.StepAt z)

/-- The position of the `i`-th coordinate of the *first* tuple. -/
def leftIx (i : Fin s.k) : Fin (s.k + s.k + s.par) := ⟨i, by have := i.isLt; omega⟩

/-- The position of the `i`-th coordinate of the *second* tuple. -/
def rightIx (i : Fin s.k) : Fin (s.k + s.k + s.par) := ⟨s.k + i, by have := i.isLt; omega⟩

/-- The position of the `j`-th parameter. -/
def parIx (j : Fin s.par) : Fin (s.k + s.k + s.par) := ⟨s.k + s.k + j, by have := j.isLt; omega⟩

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

/-- The assignment the block *has*, as opposed to one a second-order
quantifier would guess: each variable holds the reachability relation of its
walk, at the parameters read off the tuple. -/
def reachAssign (F : TCFamily L) (A : Type) [L.Structure A] : F.block.Assignment A :=
  fun q w =>
    (F.spec q.1).ReachAt (fun j => w ((F.spec q.1).parIx j))
      (q.2.1, fun i => w ((F.spec q.1).leftIx i))
      (q.2.2, fun i => w ((F.spec q.1).rightIx i))

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

/-- The base structure expanded by the reachability relations of the walks –
the structure the interpretation is read over. -/
@[reducible]
def expStructure : (L.sum I.fam.block.lang).Structure A :=
  SOBlock.structure₁ (L := L) I.fam.block (I.fam.reachAssign A)

/-- The universe of the interpreted structure. -/
def Map : Type :=
  letI := I.expStructure A
  I.toRel.MapRel A

/-- The `L'`-structure interpreted in `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) :=
  letI := I.expStructure A
  RelFOInterpretation.mapRelStructure I.toRel A

end TCInterpretation

open FirstOrder

open Language Structure

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : ParamTCSpec L)

/-- The renaming used by the uniqueness clause: the step formula is re-read
with its first tuple still the current one, its second tuple the freshly
quantified `w̄`, and its parameters unchanged. -/
def detVar : ((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) → (((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) ⊕ Fin s.k)
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (Sum.inl i))
  | Sum.inl (Sum.inr i) => Sum.inr i
  | Sum.inr j => Sum.inl (Sum.inr j)

open Classical in
/-- **The determinized step formula** at a pair of modes: this step, and no
other step out of the current node. As in
`TCSpec.detStep`, the competing successor's mode is
compared statically, so the uniqueness clause has one conjunct per mode. -/
noncomputable def detStep (m n : s.Mode) : L.Formula ((Fin s.k ⊕ Fin s.k) ⊕ Fin s.par) :=
  s.step m n ⊓
    Formula.iInf fun m' : s.Mode =>
      Formula.iAlls (Fin s.k)
        (((s.step m m').relabel s.detVar).imp
          (if m' = n then
            Formula.iInf fun i : Fin s.k =>
              Term.equal (Term.var (Sum.inr i)) (Term.var (Sum.inl (Sum.inl (Sum.inr i))))
          else ⊥))

/-- **The deterministic reading of a walk**: the same modes, arity and
parameters, with the step formula replaced by its determinization.

Reducible, so that the modes, the arity, and the parameter count of `s.det` are
those of `s` transparently – a node of the deterministic reading *is* a node,
and the block of a determinized family *is* the block of the family. -/
@[reducible]
noncomputable def det : ParamTCSpec L where
  Mode := s.Mode
  k := s.k
  par := s.par
  step := s.detStep

end ParamTCSpec

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily L)

/-- The deterministic reading of a family: every walk read through its
determinization. Reducible, so that `F.det.block` *is* `F.block`. -/
@[reducible]
noncomputable def det : TCFamily L where
  Ix := F.Ix
  spec := fun i => (F.spec i).det

end TCFamily

/-- An **FO(DTC) reduction** from `P` to `Q` – a deterministic
logarithmic-space reduction, in the logical form of Immerman: an interpretation over the ordered
expansion whose formulas may read the reachability relations of a family of
walks, each read through its determinization. -/
structure DTCReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L)
    (Q : DecisionProblem L') : Type 1 where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The walks the formulas may read – *before* determinization, which is how
  they are read. -/
  fam : TCFamily (L.sum Language.order)
  /-- The interpretation, over the base expanded by the walks' relation
  variables. -/
  toRel : RelFOInterpretation ((L.sum Language.order).sum fam.block.lang) L' Tag dim
  /-- The interpreted structure is nonempty on nonempty finite ordered
  inputs. -/
  map_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    Nonempty (TCInterpretation.Map ⟨fam.det, toRel⟩ A)
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (TCInterpretation.Map ⟨fam.det, toRel⟩ A)

end Lax945089.TransitiveClosureReductions
end

-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
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

-- Lax535992.ClassPTIME
section
namespace Lax535992.ClassPTIME
end Lax535992.ClassPTIME
end

-- Lax904597.Machines
section
namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

variable {A : Type}

/-- A binary relation is a linear order: reflexive, transitive, antisymmetric
and total. -/
def IsLinOrd (Le : A → A → Prop) : Prop :=
  (∀ a, Le a a) ∧ (∀ a b c, Le a b → Le b c → Le a c) ∧
    (∀ a b, Le a b → Le b a → a = b) ∧ ∀ a b, Le a b ∨ Le b a

/-- `p` is a lowest position. -/
def MinPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le p q

/-- `q` is the next position above `p`. -/
def SuccPos (Le : A → A → Prop) (Posn : A → Prop) (p q : A) : Prop :=
  Posn p ∧ Posn q ∧ Le p q ∧ p ≠ q ∧ ∀ r, Posn r → Le p r → Le r q → r = p ∨ r = q

/-- A configuration: the current state, the position of the head, and the
contents of the tape. -/
@[ext]
structure Config (A : Type) where
  /-- The current state. -/
  state : A
  /-- The cell the head is on. -/
  head : A
  /-- The symbol in each cell. -/
  tape : A → A

/-- A Turing machine presented as relations on a universe: the sorts, the
marks, the attributes of the transitions, the initial tape and the order along
which the head moves. -/
structure TMData (A : Type) where
  /-- Being a position – a tape cell, and equally a time step. -/
  Posn : A → Prop
  /-- The order on positions, along which the head moves. -/
  Le : A → A → Prop
  /-- Being a transition. -/
  Tr : A → Prop
  /-- Being a start state. -/
  Start : A → Prop
  /-- Being an accepting state. -/
  Acc : A → Prop
  /-- Being the blank symbol. -/
  Blank : A → Prop
  /-- This transition moves the head right (rather than left). -/
  Right : A → Prop
  /-- The state a transition applies in. -/
  Src : A → A → Prop
  /-- The symbol a transition reads. -/
  Read : A → A → Prop
  /-- The state a transition moves to. -/
  Dst : A → A → Prop
  /-- The symbol a transition writes. -/
  Write : A → A → Prop
  /-- The input: the symbol initially in a cell. -/
  Inp : A → A → Prop

namespace TMData

variable (M : TMData A)

/-- The symbols a cell may initially hold: the input symbol where the input is
defined, the blank elsewhere. -/
def InitTape (p a : A) : Prop := M.Inp p a ∨ ((∀ b, ¬ M.Inp p b) ∧ M.Blank a)

/-- Being an initial configuration: a start state, the head on the lowest
position, and an initial tape. -/
def IsInit (c : Config A) : Prop :=
  M.Start c.state ∧ MinPos M.Le M.Posn c.head ∧ ∀ p, M.InitTape p (c.tape p)

/-- One step: some transition applies in the current state to the symbol under
the head; it writes in that cell, changes state, and moves the head to the
neighboring position in the direction it names. Other cells are unchanged,
and a move off the end of the tape is impossible, so the run stops there. -/
def Step (c c' : Config A) : Prop :=
  ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
    M.Dst τ c'.state ∧ M.Write τ (c'.tape c.head) ∧
    (∀ p, p ≠ c.head → c'.tape p = c.tape p) ∧
    ((M.Right τ ∧ SuccPos M.Le M.Posn c.head c'.head) ∨
      (¬ M.Right τ ∧ SuccPos M.Le M.Posn c'.head c.head))

/-- Well-formedness: the order is linear, there is a position to start on, the
input is functional, and there is exactly one blank symbol. -/
def WellFormed : Prop :=
  IsLinOrd M.Le ∧ (∃ p, M.Posn p) ∧
    (∀ p a b, M.Inp p a → M.Inp p b → a = b) ∧
    (∃ b, M.Blank b) ∧ (∀ a b, M.Blank a → M.Blank b → a = b)

end TMData

/-- Relation symbols of machine instances. -/
inductive turingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a tape cell, and equally a time step. -/
  | posn : turingRel 1
  /-- `tr τ`: `τ` is a transition. -/
  | tr : turingRel 1
  /-- `start q`: `q` is a start state. -/
  | start : turingRel 1
  /-- `acc q`: `q` is an accepting state. -/
  | acc : turingRel 1
  /-- `blank a`: `a` is the blank symbol. -/
  | blank : turingRel 1
  /-- `right τ`: the transition `τ` moves the head right. -/
  | right : turingRel 1
  /-- `le p q`: the linear order along which the head moves. -/
  | le : turingRel 2
  /-- `tsrc τ q`: `τ` applies in the state `q`. -/
  | tsrc : turingRel 2
  /-- `tread τ a`: `τ` applies when reading the symbol `a`. -/
  | tread : turingRel 2
  /-- `tdst τ q`: `τ` moves to the state `q`. -/
  | tdst : turingRel 2
  /-- `twrite τ a`: `τ` writes the symbol `a`. -/
  | twrite : turingRel 2
  /-- `inp p a`: the cell `p` initially holds the symbol `a`. -/
  | inp : turingRel 2
  deriving DecidableEq

/-- The relational language of machine instances: positions with their order,
transitions with their attributes, the distinguished states and symbol, and the
initial tape. -/
def turing : Language :=
  ⟨fun _ => Empty, turingRel⟩

section Shorthands

variable [turing.Structure A]

end Shorthands

end Lax904597.Machines
end

-- Lax564036.AlternatingMachines
section
namespace Lax564036.AlternatingMachines

open Lax904597.Problems Lax485149.Problems

open Lax904597.Machines

/-- An alternating Turing machine presented as relations on a universe: a
machine in the sense of `TMData`, together with marks
splitting its states into quantifier blocks. -/
structure ATMData (A : Type) extends TMData A where
  /-- `Blk j q`: the state `q` belongs to the `j`-th quantifier block. -/
  Blk : ℕ → A → Prop

/-- The polarity of the `j`-th quantifier block of a prefix starting with
polarity `start`: `true` for an existential block, `false` for a universal one.
The polarities alternate, so the parity of `j` decides. -/
def blockPol (start : Bool) (j : ℕ) : Bool :=
  if j % 2 = 0 then start else !start

/-- **Quantification with a polarity, guarded.** Existentially, the guard is
conjoined; universally it is assumed – and required to be satisfiable by
*something*: a universal player with no legal move loses rather than winning
vacuously. -/
def guardQ (pol : Bool) {α : Type} (C P : α → Prop) : Prop :=
  match pol with
  | true => ∃ a, C a ∧ P a
  | false => (∃ a, C a) ∧ ∀ a, C a → P a

namespace ATMData

variable {A : Type} (M : ATMData A)

/-- The state `q` is *universal*: it carries the mark of a block whose
polarity is universal, so the moves out of it belong to the universal
player. -/
def IsUniv (start : Bool) (q : A) : Prop := ∃ j, M.Blk j q ∧ blockPol start j = false

/-- **Alternating acceptance within a budget.** `M.AltAcc start n c` says the
configuration `c` accepts with `n` steps to spare: an accepting state accepts
outright, an existential configuration accepts when *some* successor does, and
a universal one when it has a successor and *every* successor accepts. -/
def AltAcc (start : Bool) : ℕ → Config A → Prop
  | 0, c => M.Acc c.state
  | n + 1, c => M.Acc c.state ∨
      (M.IsUniv start c.state ∧ (∃ c', M.Step c c') ∧
        ∀ c', M.Step c c' → AltAcc start n c') ∨
      (¬ M.IsUniv start c.state ∧ ∃ c', M.Step c c' ∧ AltAcc start n c')

/-- **Alternating acceptance**: an initial configuration accepts within as many
steps as there are positions – chosen by the player of block `0`, which is what
`guardQ` at the polarity `start` says: the residual freedom in the initial
configuration belongs to the same player as the first move. -/
def AltAccepts (start : Bool) : Prop :=
  guardQ start (fun c₀ : Config A => M.IsInit c₀)
    (fun c₀ => M.AltAcc start (Nat.card {p : A // M.Posn p} - 1) c₀)

/-- **The block structure is well formed**: every state carries exactly one of
the `k` block marks, every transition either stays in its block or moves to
the next one, and the run starts in block `0`. The second clause is what bounds
the number of alternations by `k - 1`. -/
def BlocksWellFormed (k : ℕ) : Prop :=
  (∀ q, ∃ j, j < k ∧ M.Blk j q ∧ ∀ j', M.Blk j' q → j' = j) ∧
    (∀ τ q q' j j', M.Tr τ → M.Src τ q → M.Dst τ q' → M.Blk j q → M.Blk j' q' →
      j ≤ j' ∧ j' ≤ j + 1) ∧
    ∀ q, M.Start q → M.Blk 0 q

end ATMData

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of alternating machine instances: those of machine
instances, and one unary mark per quantifier block. -/
inductive turingAltRel (k : ℕ) : ℕ → Type
  /-- A symbol of the underlying machine vocabulary. -/
  | base {n : ℕ} : turingRel n → turingAltRel k n
  /-- `blk i q`: the state `q` belongs to the `i`-th quantifier block. -/
  | blk : Fin k → turingAltRel k 1

/-- The relational vocabulary of alternating machine instances with `k`
quantifier blocks. -/
def turingAlt (k : ℕ) : Language :=
  ⟨fun _ => Empty, turingAltRel k⟩

variable {k : ℕ}

/-- The position symbol. -/
abbrev atmPosn : (turingAlt k).Relations 1 := .base .posn

/-- The transition symbol. -/
abbrev atmTr : (turingAlt k).Relations 1 := .base .tr

/-- The start-state symbol. -/
abbrev atmStart : (turingAlt k).Relations 1 := .base .start

/-- The accepting-state symbol. -/
abbrev atmAcc : (turingAlt k).Relations 1 := .base .acc

/-- The blank symbol. -/
abbrev atmBlank : (turingAlt k).Relations 1 := .base .blank

/-- The move-right symbol. -/
abbrev atmRight : (turingAlt k).Relations 1 := .base .right

/-- The order symbol. -/
abbrev atmLe : (turingAlt k).Relations 2 := .base .le

/-- The transition-source symbol. -/
abbrev atmSrc : (turingAlt k).Relations 2 := .base .tsrc

/-- The transition-read symbol. -/
abbrev atmRead : (turingAlt k).Relations 2 := .base .tread

/-- The transition-destination symbol. -/
abbrev atmDst : (turingAlt k).Relations 2 := .base .tdst

/-- The transition-write symbol. -/
abbrev atmWrite : (turingAlt k).Relations 2 := .base .twrite

/-- The input symbol. -/
abbrev atmInp : (turingAlt k).Relations 2 := .base .inp

/-- The mark of the `i`-th quantifier block. -/
abbrev atmBlk (i : Fin k) : (turingAlt k).Relations 1 := .blk i

open FirstOrder

open Language Structure

section Shorthands

variable {k : ℕ} {A : Type} [(turingAlt k).Structure A]

/-- Being a position. -/
def ATMPosn (a : A) : Prop := RelMap (atmPosn (k := k)) ![a]

/-- Being a transition. -/
def ATMTr (a : A) : Prop := RelMap (atmTr (k := k)) ![a]

/-- Being a start state. -/
def ATMStart (a : A) : Prop := RelMap (atmStart (k := k)) ![a]

/-- Being an accepting state. -/
def ATMAcc (a : A) : Prop := RelMap (atmAcc (k := k)) ![a]

/-- Being the blank symbol. -/
def ATMBlank (a : A) : Prop := RelMap (atmBlank (k := k)) ![a]

/-- Moving the head right. -/
def ATMRight (a : A) : Prop := RelMap (atmRight (k := k)) ![a]

/-- The order on positions. -/
def ATMLe (a b : A) : Prop := RelMap (atmLe (k := k)) ![a, b]

/-- The state a transition applies in. -/
def ATMSrc (a b : A) : Prop := RelMap (atmSrc (k := k)) ![a, b]

/-- The symbol a transition reads. -/
def ATMRead (a b : A) : Prop := RelMap (atmRead (k := k)) ![a, b]

/-- The state a transition moves to. -/
def ATMDst (a b : A) : Prop := RelMap (atmDst (k := k)) ![a, b]

/-- The symbol a transition writes. -/
def ATMWrite (a b : A) : Prop := RelMap (atmWrite (k := k)) ![a, b]

/-- The initial contents of a cell. -/
def ATMInp (a b : A) : Prop := RelMap (atmInp (k := k)) ![a, b]

/-- The block of a state, read off the marks: the marks of the vocabulary are
indexed by `Fin k`, so a block index beyond `k` marks nothing. -/
def ATMBlk (j : ℕ) (a : A) : Prop := ∃ h : j < k, RelMap (atmBlk (⟨j, h⟩ : Fin k)) ![a]

/-- The alternating machine an instance describes. -/
def atmData (k : ℕ) (A : Type) [(turingAlt k).Structure A] : ATMData A where
  Posn := ATMPosn (k := k)
  Le := ATMLe (k := k)
  Tr := ATMTr (k := k)
  Start := ATMStart (k := k)
  Acc := ATMAcc (k := k)
  Blank := ATMBlank (k := k)
  Right := ATMRight (k := k)
  Src := ATMSrc (k := k)
  Read := ATMRead (k := k)
  Dst := ATMDst (k := k)
  Write := ATMWrite (k := k)
  Inp := ATMInp (k := k)
  Blk := ATMBlk (k := k)

end Shorthands

/-- The instance describes a well-formed alternating machine, with well-formed
blocks, that accepts its input. -/
def ATMAccepts (k : ℕ) (start : Bool) (A : Type) [(turingAlt k).Structure A] : Prop :=
  (atmData k A).toTMData.WellFormed ∧ ATMData.BlocksWellFormed (atmData k A) k ∧
    ATMData.AltAccepts (atmData k A) start

end Lax564036.AlternatingMachines
end

-- Lax564036.Difference
section
namespace Lax564036
end Lax564036

namespace Lax564036.Difference
end Lax564036.Difference
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

-- Lax564036.QuantifiedBooleanFormulas
section
namespace Lax564036
end Lax564036

namespace Lax564036.QuantifiedBooleanFormulas
end Lax564036.QuantifiedBooleanFormulas

namespace Lax564036.QuantifiedBooleanFormulas.QbfMatrix
end Lax564036.QuantifiedBooleanFormulas.QbfMatrix

namespace Lax564036.QuantifiedBooleanFormulas.altQuant
end Lax564036.QuantifiedBooleanFormulas.altQuant

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel
end Lax564036.QuantifiedBooleanFormulas.qbfRel

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel.block
end Lax564036.QuantifiedBooleanFormulas.qbfRel.block

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel.isClause
end Lax564036.QuantifiedBooleanFormulas.qbfRel.isClause

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel.negIn
end Lax564036.QuantifiedBooleanFormulas.qbfRel.negIn

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel.posIn
end Lax564036.QuantifiedBooleanFormulas.qbfRel.posIn
end

-- Lax564036.SatUnsat
section
namespace Lax564036
end Lax564036

namespace Lax564036.SatUnsat
end Lax564036.SatUnsat

namespace Lax564036.SatUnsat.satPairRel
end Lax564036.SatUnsat.satPairRel

namespace Lax564036.SatUnsat.satPairRel.isClause₁
end Lax564036.SatUnsat.satPairRel.isClause₁

namespace Lax564036.SatUnsat.satPairRel.isClause₂
end Lax564036.SatUnsat.satPairRel.isClause₂

namespace Lax564036.SatUnsat.satPairRel.negIn₁
end Lax564036.SatUnsat.satPairRel.negIn₁

namespace Lax564036.SatUnsat.satPairRel.negIn₂
end Lax564036.SatUnsat.satPairRel.negIn₂

namespace Lax564036.SatUnsat.satPairRel.posIn₁
end Lax564036.SatUnsat.satPairRel.posIn₁

namespace Lax564036.SatUnsat.satPairRel.posIn₂
end Lax564036.SatUnsat.satPairRel.posIn₂
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

-- Lax564036.Tautology
section
namespace Lax564036
end Lax564036

namespace Lax564036.Tautology
end Lax564036.Tautology
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

-- Lax799700.Common
section
namespace Lax799700.Common
end Lax799700.Common

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc
end

-- Lax799700.ThreeSat
section
namespace Lax799700.ThreeSat
end Lax799700.ThreeSat
end

-- Lax564036.ThreeDnfTautology
section
namespace Lax564036.ThreeDnfTautology
end Lax564036.ThreeDnfTautology
end

-- Lax564036.AlternatingMachineInvariance
section
namespace Lax564036.AlternatingMachineInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Sat Lax904597.Machines

open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME

open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology

open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- Being well-formed and accepting is isomorphism-invariant. -/
axiom atmAccepts_iso : ∀ (k : ℕ) (start : Bool) {A B : Type} [(turingAlt k).Structure A]
  [(turingAlt k).Structure B], (A ≃[turingAlt k] B) →
    (ATMAccepts k start A ↔ ATMAccepts k start B)

end Lax564036.AlternatingMachineInvariance
end

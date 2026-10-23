-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Semantics
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

-- Lax904597.Machines
section
namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

variable {A : Type}

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
namespace Lax564036.AlternatingMachines.ATMData.AltAcc
end Lax564036.AlternatingMachines.ATMData.AltAcc

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

open FirstOrder

open Language Structure

section Shorthands

variable {k : ℕ} {A : Type} [(turingAlt k).Structure A]

end Shorthands

end Lax564036.AlternatingMachines
end

-- Lax480241.AlternatingSpace
section
namespace Lax480241.AlternatingSpace

open Lax564036.AlternatingMachines Lax904597.Machines

namespace ATMData

variable {A : Type} (M : ATMData A)

/-- **Winning the alternating game**, with no bound on the length of a play: an
accepting state wins; an existential configuration wins when some successor
does; a universal one wins when it has a successor and every successor wins.

Being a least fixed point, this makes an infinite play a loss for the
existential player – the standard convention, and the one the budgeted
`ATMData.AltAcc` already has. -/
inductive AltWin (start : Bool) : Config A → Prop
  /-- An accepting state wins outright. -/
  | acc {c : Config A} : M.Acc c.state → AltWin start c
  /-- An existential configuration wins when some successor does. -/
  | ex {c c' : Config A} : ¬M.IsUniv start c.state → M.Step c c' → AltWin start c' →
      AltWin start c
  /-- A universal configuration wins when it has a successor and every
  successor wins. -/
  | all {c : Config A} : M.IsUniv start c.state → (∃ c', M.Step c c') →
      (∀ c', M.Step c c' → AltWin start c') → AltWin start c

/-- **Acceptance in bounded space**: an initial configuration wins, the choice
of that configuration belonging to the player who moves first – exactly as in
`ATMData.AltAccepts`, and for the same reason. -/
def AltAcceptsSpace (start : Bool) : Prop :=
  guardQ start (fun c₀ : Config A => M.IsInit c₀) (fun c₀ => ATMData.AltWin M start c₀)

variable {M}

variable (M)

end ATMData

open Lax904597.Problems Lax485149.Problems

end Lax480241.AlternatingSpace
end

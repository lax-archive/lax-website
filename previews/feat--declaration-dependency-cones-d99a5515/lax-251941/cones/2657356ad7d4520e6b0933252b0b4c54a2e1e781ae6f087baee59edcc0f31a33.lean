-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

-- Lax251941.PostCorrespondence
section
namespace Lax251941.PostCorrespondence

/-- A domino: a top string and a bottom string. -/
abbrev Domino (α : Type*) := List α × List α

/-- An instance of the Post correspondence problem: a finite list of dominos. -/
abbrev Inst (α : Type*) := List (Domino α)

/-- The string read off the top halves of a sequence of dominos. -/
def topStr {α : Type*} (s : List (Domino α)) : List α := (s.map Prod.fst).flatten

/-- The string read off the bottom halves of a sequence of dominos. -/
def botStr {α : Type*} (s : List (Domino α)) : List α := (s.map Prod.snd).flatten

/-- `s` is a match of the instance `P`: a nonempty sequence of dominos of `P`
whose top string equals its bottom string. -/
def IsMatch {α : Type*} (P : Inst α) (s : List (Domino α)) : Prop :=
  s ≠ [] ∧ (∀ d ∈ s, d ∈ P) ∧ topStr s = botStr s

/-- The instance `P` has a match. -/
def HasMatch {α : Type*} (P : Inst α) : Prop := ∃ s, IsMatch P s

end Lax251941.PostCorrespondence
end

-- Lax251941.TuringMachines
section
namespace Lax251941.TuringMachines

/-- The symbols in which configurations of a Turing machine, and the strings of
Sipser's reduction, are written. -/
inductive Sym where
  /-- A tape symbol; `Sym.tape 0` is the blank. -/
  | tape : ℕ → Sym
  /-- A state of the machine. -/
  | state : ℕ → Sym
  /-- The separator `#` between consecutive configurations of a history. -/
  | hash : Sym
  /-- The marker opening a computation history. -/
  | start : Sym
  /-- The auxiliary symbol `∗` of the reduction. -/
  | star : Sym
  /-- The auxiliary symbol `◇` of the reduction. -/
  | diamond : Sym
  deriving DecidableEq, Repr

/-- A string rewriting system: an alphabet, a finite list of rewriting rules
`u → v` applied in arbitrary context, and a list of symbols that may be appended
at the right end of a string. -/
structure SRS (α : Type*) where
  /-- The alphabet. -/
  alphabet : List α
  /-- The rewriting rules `u → v`. -/
  rules : List (List α × List α)
  /-- Symbols that may be appended at the right-hand end of a string. -/
  ext : List α

/-- One application of a rule, in a context `l _ r`. -/
inductive StepRule {α : Type*} (rules : List (List α × List α)) : List α → List α → Prop
  | mk (l u v r : List α) : (u, v) ∈ rules → StepRule rules (l ++ u ++ r) (l ++ v ++ r)

/-- One step of a rewriting system: a rule application, or appending one of the
designated symbols on the right. -/
inductive Step {α : Type*} (S : SRS α) : List α → List α → Prop
  | rule {a b : List α} : StepRule S.rules a b → Step S a b
  | ext {c : List α} {x : α} : x ∈ S.ext → Step S c (c ++ [x])

/-- Reachability: the reflexive transitive closure of `Step`. -/
def Reaches {α : Type*} (S : SRS α) : List α → List α → Prop := Relation.ReflTransGen (Step S)

/-- A single-tape Turing machine: a transition table whose entry `(q, a, r, b, dir)`
means `δ(q, a) = (r, b, dir)`, `dir = true` being a move to the right and
`dir = false` a move to the left, together with a start state and an accept
state. -/
structure TM where
  /-- The transition table. -/
  trans : List (ℕ × ℕ × ℕ × ℕ × Bool)
  /-- The start state. -/
  q0 : ℕ
  /-- The accept state. -/
  qacc : ℕ

namespace TM

variable (M : TM) (w : List ℕ)

/-- The tape symbols of a machine run on `w`: the blank, the letters of `w`, and
the symbols read or written by the table. -/
def tapeSyms : List ℕ :=
  0 :: (w ++ M.trans.map (fun x => x.2.1) ++ M.trans.map (fun x => x.2.2.2.1))

/-- The states of a machine: the start state, the accept state and the states of
the table. -/
def states : List ℕ :=
  M.q0 :: M.qacc :: (M.trans.map (fun x => x.1) ++ M.trans.map (fun x => x.2.2.1))

/-- The alphabet in which the configurations of a run on `w` are written. -/
def alphabet : List Sym :=
  (M.tapeSyms w).map Sym.tape ++ M.states.map Sym.state

/-- The rewriting rules `q a → b r` of the moves to the right. -/
def rightRules : List (List Sym × List Sym) :=
  M.trans.filterMap fun x =>
    if x.2.2.2.2 then
      some ([Sym.state x.1, Sym.tape x.2.1], [Sym.tape x.2.2.2.1, Sym.state x.2.2.1])
    else none

/-- The rewriting rules `c q a → r c b` of the moves to the left, one for every
tape symbol `c` to the left of the head. -/
def leftRules : List (List Sym × List Sym) :=
  (M.tapeSyms w).flatMap fun c =>
    M.trans.filterMap fun x =>
      if x.2.2.2.2 then none
      else some ([Sym.tape c, Sym.state x.1, Sym.tape x.2.1],
        [Sym.state x.2.2.1, Sym.tape c, Sym.tape x.2.2.2.1])

/-- The rewriting rules describing the single steps of the machine. -/
def transRules : List (List Sym × List Sym) := M.rightRules ++ M.leftRules w

/-- The rewriting system of the machine on the input `w`: its step rules, with a
blank appendable on the right. -/
def machineSRS : SRS Sym where
  alphabet := M.alphabet w
  rules := M.transRules w
  ext := [Sym.tape 0]

/-- The starting configuration `q₀ w`. -/
def startCfg : List Sym := Sym.state M.q0 :: w.map Sym.tape

/-- The machine accepts `w` if a configuration containing the accept state is
reachable from the starting configuration. -/
def Accepts : Prop :=
  ∃ C, Reaches (M.machineSRS w) (M.startCfg w) C ∧ Sym.state M.qacc ∈ C

end TM

/-- A machine is encoded by its transition table and its two distinguished states.
-/
def tmEquiv : TM ≃ List (ℕ × ℕ × ℕ × ℕ × Bool) × ℕ × ℕ where
  toFun M := (M.trans, M.q0, M.qacc)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := by rintro ⟨t, a, b⟩; rfl
  right_inv := by rintro ⟨t, a, b⟩; rfl

instance : Primcodable TM := Primcodable.ofEquiv _ tmEquiv

end Lax251941.TuringMachines
end

-- Lax251941.PostCorrespondenceReduction
section
namespace Lax251941.PostCorrespondenceReduction

open Lax251941.TuringMachines Lax251941.PostCorrespondence

/-- A decision procedure for the Post correspondence problem would decide the
acceptance problem for Turing machines. -/
axiom computablePred_accepts_of_hasMatch
    (h : ComputablePred fun P : Inst ℕ => HasMatch P) :
    ComputablePred fun p : TM × List ℕ => p.1.Accepts p.2

end Lax251941.PostCorrespondenceReduction
end

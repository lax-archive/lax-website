-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Logic.Relation

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

end Lax251941.TuringMachines
end

-- Lax251941.TuringCompleteness
section
namespace Lax251941.TuringCompleteness

open Lax251941.TuringMachines

/-- For every partial recursive `f` there is a tape machine, with a marker symbol
and a counter symbol, that accepts the unary encoding of `n` exactly when `f n` is
defined. -/
axiom exists_tm_accepts_iff_dom (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ (M : TM) (mk c : ℕ), ∀ n : ℕ, M.Accepts (mk :: List.replicate n c) ↔ (f n).Dom

end Lax251941.TuringCompleteness
end

-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Primrec.List
import Mathlib.Logic.Relation

-- Lax251941.TuringMachines
section
namespace Lax251941.TuringMachines.SRS
end Lax251941.TuringMachines.SRS

namespace Lax251941.TuringMachines.Step
end Lax251941.TuringMachines.Step

namespace Lax251941.TuringMachines.StepRule
end Lax251941.TuringMachines.StepRule

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

/-- The rewriting rules `q a → b r` of the moves to the right. -/
def rightRules : List (List Sym × List Sym) :=
  M.trans.filterMap fun x =>
    if x.2.2.2.2 then
      some ([Sym.state x.1, Sym.tape x.2.1], [Sym.tape x.2.2.2.1, Sym.state x.2.2.1])
    else none

end TM

end Lax251941.TuringMachines
end

-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Primrec.List
import Mathlib.Logic.Relation

-- Lax251941.TuringMachines
section
namespace Lax251941.TuringMachines.Step
end Lax251941.TuringMachines.Step

namespace Lax251941.TuringMachines.StepRule
end Lax251941.TuringMachines.StepRule

namespace Lax251941.TuringMachines.Sym
end Lax251941.TuringMachines.Sym

namespace Lax251941.TuringMachines.Sym.diamond
end Lax251941.TuringMachines.Sym.diamond

namespace Lax251941.TuringMachines.Sym.hash
end Lax251941.TuringMachines.Sym.hash

namespace Lax251941.TuringMachines.Sym.star
end Lax251941.TuringMachines.Sym.star

namespace Lax251941.TuringMachines.Sym.start
end Lax251941.TuringMachines.Sym.start

namespace Lax251941.TuringMachines.Sym.state
end Lax251941.TuringMachines.Sym.state

namespace Lax251941.TuringMachines.Sym.tape
end Lax251941.TuringMachines.Sym.tape

namespace Lax251941.TuringMachines

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

end TM

end Lax251941.TuringMachines
end

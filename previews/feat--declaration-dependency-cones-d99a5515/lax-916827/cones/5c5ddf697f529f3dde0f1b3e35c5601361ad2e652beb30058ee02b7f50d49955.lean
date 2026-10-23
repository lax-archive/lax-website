-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finite.Defs

-- Lax916827.TwoWayTransducers
section
namespace Lax916827.TwoWayTransducers.Cfg
end Lax916827.TwoWayTransducers.Cfg

namespace Lax916827.TwoWayTransducers.Cfg.conf
end Lax916827.TwoWayTransducers.Cfg.conf

namespace Lax916827.TwoWayTransducers.Cfg.halt
end Lax916827.TwoWayTransducers.Cfg.halt

namespace Lax916827.TwoWayTransducers.TwoWay.Reaches
end Lax916827.TwoWayTransducers.TwoWay.Reaches

namespace Lax916827.TwoWayTransducers.TwoWay.cfgAt
end Lax916827.TwoWayTransducers.TwoWay.cfgAt

namespace Lax916827.TwoWayTransducers.TwoWay.stepCfg
end Lax916827.TwoWayTransducers.TwoWay.stepCfg

namespace Lax916827.TwoWayTransducers

/-- A two-way transducer: on the letters adjacent to the head and the state, it
either produces an output string and halts (`Sum.inl`), or produces an output
string, changes state and moves the head left (`false`) or right (`true`). -/
structure TwoWay (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Option A → Q → Option A → List B ⊕ (Q × List B × Bool)

namespace TwoWay

variable {A B Q : Type}

end TwoWay

end Lax916827.TwoWayTransducers
end

-- Lax916827.TwoWayCodes
section
namespace Lax916827.TwoWayCodes

open Lax916827.TwoWayTransducers

/-- A code of a two-way transducer over `ℕ`: a lookup table from triples (letter to
the left, state, letter to the right) to transitions. -/
abbrev TwoWayCode := List ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool)))

/-- The two-way transducer described by a code: initial state `0`, and the table
entry of a triple, or halting with empty output when the triple is absent. -/
def twoWayCodeAut (c : TwoWayCode) : TwoWay ℕ ℕ ℕ where
  init := 0
  step := fun l q r =>
    match c.lookup (l, q, r) with
    | some x => x
    | none => Sum.inl []

end Lax916827.TwoWayCodes
end

-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal

-- Lax199508.GraphClasses
section
namespace Lax199508
end Lax199508

namespace Lax199508.GraphClasses
end Lax199508.GraphClasses
end

-- Lax199508.UniformQuasiWideness
section
namespace Lax199508.UniformQuasiWideness
end Lax199508.UniformQuasiWideness
end

-- Lax3.ColoredGraphs
section
namespace Lax3
end Lax3

namespace Lax3.ColoredGraphs
end Lax3.ColoredGraphs
end

-- Lax3.DistFO
section
namespace Lax3.DistFO
end Lax3.DistFO

namespace Lax3.DistFO.DRank
end Lax3.DistFO.DRank

namespace Lax3.DistFO.DistFO
end Lax3.DistFO.DistFO

namespace Lax3.DistFO.IsLocal
end Lax3.DistFO.IsLocal

namespace Lax3.DistFO.Sat
end Lax3.DistFO.Sat

namespace Lax3.DistFO.rename
end Lax3.DistFO.rename

namespace Lax3.DistFO.DistFO.adj
end Lax3.DistFO.DistFO.adj

namespace Lax3.DistFO.DistFO.and
end Lax3.DistFO.DistFO.and

namespace Lax3.DistFO.DistFO.color
end Lax3.DistFO.DistFO.color

namespace Lax3.DistFO.DistFO.distColorLt
end Lax3.DistFO.DistFO.distColorLt

namespace Lax3.DistFO.DistFO.distLe
end Lax3.DistFO.DistFO.distLe

namespace Lax3.DistFO.DistFO.eq
end Lax3.DistFO.DistFO.eq

namespace Lax3.DistFO.DistFO.exL
end Lax3.DistFO.DistFO.exL

namespace Lax3.DistFO.DistFO.exU
end Lax3.DistFO.DistFO.exU

namespace Lax3.DistFO.DistFO.not
end Lax3.DistFO.DistFO.not
end

-- Lax3.ScatterSentences
section
namespace Lax3.ScatterSentences
end Lax3.ScatterSentences

namespace Lax3.ScatterSentences.ScatterChoice
end Lax3.ScatterSentences.ScatterChoice

namespace Lax3.ScatterSentences.ScatterSentence
end Lax3.ScatterSentences.ScatterSentence
end

-- Lax3.Locality
section
namespace Lax3.Locality

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences

universe u

/-- Boolean combinations of atoms drawn from `α`. Disjunction and
implication are the usual abbreviations; the empty combination is
`tru`. -/
inductive BC (α : Type u) : Type u
  /-- An atom. -/
  | atom (a : α) : BC α
  /-- The empty combination, always true. -/
  | tru : BC α
  /-- Negation. -/
  | not (b : BC α) : BC α
  /-- Conjunction. -/
  | and (b c : BC α) : BC α

/-- The truth value of a boolean combination, given a truth value for
each atom. -/
def BC.eval {α : Type u} (v : α → Prop) : BC α → Prop
  | .atom a => v a
  | .tru => True
  | .not b => ¬ BC.eval v b
  | .and b c => BC.eval v b ∧ BC.eval v c

variable {L : ℕ}

end Lax3.Locality
end

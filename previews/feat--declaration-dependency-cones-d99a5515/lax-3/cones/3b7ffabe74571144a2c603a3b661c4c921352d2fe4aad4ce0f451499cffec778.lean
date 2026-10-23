-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.FinRange
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
namespace Lax3.DistFO.DRank
end Lax3.DistFO.DRank

namespace Lax3.DistFO.IsLocal
end Lax3.DistFO.IsLocal

namespace Lax3.DistFO.Sat
end Lax3.DistFO.Sat

namespace Lax3.DistFO.rename
end Lax3.DistFO.rename

namespace Lax3.DistFO

open Lax3.ColoredGraphs

set_option linter.dupNamespace false in
/-- Formulas of distance logic over `L`-colored graphs, with `k` free
variables. Variables are `Fin k`, and both quantifiers bind the *new
last* index. Beyond the atoms of first-order logic there are colors and
the two distance atoms, and beyond unrestricted quantification there is
local quantification, which ranges over the vertices within a given
radius of the free variables. -/
inductive DistFO (L : ℕ) : ℕ → Type
  /-- The vertices `i` and `j` are adjacent. -/
  | adj {k : ℕ} (i j : Fin k) : DistFO L k
  /-- The vertices `i` and `j` are equal. -/
  | eq {k : ℕ} (i j : Fin k) : DistFO L k
  /-- The vertex `i` has color `c`. -/
  | color {k : ℕ} (c : Fin L) (i : Fin k) : DistFO L k
  /-- Binary distance atom: the distance between `i` and `j` is at most
  `r`. -/
  | distLe {k : ℕ} (r : ℕ) (i j : Fin k) : DistFO L k
  /-- Unary distance atom: the distance from `i` to the color class `c`
  is smaller than `r`. -/
  | distColorLt {k : ℕ} (r : ℕ) (c : Fin L) (i : Fin k) : DistFO L k
  /-- Negation. -/
  | not {k : ℕ} (φ : DistFO L k) : DistFO L k
  /-- Conjunction. -/
  | and {k : ℕ} (φ ψ : DistFO L k) : DistFO L k
  /-- Unrestricted quantification: there is a vertex satisfying `φ`,
  bound at the last index. -/
  | exU {k : ℕ} (φ : DistFO L (k + 1)) : DistFO L k
  /-- Local quantification: there is a vertex within distance `r` of
  some variable in the guard set `g` satisfying `φ`, bound at the last
  index. The radius and the guard set are part of the syntax; which
  radii are admissible at a given distance rank is the business of
  `DRank`, and the guard set is unconstrained there, as in the
  source. -/
  | exL {k : ℕ} (r : ℕ) (g : Finset (Fin k)) (φ : DistFO L (k + 1)) : DistFO L k

variable {L n : ℕ}

end Lax3.DistFO
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
end Lax3.Locality

namespace Lax3.Locality.BC
end Lax3.Locality.BC

namespace Lax3.Locality.BC.and
end Lax3.Locality.BC.and

namespace Lax3.Locality.BC.atom
end Lax3.Locality.BC.atom

namespace Lax3.Locality.BC.eval
end Lax3.Locality.BC.eval

namespace Lax3.Locality.BC.not
end Lax3.Locality.BC.not

namespace Lax3.Locality.BC.tru
end Lax3.Locality.BC.tru
end

-- Lax3.NormalForm
section
namespace Lax3.NormalForm.conj
end Lax3.NormalForm.conj

namespace Lax3.NormalForm

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality

variable {L : ℕ}

/-- `k` unrestricted quantifiers in front of a formula with `k` free
variables, leaving a sentence. -/
def exUs : {k : ℕ} → DistFO L k → DistFO L 0
  | 0, φ => φ
  | _ + 1, φ => exUs (.exU φ)

end Lax3.NormalForm
end

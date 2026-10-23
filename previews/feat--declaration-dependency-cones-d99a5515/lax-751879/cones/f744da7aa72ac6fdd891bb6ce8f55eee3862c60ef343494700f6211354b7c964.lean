-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Set.Lattice

-- Lax751879.OrderedStructures
section
namespace Lax751879
end Lax751879

namespace Lax751879.OrderedStructures
end Lax751879.OrderedStructures

namespace Lax751879.OrderedStructures.OrderedStructure
end Lax751879.OrderedStructures.OrderedStructure

namespace Lax751879.OrderedStructures.PointedStructure
end Lax751879.OrderedStructures.PointedStructure
end

-- Lax751879.FixedPointSyntax
section
namespace Lax751879.FixedPointSyntax
end Lax751879.FixedPointSyntax

namespace Lax751879.FixedPointSyntax.RawFormula
end Lax751879.FixedPointSyntax.RawFormula

namespace Lax751879.FixedPointSyntax.RawFormula.Admissible
end Lax751879.FixedPointSyntax.RawFormula.Admissible

namespace Lax751879.FixedPointSyntax.RawFormula.conj
end Lax751879.FixedPointSyntax.RawFormula.conj

namespace Lax751879.FixedPointSyntax.RawFormula.equal
end Lax751879.FixedPointSyntax.RawFormula.equal

namespace Lax751879.FixedPointSyntax.RawFormula.exists'
end Lax751879.FixedPointSyntax.RawFormula.exists'

namespace Lax751879.FixedPointSyntax.RawFormula.less
end Lax751879.FixedPointSyntax.RawFormula.less

namespace Lax751879.FixedPointSyntax.RawFormula.lfp
end Lax751879.FixedPointSyntax.RawFormula.lfp

namespace Lax751879.FixedPointSyntax.RawFormula.neg
end Lax751879.FixedPointSyntax.RawFormula.neg

namespace Lax751879.FixedPointSyntax.RawFormula.positiveAt
end Lax751879.FixedPointSyntax.RawFormula.positiveAt

namespace Lax751879.FixedPointSyntax.RawFormula.relation
end Lax751879.FixedPointSyntax.RawFormula.relation

namespace Lax751879.FixedPointSyntax.RawFormula.truth
end Lax751879.FixedPointSyntax.RawFormula.truth

namespace Lax751879.FixedPointSyntax.RawFormula.variable
end Lax751879.FixedPointSyntax.RawFormula.variable
end

-- Lax751879.LeastFixedPoints
section
namespace Lax751879
end Lax751879

namespace Lax751879.LeastFixedPoints
end Lax751879.LeastFixedPoints

namespace Lax751879.LeastFixedPoints.stage
end Lax751879.LeastFixedPoints.stage
end

-- Lax751879.FixedPointSemantics
section
namespace Lax751879.FixedPointSemantics.eval
end Lax751879.FixedPointSemantics.eval

namespace Lax751879.FixedPointSemantics

open Lax751879.OrderedStructures Lax751879.FixedPointSyntax

open Lax751879.LeastFixedPoints

abbrev RelationEnv (n : Nat) (ρ : List Nat) :=
  (r : Fin ρ.length) → Set (Fin (ρ.get r) → Fin n)

def extend {n k : Nat} {ρ : List Nat} (R : Set (Fin k → Fin n))
    (η : RelationEnv n ρ) : RelationEnv n (k :: ρ) :=
  Fin.cons R η

end Lax751879.FixedPointSemantics
end

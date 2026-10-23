-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Set.Lattice

-- Lax979537.OrderedStructures
section
namespace Lax979537
end Lax979537

namespace Lax979537.OrderedStructures
end Lax979537.OrderedStructures

namespace Lax979537.OrderedStructures.OrderedStructure
end Lax979537.OrderedStructures.OrderedStructure

namespace Lax979537.OrderedStructures.PointedStructure
end Lax979537.OrderedStructures.PointedStructure
end

-- Lax979537.FixedPointSyntax
section
namespace Lax979537.FixedPointSyntax
end Lax979537.FixedPointSyntax

namespace Lax979537.FixedPointSyntax.RawFormula
end Lax979537.FixedPointSyntax.RawFormula

namespace Lax979537.FixedPointSyntax.RawFormula.Admissible
end Lax979537.FixedPointSyntax.RawFormula.Admissible

namespace Lax979537.FixedPointSyntax.RawFormula.conj
end Lax979537.FixedPointSyntax.RawFormula.conj

namespace Lax979537.FixedPointSyntax.RawFormula.equal
end Lax979537.FixedPointSyntax.RawFormula.equal

namespace Lax979537.FixedPointSyntax.RawFormula.exists'
end Lax979537.FixedPointSyntax.RawFormula.exists'

namespace Lax979537.FixedPointSyntax.RawFormula.less
end Lax979537.FixedPointSyntax.RawFormula.less

namespace Lax979537.FixedPointSyntax.RawFormula.lfp
end Lax979537.FixedPointSyntax.RawFormula.lfp

namespace Lax979537.FixedPointSyntax.RawFormula.neg
end Lax979537.FixedPointSyntax.RawFormula.neg

namespace Lax979537.FixedPointSyntax.RawFormula.positiveAt
end Lax979537.FixedPointSyntax.RawFormula.positiveAt

namespace Lax979537.FixedPointSyntax.RawFormula.relation
end Lax979537.FixedPointSyntax.RawFormula.relation

namespace Lax979537.FixedPointSyntax.RawFormula.truth
end Lax979537.FixedPointSyntax.RawFormula.truth

namespace Lax979537.FixedPointSyntax.RawFormula.variable
end Lax979537.FixedPointSyntax.RawFormula.variable
end

-- Lax979537.LeastFixedPoints
section
namespace Lax979537
end Lax979537

namespace Lax979537.LeastFixedPoints
end Lax979537.LeastFixedPoints

namespace Lax979537.LeastFixedPoints.stage
end Lax979537.LeastFixedPoints.stage
end

-- Lax979537.FixedPointSemantics
section
namespace Lax979537.FixedPointSemantics.eval
end Lax979537.FixedPointSemantics.eval

namespace Lax979537.FixedPointSemantics

open Lax979537.OrderedStructures Lax979537.FixedPointSyntax

open Lax979537.LeastFixedPoints

abbrev RelationEnv (n : Nat) (ρ : List Nat) :=
  (r : Fin ρ.length) → Set (Fin (ρ.get r) → Fin n)

end Lax979537.FixedPointSemantics
end

-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

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

-- Lax979537.StructureEncoding
section
namespace Lax979537.StructureEncoding

open Lax979537.OrderedStructures

/-- All tuples, with the first coordinate varying slowest. -/
def tuples (n : Nat) : (k : Nat) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange n).flatMap fun a =>
      (tuples n k).map (Fin.cons a)

end Lax979537.StructureEncoding
end

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
namespace Lax979537.StructureEncoding.tuples
end Lax979537.StructureEncoding.tuples

namespace Lax979537.StructureEncoding

open Lax979537.OrderedStructures

def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

end Lax979537.StructureEncoding
end

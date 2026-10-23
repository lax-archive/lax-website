-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

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

-- Lax751879.StructureEncoding
section
namespace Lax751879.StructureEncoding.tuples
end Lax751879.StructureEncoding.tuples

namespace Lax751879.StructureEncoding

open Lax751879.OrderedStructures

def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

end Lax751879.StructureEncoding
end

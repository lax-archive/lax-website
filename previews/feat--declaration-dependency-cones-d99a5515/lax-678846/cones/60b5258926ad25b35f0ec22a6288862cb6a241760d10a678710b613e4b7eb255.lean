-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax979537.OrderedStructures
section
namespace Lax979537.OrderedStructures.OrderedStructure
end Lax979537.OrderedStructures.OrderedStructure

namespace Lax979537.OrderedStructures.PointedStructure
end Lax979537.OrderedStructures.PointedStructure

namespace Lax979537.OrderedStructures

abbrev Vocabulary := List Nat

end Lax979537.OrderedStructures
end

-- Lax979537.StructureEncoding
section
namespace Lax979537.StructureEncoding
end Lax979537.StructureEncoding

namespace Lax979537.StructureEncoding.tuples
end Lax979537.StructureEncoding.tuples
end

-- Lax678846.FiniteStructures
section
namespace Lax678846.FiniteStructures.Isomorphism
end Lax678846.FiniteStructures.Isomorphism

namespace Lax678846.FiniteStructures

abbrev Vocabulary := Lax979537.OrderedStructures.Vocabulary

end Lax678846.FiniteStructures
end

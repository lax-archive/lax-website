-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax751879.OrderedStructures
section
namespace Lax751879.OrderedStructures.OrderedStructure
end Lax751879.OrderedStructures.OrderedStructure

namespace Lax751879.OrderedStructures.PointedStructure
end Lax751879.OrderedStructures.PointedStructure

namespace Lax751879.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

end Lax751879.OrderedStructures
end

-- Lax751879.StructureEncoding
section
namespace Lax751879.StructureEncoding
end Lax751879.StructureEncoding

namespace Lax751879.StructureEncoding.tuples
end Lax751879.StructureEncoding.tuples
end

-- Lax988886.FiniteStructures
section
namespace Lax988886.FiniteStructures.Isomorphism
end Lax988886.FiniteStructures.Isomorphism

namespace Lax988886.FiniteStructures

abbrev Symbol := Lax751879.OrderedStructures.Symbol

end Lax988886.FiniteStructures
end

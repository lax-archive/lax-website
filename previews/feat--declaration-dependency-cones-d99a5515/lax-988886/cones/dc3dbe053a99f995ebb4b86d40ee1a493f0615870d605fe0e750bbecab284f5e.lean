-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
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
namespace Lax751879.StructureEncoding
end Lax751879.StructureEncoding

namespace Lax751879.StructureEncoding.tuples
end Lax751879.StructureEncoding.tuples
end

-- Lax988886.FiniteStructures
section
namespace Lax988886
end Lax988886

namespace Lax988886.FiniteStructures
end Lax988886.FiniteStructures

namespace Lax988886.FiniteStructures.Isomorphism
end Lax988886.FiniteStructures.Isomorphism
end

-- Lax988886.NondeterministicPolynomialTime
section
namespace Lax988886.NondeterministicPolynomialTime

open Lax988886.FiniteStructures

def encodePair (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ false :: p.2

def LanguageInNP (L : List Bool → Prop) : Prop :=
  ∃ (V : List Bool × List Bool → Bool) (p : Polynomial Nat),
    Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) V) ∧
    ∀ w, L w ↔ ∃ c : List Bool, c.length ≤ p.eval w.length ∧ V (w, c) = true

end Lax988886.NondeterministicPolynomialTime
end

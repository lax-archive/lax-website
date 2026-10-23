-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Computability.TuringMachine.Computable
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
end Lax979537.StructureEncoding

namespace Lax979537.StructureEncoding.tuples
end Lax979537.StructureEncoding.tuples
end

-- Lax678846.FiniteStructures
section
namespace Lax678846
end Lax678846

namespace Lax678846.FiniteStructures
end Lax678846.FiniteStructures

namespace Lax678846.FiniteStructures.Isomorphism
end Lax678846.FiniteStructures.Isomorphism
end

-- Lax678846.NondeterministicPolynomialTime
section
namespace Lax678846.NondeterministicPolynomialTime

open Lax678846.FiniteStructures

def encodePair (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ false :: p.2

def LanguageInNP (L : List Bool → Prop) : Prop :=
  ∃ (V : List Bool × List Bool → Bool) (p : Polynomial Nat),
    Nonempty (Turing.TM2ComputableInPolyTime encodePair (fun b => [b]) V) ∧
    ∀ w, L w ↔ ∃ c : List Bool, c.length ≤ p.eval w.length ∧ V (w, c) = true

end Lax678846.NondeterministicPolynomialTime
end

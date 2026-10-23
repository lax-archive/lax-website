-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d



-- Lax560851.StructuralPresentation
section
namespace Lax560851
end Lax560851

namespace Lax560851.StructuralPresentation
end Lax560851.StructuralPresentation

namespace Lax560851.StructuralPresentation.Presentation
end Lax560851.StructuralPresentation.Presentation

namespace Lax560851.StructuralPresentation.Raw
end Lax560851.StructuralPresentation.Raw

namespace Lax560851.StructuralPresentation.Raw.nat
end Lax560851.StructuralPresentation.Raw.nat

namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation.Raw.pair
end Lax560851.StructuralPresentation.Raw.pair
end

-- Lax560851.WordArena
section
namespace Lax560851.WordArena.encodeInto
end Lax560851.WordArena.encodeInto

namespace Lax560851.WordArena.WordImage.ChildAddress
end Lax560851.WordArena.WordImage.ChildAddress

namespace Lax560851.WordArena.WordImage.ReachableFrom
end Lax560851.WordArena.WordImage.ReachableFrom

namespace Lax560851.WordArena.WordImage.Represents
end Lax560851.WordArena.WordImage.Represents

namespace Lax560851.WordArena

open Lax560851.StructuralPresentation

universe u

/-- A finite array of unbounded natural-number words. -/
abbrev WordMemory := Array Nat

/-- A closed word array together with its distinguished root address. -/
structure WordImage where
  memory : WordMemory
  root : Nat
  deriving DecidableEq

namespace WordImage

/-- The word at an in-bounds arena address. -/
def wordAt? (I : WordImage) (address : Nat) : Option Nat :=
  I.memory[address]?

end WordImage

end Lax560851.WordArena
end

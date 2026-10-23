-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576
end Lax132576

namespace Lax132576.LabelledAutomata
end Lax132576.LabelledAutomata

namespace Lax132576.LabelledAutomata.LabAut
end Lax132576.LabelledAutomata.LabAut

namespace Lax132576.LabelledAutomata.LabAut.Path
end Lax132576.LabelledAutomata.LabAut.Path
end

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations
end Lax132576.RationalRelations

namespace Lax132576.RationalRelations.NFAO
end Lax132576.RationalRelations.NFAO
end

-- Lax132576.RationalFunctions
section
namespace Lax132576.RationalFunctions
end Lax132576.RationalFunctions
end

-- Lax765601.CompositionClosure
section
namespace Lax765601
end Lax765601

namespace Lax765601.CompositionClosure
end Lax765601.CompositionClosure

namespace Lax765601.CompositionClosure.CompClosure
end Lax765601.CompositionClosure.CompClosure
end

-- Lax765601.MapLifting
section
namespace Lax765601.MapLifting

/-- Cut a string over `A + 1` (the separator being `none`) into its maximal blocks
without the separator; there is always one block more than there are separators.
-/
def splitSep {A : Type} : List (Option A) → List (List A)
  | [] => [[]]
  | none :: w => [] :: splitSep w
  | some a :: w =>
      match splitSep w with
      | [] => [[a]]
      | u :: us => (a :: u) :: us

/-- The map lifting of `f`: apply `f` to every block delimited by the separator,
`w₁ # ⋯ # wₙ ↦ f w₁ # ⋯ # f wₙ`. -/
def mapLift {A B : Type} (f : List A → List B) (w : List (Option A)) : List (Option B) :=
  List.intercalate [none] ((splitSep w).map (fun u => (f u).map some))

end Lax765601.MapLifting
end

-- Lax916827.RegularFunctions
section
namespace Lax916827.RegularFunctions

open Lax765601.MapLifting Lax765601.CompositionClosure Lax132576.RationalFunctions

/-- The map duplicate function `w₁ # ⋯ # wₙ ↦ w₁w₁ # ⋯ # wₙwₙ`. -/
def mapDuplicate (A : Type) : List (Option A) → List (Option A) := mapLift (fun w => w ++ w)

end Lax916827.RegularFunctions
end

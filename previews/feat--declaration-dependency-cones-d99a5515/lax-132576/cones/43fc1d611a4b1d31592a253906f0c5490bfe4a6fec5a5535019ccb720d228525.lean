-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576.LabelledAutomata.LabAut.Path
end Lax132576.LabelledAutomata.LabAut.Path

namespace Lax132576.LabelledAutomata

namespace LabAut

variable {A L Q : Type}

/-- The labels along a path, in the order of the transitions. -/
def labelsOf (ts : List (Q × List A × L × Q)) : List L := ts.map (fun t => t.2.2.1)

end LabAut

end Lax132576.LabelledAutomata
end

-- Lax132576.WeightedAutomata
section
namespace Lax132576.WeightedAutomata

open Lax132576.LabelledAutomata

variable {A S Q : Type} [Semiring S]

/-- The weight of a path: the product of the weights of its transitions, in the
order in which they are taken. -/
def weightOf (ts : List (Q × List A × S × Q)) : S := (LabAut.labelsOf ts).prod

end Lax132576.WeightedAutomata
end

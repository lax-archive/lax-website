-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations

open Lax132576.LabelledAutomata

namespace NFAO

variable {A B Q : Type}

/-- The output string of a path: the concatenation of the outputs of its
transitions. -/
def outputOf (ts : List (Q × List A × List B × Q)) : List B := (LabAut.labelsOf ts).flatten

end NFAO

end Lax132576.RationalRelations
end

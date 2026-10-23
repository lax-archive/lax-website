-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

-- Lax825748.Series
section
namespace Lax825748
end Lax825748

namespace Lax825748.Series
end Lax825748.Series
end

-- Lax825748.LieRank
section
namespace Lax825748.LieRank
end Lax825748.LieRank
end

-- Lax825748.PBW
section
noncomputable section

namespace Lax825748.PBW

open Series LieRank

abbrev OrderedWord (ι : Type) [LinearOrder ι] :=
  {l : List ι // l.Pairwise (· ≤ ·)}

end Lax825748.PBW
end

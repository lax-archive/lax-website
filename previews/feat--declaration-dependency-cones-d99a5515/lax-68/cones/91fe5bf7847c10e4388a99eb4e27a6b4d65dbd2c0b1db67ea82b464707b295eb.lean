-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- Lax68.GraphMinors
section
namespace Lax68.GraphMinors.MinorModel
end Lax68.GraphMinors.MinorModel

set_option autoImplicit false

namespace Lax68.GraphMinors

abbrev K4 : SimpleGraph (Fin 4) :=
  SimpleGraph.completeGraph (Fin 4)

end Lax68.GraphMinors
end

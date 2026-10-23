-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps

-- Lax68.Triangles
section
set_option autoImplicit false

namespace Lax68.Triangles

def IsTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.completeGraph (Fin 3))

end Lax68.Triangles
end

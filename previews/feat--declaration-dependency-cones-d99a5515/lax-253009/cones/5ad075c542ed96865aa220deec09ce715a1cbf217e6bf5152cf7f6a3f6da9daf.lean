-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

-- Lax253009.LocalTests
section
namespace Lax253009.LocalTests

abbrev View (m : ℕ) := Fin m → Option Bool

structure System (r m : ℕ) where
  accepting : Fin r → Finset (View m)

end Lax253009.LocalTests
end

-- Lax253009.ConsistencyGraph
section
namespace Lax253009.ConsistencyGraph

open LocalTests

abbrev Vertex {r m : ℕ} (C : System r m) :=
  (seed : Fin r) × {a // a ∈ C.accepting seed}

end Lax253009.ConsistencyGraph
end

-- Lax253009.CliqueCorrespondence
section
namespace Lax253009.CliqueCorrespondence

open LocalTests ConsistencyGraph

axiom vertex_bound {r m : ℕ} (C : System r m) (A : ℕ)
    (hA : ∀ seed, (C.accepting seed).card ≤ A) :
  Fintype.card (Vertex C) ≤ r * A

end Lax253009.CliqueCorrespondence
end

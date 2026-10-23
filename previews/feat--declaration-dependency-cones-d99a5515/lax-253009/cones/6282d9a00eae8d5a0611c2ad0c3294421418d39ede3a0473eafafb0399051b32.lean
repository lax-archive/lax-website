-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.FinRange
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.BernoulliSampling
section
namespace Lax253009.BernoulliSampling
end Lax253009.BernoulliSampling
end

-- Lax253009.Graphs
section
namespace Lax253009
end Lax253009

namespace Lax253009.Graphs
end Lax253009.Graphs

namespace Lax253009.Graphs.Graph
end Lax253009.Graphs.Graph
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax253009.Approximation
section
namespace Lax253009.Approximation
end Lax253009.Approximation
end

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
end Lax253009.CliqueCorrespondence
end

-- Lax253009.GraphEncoding
section
namespace Lax253009.GraphEncoding
end Lax253009.GraphEncoding
end

-- Lax253009.EncodedReduction
section
namespace Lax253009.EncodedReduction
end Lax253009.EncodedReduction
end

-- Lax253009.TestSampling
section
namespace Lax253009.TestSampling

open LocalTests FiniteProbability ConsistencyGraph

def sampled {r m N : ℕ} (C : System r m) (z : Fin N → Fin r) : System N m :=
  ⟨fun i ↦ C.accepting (z i)⟩

axiom vertex_bound {r m N : ℕ} (C : System r m) (z : Fin N → Fin r)
    (A : ℕ) (hA : ∀ seed, (C.accepting seed).card ≤ A) :
    Fintype.card (Vertex (sampled C z)) ≤ N * A

end Lax253009.TestSampling
end

-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.BernoulliSampling
section
namespace Lax323828.BernoulliSampling
end Lax323828.BernoulliSampling
end

-- Lax323828.Graphs
section
namespace Lax323828
end Lax323828

namespace Lax323828.Graphs
end Lax323828.Graphs

namespace Lax323828.Graphs.Graph
end Lax323828.Graphs.Graph
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax323828.Approximation
section
namespace Lax323828.Approximation
end Lax323828.Approximation
end

-- Lax323828.LocalTests
section
namespace Lax323828
end Lax323828

namespace Lax323828.LocalTests
end Lax323828.LocalTests

namespace Lax323828.LocalTests.System
end Lax323828.LocalTests.System
end

-- Lax323828.ConsistencyGraph
section
namespace Lax323828.ConsistencyGraph
end Lax323828.ConsistencyGraph
end

-- Lax323828.CliqueCorrespondence
section
namespace Lax323828.CliqueCorrespondence
end Lax323828.CliqueCorrespondence
end

-- Lax323828.GraphEncoding
section
namespace Lax323828.GraphEncoding
end Lax323828.GraphEncoding
end

-- Lax323828.EncodedReduction
section
namespace Lax323828.EncodedReduction
end Lax323828.EncodedReduction
end

-- Lax323828.TestSampling
section
namespace Lax323828.TestSampling
end Lax323828.TestSampling
end

-- Lax323828.TestRepetition
section
namespace Lax323828.TestRepetition
end Lax323828.TestRepetition

namespace Lax323828.TestRepetition.merge
end Lax323828.TestRepetition.merge
end

-- Lax323828.SamplingParameters
section
namespace Lax323828.SamplingParameters

def repetitions (c m : ℕ) : ℕ := c * (Nat.clog 2 (m + 2) + 3)

def vertexBound (f t k m : ℕ) : ℕ := (m + 2) * 2 ^ ((t + f) * k)

axiom polynomial_bound (f t c m : ℕ) :
  vertexBound f t (repetitions c m) m ≤
    16 ^ ((t + f) * c) * (m + 2) ^ ((t + f) * c + 1)

end Lax323828.SamplingParameters
end

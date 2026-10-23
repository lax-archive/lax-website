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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.FinRange
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.LongCode
section
namespace Lax323828.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

end Lax323828.LongCode
end

-- Lax323828.CNASoundness
section
namespace Lax323828.CNASoundness
end Lax323828.CNASoundness
end

-- Lax323828.ManyTableConsistency
section
namespace Lax323828.ManyTableConsistency
end Lax323828.ManyTableConsistency
end

-- Lax323828.FAFTest
section
namespace Lax323828.FAFTest
end Lax323828.FAFTest
end

-- Lax323828.LongCodePatterns
section
namespace Lax323828.LongCodePatterns
end Lax323828.LongCodePatterns
end

-- Lax323828.FAFPatterns
section
namespace Lax323828.FAFPatterns
end Lax323828.FAFPatterns
end

-- Lax323828.DecodedStrategies
section
namespace Lax323828.DecodedStrategies
end Lax323828.DecodedStrategies
end

-- Lax323828.FAFStrategyExtraction
section
namespace Lax323828.FAFStrategyExtraction

open LongCode FiniteProbability

abbrev Seed (Ω : Type) (u w n s q : ℕ) :=
  ((Fin n → Ω) × (Fin q → Coordinate u)) × (Fin n → Fin s → Coordinate w)

end Lax323828.FAFStrategyExtraction
end

-- Lax323828.FAFComposition
section
namespace Lax323828.FAFComposition
end Lax323828.FAFComposition
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

-- Lax323828.FAFLocalTests
section
namespace Lax323828.FAFLocalTests.parts
end Lax323828.FAFLocalTests.parts

namespace Lax323828.FAFLocalTests

open scoped Classical

open LongCode LocalTests LongCodePatterns TestRepetition TestSampling

/-- A reference question together with all random choices made by its local test. -/
abbrev Randomness (U Ω : Type) (u w n s q : ℕ) :=
  U × FAFStrategyExtraction.Seed Ω u w n s q

/-- Number the possible random choices consecutively. -/
noncomputable def randomEquiv (U Ω : Type) [Fintype U] [Fintype Ω] (u w n s q : ℕ) :
    Randomness U Ω u w n s q ≃ Fin (Fintype.card (Randomness U Ω u w n s q)) :=
  Fintype.equivFin _

end Lax323828.FAFLocalTests
end

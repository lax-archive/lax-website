-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
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

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

end Lax253009.LongCode
end

-- Lax253009.CNASoundness
section
namespace Lax253009.CNASoundness
end Lax253009.CNASoundness
end

-- Lax253009.ManyTableConsistency
section
namespace Lax253009.ManyTableConsistency
end Lax253009.ManyTableConsistency
end

-- Lax253009.FAFTest
section
namespace Lax253009.FAFTest
end Lax253009.FAFTest
end

-- Lax253009.LongCodePatterns
section
namespace Lax253009.LongCodePatterns
end Lax253009.LongCodePatterns
end

-- Lax253009.FAFPatterns
section
namespace Lax253009.FAFPatterns
end Lax253009.FAFPatterns
end

-- Lax253009.DecodedStrategies
section
namespace Lax253009.DecodedStrategies
end Lax253009.DecodedStrategies
end

-- Lax253009.FAFStrategyExtraction
section
namespace Lax253009.FAFStrategyExtraction
end Lax253009.FAFStrategyExtraction
end

-- Lax253009.FAFComposition
section
namespace Lax253009.FAFComposition
end Lax253009.FAFComposition
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
namespace Lax253009
end Lax253009

namespace Lax253009.LocalTests
end Lax253009.LocalTests

namespace Lax253009.LocalTests.System
end Lax253009.LocalTests.System
end

-- Lax253009.ConsistencyGraph
section
namespace Lax253009.ConsistencyGraph
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
end Lax253009.TestSampling
end

-- Lax253009.TestRepetition
section
namespace Lax253009.TestRepetition
end Lax253009.TestRepetition

namespace Lax253009.TestRepetition.merge
end Lax253009.TestRepetition.merge
end

-- Lax253009.FAFLocalTests
section
namespace Lax253009.FAFLocalTests.parts
end Lax253009.FAFLocalTests.parts

namespace Lax253009.FAFLocalTests

open LongCode LocalTests LongCodePatterns TestRepetition TestSampling

abbrev Index (U W : Type) (u w : ℕ) := (U × Coordinate u) ⊕ (W × Coordinate w)

end Lax253009.FAFLocalTests
end

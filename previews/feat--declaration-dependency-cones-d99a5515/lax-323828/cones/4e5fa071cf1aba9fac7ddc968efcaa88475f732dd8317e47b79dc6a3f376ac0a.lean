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

abbrev Table (w : ℕ) := Coordinate w → Bool

def compose {w s : ℕ} (f : Fin s → Coordinate w) (B : Word s → Bool) : Coordinate w :=
  fun x ↦ B (fun i ↦ f i x)

def Accepts {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) : Prop :=
  ∀ B : Word s → Bool, A (compose f B) = B (fun i ↦ A (f i))

def AgreesOn {w : ℕ} (h g g' : Coordinate w) : Prop :=
  ∀ x, h x = true → g x = g' x

def Queried {w s : ℕ} (f : Fin s → Coordinate w) (g : Coordinate w) : Prop :=
  (∃ i, g = f i) ∨ ∃ B : Word s → Bool, g = compose f B

def AcceptsWithCondition {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) : Prop :=
  Accepts A f ∧ ∀ g, Queried f g → ∀ g', AgreesOn h g g' → A g = A g'

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

open scoped Classical

open LongCode

/-- A partial Boolean answer table; `none` marks an unqueried coordinate. -/
abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

/-- Record the table answers on the queried coordinates and leave the others unspecified. -/
noncomputable def restrict {w : ℕ} (Q : Coordinate w → Prop) (A : Table w) :
    Pattern w :=
  fun g ↦ if Q g then some (A g) else none

/-- A coordinate queried by the test or forced by agreement on the side condition. -/
def SideQueried {w s : ℕ} (f : Fin s → Coordinate w) (h g' : Coordinate w) : Prop :=
  ∃ g, Queried f g ∧ AgreesOn h g g'

/-- All queried answer patterns arising from tables accepted with the side condition. -/
noncomputable def sidePatterns {w s : ℕ} (f : Fin s → Coordinate w)
    (h : Coordinate w) : Finset (Pattern w) :=
  (Finset.univ.filter (fun A : Table w ↦ AcceptsWithCondition A f h)).image
    (restrict (SideQueried f h))

end Lax323828.LongCodePatterns
end

-- Lax323828.FAFPatterns
section
namespace Lax323828.FAFPatterns

open scoped Classical

open LongCode LongCodePatterns

/-- The side condition on a larger-table word: validity and agreement with all reference answers. -/
noncomputable def conditionOfAnswers {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Ω) (g : Fin q → Coordinate u) (b : Word q) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = b j)

/-- All reference answer strings paired with one permissible partial pattern for each sampled larger table. -/
noncomputable def patterns {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u) (f : Fin n → Fin s → Coordinate w) :
    Finset (Word q × (Fin n → Pattern w)) :=
  Finset.univ.biUnion (fun b : Word q ↦
    (Fintype.piFinset (fun i ↦ sidePatterns (f i) (conditionOfAnswers ρ valid (ω i) g b))).image
      (fun a ↦ (b, a)))

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
namespace Lax323828.LocalTests

open scoped Classical

/-- A complete Boolean proof with `m` positions. -/
abbrev Oracle (m : ℕ) := Fin m → Bool

/-- A partial proof; `none` means that the position is not queried. -/
abbrev View (m : ℕ) := Fin m → Option Bool

/-- The complete proof agrees with every specified answer in the local view. -/
def Extends {m : ℕ} (π : Oracle m) (a : View m) : Prop :=
  ∀ i b, a i = some b → π i = b

/-- The two partial views agree at all positions where both specify an answer. -/
def Compatible {m : ℕ} (a b : View m) : Prop :=
  ∀ i x y, a i = some x → b i = some y → x = y

/-- For each random choice, the collection of local views that make the verifier accept. -/
structure System (r m : ℕ) where
  /-- The acceptable partial answer patterns for this random choice. -/
  accepting : Fin r → Finset (View m)

end Lax323828.LocalTests
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

open LocalTests FiniteProbability ConsistencyGraph

def Passes {r m : ℕ} (C : System r m) (π : Oracle m) (seed : Fin r) : Prop :=
  ∃ a ∈ C.accepting seed, Extends π a

def Complete {r m : ℕ} (C : System r m) : Prop := ∃ π, ∀ seed, Passes C π seed

end Lax323828.TestSampling
end

-- Lax323828.TestRepetition
section
namespace Lax323828.TestRepetition

open scoped Classical

open LocalTests TestSampling FiniteProbability

/-- Every pair of local views gives the same answer wherever both are defined. -/
def Coherent {m k : ℕ} (a : Fin k → View m) : Prop :=
  ∀ i j, Compatible (a i) (a j)

/-- Combine the views into one partial assignment, using the first available answer at each coordinate. -/
def merge {m : ℕ} : {k : ℕ} → (Fin k → View m) → View m
  | 0, _ => fun _ ↦ none
  | k + 1, a => fun i ↦ (a 0 i).or (merge (fun j : Fin k ↦ a j.succ) i)

end Lax323828.TestRepetition
end

-- Lax323828.FAFLocalTests
section
namespace Lax323828.FAFLocalTests

open scoped Classical

open LongCode LocalTests LongCodePatterns TestRepetition TestSampling

/-- All coordinates of the reference tables and the larger tables, kept as two separate families. -/
abbrev Index (U W : Type) (u w : ℕ) := (U × Coordinate u) ⊕ (W × Coordinate w)

/-- A reference question together with all random choices made by its local test. -/
abbrev Randomness (U Ω : Type) (u w n s q : ℕ) :=
  U × FAFStrategyExtraction.Seed Ω u w n s q

/-- Number the proof coordinates consecutively. -/
noncomputable def indexEquiv (U W : Type) [Fintype U] [Fintype W] (u w : ℕ) :
    Index U W u w ≃ Fin (Fintype.card (Index U W u w)) := Fintype.equivFin _

/-- Number the possible random choices consecutively. -/
noncomputable def randomEquiv (U Ω : Type) [Fintype U] [Fintype Ω] (u w n s q : ℕ) :
    Randomness U Ω u w n s q ≃ Fin (Fintype.card (Randomness U Ω u w n s q)) :=
  Fintype.equivFin _

/-- Translate the reference answers and the larger-table patterns into partial assignments to the global proof. -/
noncomputable def parts {U Ω W : Type} [Fintype U] [Fintype W] {u w n s q : ℕ}
    (question : U → Ω → W) (z : Randomness U Ω u w n s q)
    (p : LongCode.Word q × (Fin n → Pattern w)) :
    Fin (q + n) → View (Fintype.card (Index U W u w)) :=
  Fin.addCases
    (fun j x ↦ if x = indexEquiv U W u w (Sum.inl (z.1, z.2.1.2 j)) then some (p.1 j) else none)
    (fun i x ↦ match (indexEquiv U W u w).symm x with
      | .inl _ => none
      | .inr (v, g) => if v = question z.1 (z.2.1.1 i) then p.2 i g else none)

/-- For each random choice, merge exactly the mutually consistent accepting partial assignments. -/
noncomputable def system {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w) :
    System (Fintype.card (Randomness U Ω u w n s q)) (Fintype.card (Index U W u w)) :=
  ⟨fun seed ↦
    let z := (randomEquiv U Ω u w n s q).symm seed
    ((FAFPatterns.patterns (ρ z.1) (valid z.1) z.2.1.1 z.2.1.2 z.2.2).filter
      (fun p ↦ Coherent (parts question z p))).image (fun p ↦ merge (parts question z p))⟩

axiom perfect_completeness {U Ω W : Type} [Fintype U] [Fintype Ω] [Fintype W]
    {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → LongCode.Word w → LongCode.Word u) (valid : U → Ω → Coordinate w)
    (P : W → LongCode.Word w) (Q : U → LongCode.Word u)
    (hvalid : ∀ v ω, valid v ω (P (question v ω)) = true)
    (hproject : ∀ v ω, ρ v ω (P (question v ω)) = Q v) :
  Complete (system (n := n) (s := s) (q := q) question ρ valid)

end Lax323828.FAFLocalTests
end

-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

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

/-- The random choices on which the supplied proof extends an accepting view. -/
noncomputable def System.acceptedSeeds {r m : ℕ} (C : System r m)
    (π : Oracle m) : Finset (Fin r) :=
  Finset.univ.filter fun seed ↦ ∃ a ∈ C.accepting seed, Extends π a

/-- The largest number of accepting random choices attained by any single proof. -/
noncomputable def System.optimum {r m : ℕ} (C : System r m) : ℕ :=
  Finset.univ.sup fun π : Oracle m ↦ (C.acceptedSeeds π).card

end Lax323828.LocalTests
end

-- Lax323828.ConsistencyGraph
section
namespace Lax323828.ConsistencyGraph

open LocalTests

abbrev Vertex {r m : ℕ} (C : System r m) :=
  (seed : Fin r) × {a // a ∈ C.accepting seed}

def graph {r m : ℕ} (C : System r m) : SimpleGraph (Vertex C) where
  Adj u v := u.1 ≠ v.1 ∧ Compatible u.2.1 v.2.1
  symm := ⟨fun _ _ h ↦ ⟨Ne.symm h.1,
    fun i x y hx hy ↦ (h.2 i y x hy hx).symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

end Lax323828.ConsistencyGraph
end

-- Lax323828.CliqueCorrespondence
section
namespace Lax323828.CliqueCorrespondence

open LocalTests ConsistencyGraph

axiom cliqueNumber_eq_optimum {r m : ℕ} (C : System r m) :
  (graph C).cliqueNum = C.optimum

end Lax323828.CliqueCorrespondence
end

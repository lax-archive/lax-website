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

abbrev Oracle (m : ℕ) := Fin m → Bool

abbrev View (m : ℕ) := Fin m → Option Bool

def Extends {m : ℕ} (π : Oracle m) (a : View m) : Prop :=
  ∀ i b, a i = some b → π i = b

def Compatible {m : ℕ} (a b : View m) : Prop :=
  ∀ i x y, a i = some x → b i = some y → x = y

structure System (r m : ℕ) where
  accepting : Fin r → Finset (View m)

noncomputable def System.acceptedSeeds {r m : ℕ} (C : System r m)
    (π : Oracle m) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter fun seed ↦ ∃ a ∈ C.accepting seed, Extends π a

noncomputable def System.optimum {r m : ℕ} (C : System r m) : ℕ :=
  Finset.univ.sup fun π : Oracle m ↦ (C.acceptedSeeds π).card

end Lax253009.LocalTests
end

-- Lax253009.ConsistencyGraph
section
namespace Lax253009.ConsistencyGraph

open LocalTests

abbrev Vertex {r m : ℕ} (C : System r m) :=
  (seed : Fin r) × {a // a ∈ C.accepting seed}

def graph {r m : ℕ} (C : System r m) : SimpleGraph (Vertex C) where
  Adj u v := u.1 ≠ v.1 ∧ Compatible u.2.1 v.2.1
  symm := ⟨fun _ _ h ↦ ⟨Ne.symm h.1,
    fun i x y hx hy ↦ (h.2 i y x hy hx).symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

end Lax253009.ConsistencyGraph
end

-- Lax253009.CliqueCorrespondence
section
namespace Lax253009.CliqueCorrespondence

open LocalTests ConsistencyGraph

axiom cliqueNumber_eq_optimum {r m : ℕ} (C : System r m) :
  (graph C).cliqueNum = C.optimum

end Lax253009.CliqueCorrespondence
end

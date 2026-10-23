-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.DeriveFintype

-- Lax342547.HoleRelation
section
namespace Lax342547
end Lax342547

namespace Lax342547.HoleRelation
end Lax342547.HoleRelation

namespace Lax342547.HoleRelation.HoleData
end Lax342547.HoleRelation.HoleData
end

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

instance (b degree : ℕ) : Fintype (SelectorCoordinates b degree) :=
  inferInstanceAs (Fintype {S : Finset (Fin b) // S.card ≤ degree})

def selectorEval {b degree : ℕ} (s : Fin b → Binary)
    (c : SelectorCoordinates b degree) : Binary := ∏ i ∈ c.val, s i

variable {Label Coord Base : Type}

def baseEval (z : Base → Binary) : Option Base → Binary
  | none => 1
  | some i => z i

def point (p : Label → Coord → Binary) (s : Label) (z : Base → Binary)
    (i : Coord × Option Base) : Binary := p s i.1 * baseEval z i.2

end Lax342547.MomentSpace
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm

open Lax342547.MomentSpace

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

def rankOne (a b : X →ₗ[Binary] Binary) : LinearMap.BilinForm Binary X := a.smulRight b

end Lax342547.GradientForm
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles
end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry.allowedBase
end Lax342547.TagGeometry.allowedBase

namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

def interval (k : ℕ) (d : Tag k) : Finset (Tag k) :=
  Finset.univ.image (fun i : Fin k => d + (i.val + 1 : ℕ))

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

end Lax342547.TagGeometry
end

-- Lax342547.ConcreteGeometry
section
namespace Lax342547.ConcreteGeometry.changeZ
end Lax342547.ConcreteGeometry.changeZ

namespace Lax342547.ConcreteGeometry

open Lax342547.MomentSpace Lax342547.TagGeometry

abbrev Coordinate (k n b degree : ℕ) := SelectorCoordinates b degree × Option (Base k n)

noncomputable instance (k n b degree : ℕ) : DecidableEq (Coordinate k n b degree) := Classical.decEq _

abbrev Vector (k n b degree : ℕ) := Coordinate k n b degree → Binary

abbrev Moment (k n b degree : ℕ) := Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary

def ordinary {k n : ℕ} (d t : Tag k) (i : Fin n) : Base k n := Sum.inl ((d, t), i)

def shared {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (0, i)

def sharp {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (1, i)

def free {k n : ℕ} (i : Fin n) : Base k n := Sum.inr (2, i)

def emptySelector (b degree : ℕ) : SelectorCoordinates b degree := ⟨∅, Nat.zero_le _⟩

def bitSelector {b degree : ℕ} (h : 1 ≤ degree) (a : Fin b) : SelectorCoordinates b degree :=
  ⟨{a}, by simpa using h⟩

def pairLeft {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val, by omega⟩

def pairRight {n r : ℕ} (h : 2 * r ≤ n) (ρ : Fin r) : Fin n := ⟨2 * ρ.val + 1, by omega⟩

def matrixEntry {I : Type} (i j : I) : Matrix I I Binary →ₗ[Binary] Binary where
  toFun w := w i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blockTester {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    Moment k n b degree →ₗ[Binary] Binary :=
  ∑ ρ : Fin r, matrixEntry (emptySelector b degree, some (c (pairLeft h ρ)))
    (emptySelector b degree, some (c (pairRight h ρ)))

def etaO {k n b degree r : ℕ} (h : 2 * r ≤ n) : Moment k n b degree →ₗ[Binary] Binary :=
  ∑ d : Tag k, ∑ t : Tag k, blockTester h (ordinary d t)

def blockForm {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ ρ : Fin r, GradientForm.rankOne
    (LinearMap.proj (emptySelector b degree, some (c (pairLeft h ρ))))
    (LinearMap.proj (emptySelector b degree, some (c (pairRight h ρ))))

def testerForm {k n b degree r : ℕ} (h : 2 * r ≤ n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  (∑ d : Tag k, ∑ t : Tag k, blockForm h (ordinary d t)) + blockForm h shared

def sharpForm {k n b degree : ℕ} (h : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ a : Fin b, ∑ i : Fin n, ∑ j : Fin n, M a i j •
    (GradientForm.rankOne (LinearMap.proj (bitSelector h a, some (sharp i)))
      (LinearMap.proj (emptySelector b degree, some (sharp j))) +
    GradientForm.rankOne (LinearMap.proj (emptySelector b degree, some (sharp i)))
      (LinearMap.proj (bitSelector h a, some (sharp j))))

noncomputable def selfGram {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Moment k n b degree :=
  (testerForm hr + sharpForm hd M).toMatrix'

end Lax342547.ConcreteGeometry
end

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames
end Lax342547.RawFrames

namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame
end

-- Lax342547.ConcreteCut
section
namespace Lax342547.ConcreteCut
end Lax342547.ConcreteCut

namespace Lax342547.ConcreteCut.Testers
end Lax342547.ConcreteCut.Testers
end

-- Lax342547.Atoms
section
namespace Lax342547.Atoms.testerSummary
end Lax342547.Atoms.testerSummary

namespace Lax342547.Atoms

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.ConcreteCut

inductive Flavor (k : ℕ) where
  | generic
  | sharedOnly
  | pure (blocks : Finset (Tag k × Tag k))
  deriving Fintype

def retained {k n : ℕ} (l : Tag k) (f : Flavor k) : Set (Base k n)
  | Sum.inl ((d, t), _) => l ∈ interval k d ∧ match f with
      | .generic => True
      | .sharedOnly => False
      | .pure blocks => (d, t) ∈ blocks
  | Sum.inr (q, _) => match f with
      | .pure _ => q ≠ 0
      | _ => True

abbrev Parameters {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) :=
  {i : Base k n // i ∈ retained l f} → Binary

noncomputable instance {k n : ℕ} (l : Tag k) (f : Flavor k) :
    Fintype {i : Base k n // i ∈ retained l f} := Fintype.ofFinite _

noncomputable def parameterValue {k n : ℕ} {l : Tag k} {f : Flavor k} (p : Parameters n l f)
    (i : Base k n) : Binary := by
  classical
  exact if hi : i ∈ retained l f then p ⟨i, hi⟩ else 0

end Lax342547.Atoms
end

-- Lax342547.AtomDirections
section
namespace Lax342547.AtomDirections

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

noncomputable def blockDirections {k n b degree : ℕ} (s : Fin b → Binary)
    (c : Fin n → Base k n) : Matrix (Coordinate k n b degree) (Fin n) Binary := by
  classical
  exact fun i j => if i.2 = some (c j) then selectorEval s i.1 else 0

end Lax342547.AtomDirections
end

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
end

-- Lax342547.LowRankCounting
section
namespace Lax342547.LowRankCounting
end Lax342547.LowRankCounting
end

-- Lax342547.OrderedMixerLaw
section
namespace Lax342547.OrderedMixerLaw

variable {K I N P : Type} [Field K] [Fintype I]

def orders (D : Matrix I N K) (E : Matrix I P K) :
    Matrix I I K →ₗ[K] (Matrix N P K × Matrix P N K) where
  toFun L := (D.transpose * L * E, E.transpose * L * D)
  map_add' L M := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a L := by simp [Matrix.mul_smul, Matrix.smul_mul]

def parity (a b : K) : (Matrix N P K × Matrix P N K) →ₗ[K] Matrix N P K where
  toFun x := a • x.1 + b • x.2.transpose
  map_add' x y := by simp [smul_add, add_add_add_comm]
  map_smul' c x := by simp [smul_add, smul_smul, mul_comm]

def familyParity {F : Type} [Fintype F] (D : Matrix I N K) (E : Matrix I P K) (a b : F → K) :
    (F → Matrix I I K) →ₗ[K] Matrix N P K :=
  ∑ j, ((parity (a j) (b j)).comp (orders D E)).comp (LinearMap.proj j)

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.AtomDirections

open scoped ENNReal

end Lax342547.OrderedMixerLaw
end

-- Lax342547.SharpMixerLaw
section
namespace Lax342547.SharpMixerLaw

variable {K A I N P : Type} [Field K] [Fintype A]

def weighted (c : A → K) : (A → Matrix I I K) →ₗ[K] Matrix I I K where
  toFun M := ∑ a, c a • M a
  map_add' M L := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' r M := by simp [smul_smul, Finset.smul_sum, mul_comm]

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.AtomDirections

open scoped ENNReal

end Lax342547.SharpMixerLaw
end

-- Lax342547.BinaryMixer
section
namespace Lax342547.BinaryMixer

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.Atoms Lax342547.AtomDirections

abbrev ParameterIndex {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) :=
  {i : Base k n // i ∈ retained l f}

noncomputable def pointInput {k n b degree : ℕ} (s : Fin b → Binary)
    {l : Tag k} {f : Flavor k} (p : Parameters n l f) : Vector k n b degree :=
  point selectorEval s (parameterValue p)

noncomputable def mixedMatrix {P Q : Type} [DecidableEq P] [DecidableEq Q]
    (f : (P → Binary) → (Q → Binary) → Binary) : Matrix P Q Binary :=
  fun i j => f (Pi.single i 1) (Pi.single j 1) + f (Pi.single i 1) 0 +
    f 0 (Pi.single j 1) + f 0 0

noncomputable def bilinearPart {k n b degree : ℕ} (A : Moment k n b degree)
    (s t : Fin b → Binary) (l m : Tag k) (f g : Flavor k) :
    Matrix (ParameterIndex n l f) (ParameterIndex n m g) Binary := by
  classical
  exact mixedMatrix (fun p q => A.toBilin' (pointInput s p) (pointInput t q))

def ambientParity {I F : Type} [Fintype F] (L : F → Matrix I I Binary)
    (a b : F → Binary) (E : Matrix I I Binary) (c d : Binary) : Matrix I I Binary :=
  (∑ j, (a j • L j + b j • (L j).transpose)) + c • E + d • E.transpose

end Lax342547.BinaryMixer
end

-- Lax342547.BinaryMixers
section
namespace Lax342547.BinaryMixers

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.Atoms Lax342547.AtomDirections Lax342547.BinaryMixer

def MixerGood {k n b degree : ℕ} {F : Type} [Fintype F]
    (L : F → Moment k n b degree) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ a b' : F → Binary,
    (∃ j, a j ≠ 0 ∨ b' j ≠ 0) →
      n ≤ 5 * (OrderedMixerLaw.familyParity (blockDirections s free)
        (blockDirections t free) a b' L).rank

def SharpGood {n b : ℕ} (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ c d : Binary, (c ≠ 0 ∨ d ≠ 0) →
    n ≤ 5 * (c • SharpMixerLaw.weighted (fun a => s a + t a) M +
      d • (SharpMixerLaw.weighted (fun a => s a + t a) M).transpose).rank

def UniformBinary {k n b degree r : ℕ} {F : Type} [Fintype F]
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (L : F → Moment k n b degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ l m : Tag k, ∀ f g : Flavor k,
    ∀ a b' : F → Binary, ∀ c d : Binary,
      ((∃ j, a j ≠ 0 ∨ b' j ≠ 0) ∨ c ≠ 0 ∨ d ≠ 0) →
        n ≤ 5 * (bilinearPart (ambientParity L a b' (selfGram hr hd M) c d) s t l m f g).rank

open scoped ENNReal

axiom uniform_of_restrictions {k n b degree r : ℕ} {F : Type} [Fintype F]
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (L : F → Moment k n b degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (hL : MixerGood L) (hM : SharpGood M) : UniformBinary hr hd L M

end Lax342547.BinaryMixers
end

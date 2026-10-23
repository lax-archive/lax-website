-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.QuadraticForm.Prod
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

def pointMoment (p : Label → Coord → Binary) (s : Label) (z : Base → Binary) :
    Matrix (Coord × Option Base) (Coord × Option Base) Binary :=
  fun i j => point p s z i * point p s z j

def momentSpace (p : Label → Coord → Binary) (A : Set Base) :
    Submodule Binary (Matrix (Coord × Option Base) (Coord × Option Base) Binary) :=
  Submodule.span Binary {w | ∃ s z, (∀ i, i ∉ A → z i = 0) ∧ w = pointMoment p s z}

end Lax342547.MomentSpace
end

-- Lax342547.GradientForm
section
namespace Lax342547.GradientForm

open Lax342547.MomentSpace

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

def rankOne (a b : X →ₗ[Binary] Binary) : LinearMap.BilinForm Binary X := a.smulRight b

def form (a : X →ₗ[Binary] Binary) (aTag bTag : Tag → X →ₗ[Binary] Binary)
    (B : LinearMap.BilinForm Binary X) : LinearMap.BilinForm Binary X :=
  rankOne a a + (∑ t, (rankOne (aTag t) (bTag t) + rankOne (bTag t) (aTag t))) + B + B.flip

end Lax342547.GradientForm
end

-- Lax342547.CutProfiles
section
namespace Lax342547.CutProfiles

open Lax342547.MomentSpace

def Component (Tag : Type) := {e : Finset Tag // e.card = 2}

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

def cutMap : (Tag → V) →ₗ[Binary] (Component Tag → V) where
  toFun w e := ∑ t ∈ e.val, w t
  map_add' w v := by ext e; simp [Finset.sum_add_distrib]
  map_smul' c w := by ext e; simp [Finset.smul_sum]

def representatives (W : Tag → Submodule Binary V) : Submodule Binary (Tag → V) :=
  Submodule.pi Set.univ W

end Lax342547.CutProfiles
end

-- Lax342547.TagGeometry
section
namespace Lax342547.TagGeometry.commonBase
end Lax342547.TagGeometry.commonBase

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

def interval (k : ℕ) (d : Tag k) : Finset (Tag k) :=
  Finset.univ.image (fun i : Fin k => d + (i.val + 1 : ℕ))

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

def allowedBase (k n : ℕ) (l : Tag k) : Set (Base k n)
  | Sum.inl ((d, _), _) => l ∈ interval k d
  | Sum.inr _ => True

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

def matrixPair {I : Type} [Fintype I] (E : Matrix I I Binary) :
    Matrix I I Binary →ₗ[Binary] Binary :=
  ∑ i, ∑ j, E i j • matrixEntry i j

end Lax342547.ConcreteGeometry
end

-- Lax342547.RawFrames
section
namespace Lax342547.RawFrames.Frame
end Lax342547.RawFrames.Frame

namespace Lax342547.RawFrames

open Lax342547.MomentSpace

variable (B H N : Type) [Fintype B] [Fintype H] [Fintype N]

variable {B H N}

def sandwich (P Q : Matrix N B Binary) : Matrix B B Binary →ₗ[Binary] Matrix N N Binary where
  toFun Z := P * Z * Q.transpose
  map_add' Z W := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.smul_mul]

variable {Comp : Type}

end Lax342547.RawFrames
end

-- Lax342547.ConcreteCut
section
namespace Lax342547.ConcreteCut

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles

noncomputable instance (k : ℕ) : Fintype (Component (Tag k)) := by
  classical
  exact inferInstanceAs (Fintype {e : Finset (Tag k) // e.card = 2})

def tagSpace (k n b degree : ℕ) (l : Tag k) : Submodule Binary (Moment k n b degree) :=
  momentSpace selectorEval (allowedBase k n l)

abbrev Representation (k n b degree : ℕ) := representatives (tagSpace k n b degree)

def representationCut (k n b degree : ℕ) :
    Representation k n b degree →ₗ[Binary] (Component (Tag k) → Moment k n b degree) :=
  cutMap.comp (representatives (tagSpace k n b degree)).subtype

abbrev Profile (k n b degree : ℕ) := LinearMap.range (representationCut k n b degree)

def representativeAt {k n b degree : ℕ} (l : Tag k) :
    Representation k n b degree →ₗ[Binary] Moment k n b degree :=
  (LinearMap.proj l).comp (representatives (tagSpace k n b degree)).subtype

def ordinarySum {k n b degree r : ℕ} (hr : 2 * r ≤ n) (t : Tag k) :
    Representation k n b degree →ₗ[Binary] Binary :=
  ∑ l : Tag k, ∑ d : Tag k, (blockTester hr (ordinary d t)).comp (representativeAt l)

noncomputable def sharedSum {k n b degree r : ℕ} (hr : 2 * r ≤ n) (t : Tag k) :
    Representation k n b degree →ₗ[Binary] Binary := by
  classical
  exact ∑ l ∈ Finset.univ.erase t, (blockTester hr shared).comp (representativeAt l)

structure Testers {k n b degree r : ℕ} (hr : 2 * r ≤ n) where
  aTag : Tag k → Profile k n b degree →ₗ[Binary] Binary
  bTag : Tag k → Profile k n b degree →ₗ[Binary] Binary
  ordinary_formula : ∀ t w, aTag t ((representationCut k n b degree).rangeRestrict w) = ordinarySum hr t w
  shared_formula : ∀ t w, bTag t ((representationCut k n b degree).rangeRestrict w) = sharedSum hr t w

def Testers.role {k n b degree r : ℕ} {hr : 2 * r ≤ n} (D : Testers (k := k) (b := b) (degree := degree) hr) :
    Profile k n b degree →ₗ[Binary] Binary := ∑ t, D.aTag t

def profileAt {k n b degree : ℕ} (e : Component (Tag k)) :
    Profile k n b degree →ₗ[Binary] Moment k n b degree :=
  (LinearMap.proj e).comp (LinearMap.range (representationCut k n b degree)).subtype

def matrixPairing {I : Type} [Fintype I] : LinearMap.BilinForm Binary (Matrix I I Binary) where
  toFun := matrixPair
  map_add' x y := by
    ext w
    simp [matrixPair, Matrix.add_apply, add_smul, Finset.sum_add_distrib, LinearMap.sum_apply]
  map_smul' a x := by
    ext w
    simp [matrixPair, Matrix.smul_apply, mul_smul, Finset.smul_sum, LinearMap.sum_apply]

noncomputable def mixingForm {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) :
    LinearMap.BilinForm Binary (Profile k n b degree) :=
  ∑ j, ∑ e, ∑ f, matrixPairing.comp (profileAt e)
    ((RawFrames.sandwich (L j e f) (R j e f)).comp (profileAt f))

noncomputable def gradient {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) :
    LinearMap.BilinForm Binary (Profile k n b degree) :=
  GradientForm.form D.role D.aTag D.bTag (mixingForm L R)

end Lax342547.ConcreteCut
end

-- Lax342547.Atoms
section
namespace Lax342547.Atoms.testerSummary
end Lax342547.Atoms.testerSummary

namespace Lax342547.Atoms

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.ConcreteCut

noncomputable def atomRepresentation {k n b degree : ℕ} (l : Tag k)
    (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) : Representation k n b degree := by
  classical
  refine ⟨Pi.single l (pointMoment selectorEval s z), ?_⟩
  intro t _
  by_cases ht : l = t
  · subst t
    simp only [Pi.single_eq_same]
    exact Submodule.subset_span ⟨s, z, hz, rfl⟩
  · simp [ht]

noncomputable def atom {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) : Profile k n b degree :=
  (representationCut k n b degree).rangeRestrict (atomRepresentation l s z hz)

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

noncomputable def varyBlock {k n : ℕ} (z : Base k n → Binary) (c : Fin n → Base k n)
    (v : Fin n → Binary) : Base k n → Binary := by
  classical
  exact fun i => z i + ∑ j, if c j = i then v j else 0

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
end Lax342547.OrderedMixerLaw
end

-- Lax342547.SharpMixerLaw
section
namespace Lax342547.SharpMixerLaw
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

def UniformBinary {k n b degree r : ℕ} {F : Type} [Fintype F]
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (L : F → Moment k n b degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary) : Prop :=
  ∀ s t : Fin b → Binary, s ≠ t → ∀ l m : Tag k, ∀ f g : Flavor k,
    ∀ a b' : F → Binary, ∀ c d : Binary,
      ((∃ j, a j ≠ 0 ∨ b' j ≠ 0) ∨ c ≠ 0 ∨ d ≠ 0) →
        n ≤ 5 * (bilinearPart (ambientParity L a b' (selfGram hr hd M) c d) s t l m f g).rank

open scoped ENNReal

end Lax342547.BinaryMixers
end

-- Lax342547.CoordinateCounts
section
namespace Lax342547.CoordinateCounts
end Lax342547.CoordinateCounts
end

-- Lax342547.SymmetricFactorization
section
namespace Lax342547.SymmetricFactorization
end Lax342547.SymmetricFactorization
end

-- Lax342547.ProfileCounting
section
namespace Lax342547.ProfileCounting
end Lax342547.ProfileCounting
end

-- Lax342547.CorankCounting
section
namespace Lax342547.CorankCounting
end Lax342547.CorankCounting
end

-- Lax342547.MixerCompatibility
section
namespace Lax342547
end Lax342547

namespace Lax342547.MixerCompatibility
end Lax342547.MixerCompatibility
end

-- Lax342547.MixerRowLaw
section
namespace Lax342547.MixerRowLaw
end Lax342547.MixerRowLaw
end

-- Lax342547.FormalQuadratic
section
namespace Lax342547.FormalQuadratic

variable {K B : Type} [Field K] [Fintype B] {V : B → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

open Lax342547.MomentSpace

def affinePolar {U : Type} [AddCommGroup U] (f : U → Binary) (u v : U) : Binary :=
  f (u + v) + f u + f v + f 0

def polarMatrix {I : Type} [DecidableEq I] (f : (I → Binary) → Binary) : Matrix I I Binary :=
  fun i j => affinePolar f (Pi.single i 1) (Pi.single j 1)

end Lax342547.FormalQuadratic
end

-- Lax342547.RestrictionRank
section
namespace Lax342547
end Lax342547

namespace Lax342547.RestrictionRank
end Lax342547.RestrictionRank
end

-- Lax342547.UnaryMixer
section
namespace Lax342547.UnaryMixer.blockRank
end Lax342547.UnaryMixer.blockRank

namespace Lax342547.UnaryMixer

open Lax342547.MomentSpace

variable {E I : Type} [Fintype E] [Fintype I]

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut

open Lax342547.CutProfiles Lax342547.Atoms

noncomputable def atomAlongZ {k n b degree : ℕ}
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0)
    (v : Fin n → Binary) : Profile k n b degree :=
  atom l s (AtomDirections.varyBlock z free v) (by
    classical
    intro i hi
    cases i with
    | inl i => simpa [AtomDirections.varyBlock, free] using hz (.inl i) hi
    | inr i => exact False.elim (hi trivial))

end Lax342547.UnaryMixer
end

-- Lax342547.UnaryRowLaw
section
namespace Lax342547.UnaryRowLaw.pack
end Lax342547.UnaryRowLaw.pack

namespace Lax342547.UnaryRowLaw

open Lax342547.MomentSpace Lax342547.UnaryMixer

variable {E I N : Type} [Fintype E] [Fintype I] [Fintype N]

abbrev Index (E : Type) (J : ℕ) := Bool × Fin J × E × E

open scoped ENNReal

def leftMixers {J : ℕ} (M : Index E J → Matrix I I Binary) : Fin J → E → E → Matrix I I Binary :=
  fun j e f => M (false, j, e, f)

def rightMixers {J : ℕ} (M : Index E J → Matrix I I Binary) : Fin J → E → E → Matrix I I Binary :=
  fun j e f => M (true, j, e, f)

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles

end Lax342547.UnaryRowLaw
end

-- Lax342547.UnaryMixers
section
namespace Lax342547.UnaryMixers

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.UnaryRowLaw

abbrev Test (k n b degree K : ℕ) :=
  {x : Profile k n b degree // ∑ e, (x.val e).rank ≤ K} × Tag k × (Fin b → Binary)

def UniformUnary {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (K s₀ : ℕ)
    (M : Index (Component (Tag k)) J → Moment k n b degree) : Prop :=
  ∀ x : Profile k n b degree, x ≠ 0 → (∑ e, (x.val e).rank ≤ K) → ∀ l s,
    ∃ W : Submodule Binary (Module.Dual Binary (Fin n → Binary)),
      Module.finrank Binary W ≤ 4 * J * (2 * k) * K ∧
      ∀ z : Base k n → Binary, ∀ hz : ∀ i, i ∉ allowedBase k n l → z i = 0,
        2 * (J - s₀) ≤ (FormalQuadratic.polarMatrix (fun v =>
          gradient D (leftMixers M) (rightMixers M) x (UnaryMixer.atomAlongZ l s z hz v))).rank ∧
        ∀ u v, (∀ a ∈ W, a u = a v) →
          gradient D (leftMixers M) (rightMixers M) x (UnaryMixer.atomAlongZ l s z hz u) =
            gradient D (leftMixers M) (rightMixers M) x (UnaryMixer.atomAlongZ l s z hz v)

open scoped ENNReal

noncomputable def threshold (k b degree J K s₀ : ℕ) : ℕ :=
  (K + 1) ^ Fintype.card (Component (Tag k)) * (2 * k + 1) * 2 ^ b *
    2 ^ ((∑ j ∈ Finset.range (degree + 1), b.choose j) * K + K * K +
      (2 * J * K ^ 2 + (s₀ + 1) * (4 * J * (2 * k) * K)))

end Lax342547.UnaryMixers
end

-- Lax342547.UniformMixers
section
namespace Lax342547.UniformMixers

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.UnaryRowLaw

noncomputable def threshold (k b degree J K s₀ : ℕ) : ℕ :=
  max 50 (UnaryMixers.threshold k b degree J K s₀ +
    2 ^ (2 * b + 2 * Fintype.card (Index (Component (Tag k)) J)) + 2 ^ (2 * b + 2))

axiom exists_uniform_mixers (k b degree J K s₀ : ℕ) (hk : 0 < k) (hd : 1 ≤ degree)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀)
    (n : ℕ) (hn : threshold k b degree J K s₀ ≤ n)
    (r₀ : ℕ) (hr : 2 * r₀ ≤ n) (D : Testers (k := k) (b := b) (degree := degree) hr) :
    ∃ L : Index (Component (Tag k)) J → Moment k n b degree,
      ∃ M : Fin b → Matrix (Fin n) (Fin n) Binary,
        UnaryMixers.UniformUnary D K s₀ L ∧ BinaryMixers.UniformBinary hr hd L M

end Lax342547.UniformMixers
end

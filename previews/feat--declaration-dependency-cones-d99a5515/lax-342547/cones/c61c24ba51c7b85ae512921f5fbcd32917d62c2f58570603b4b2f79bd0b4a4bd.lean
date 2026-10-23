-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.Probability.Distributions.Uniform

-- Lax342547.HoleRelation
section
namespace Lax342547.HoleRelation

universe u v w

structure HoleData (Ω : Type u) (X : Type v) (V : Type w)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup V] [Module (ZMod 2) V] where
  a : X →ₗ[ZMod 2] ZMod 2
  T : LinearMap.BilinForm (ZMod 2) X
  symmetric : ∀ x y, T x y = T y x
  U : Ω → X →ₗ[ZMod 2] V
  injective : ∀ i, Function.Injective (U i)
  u : Ω → V →ₗ[ZMod 2] ZMod 2

variable {Ω : Type u} {X : Type v} {V : Type w}

variable [AddCommGroup X] [Module (ZMod 2) X]

variable [AddCommGroup V] [Module (ZMod 2) V]

def Hole (D : HoleData Ω X V) (i j : Ω) : Prop :=
  ∃ x y : X, D.U i x = D.U j y ∧
    (∀ z, D.u j (D.U i z) = D.a z + D.T x z) ∧
    (∀ z, D.u i (D.U j z) = D.a z + D.T y z) ∧
    D.a x + D.a y = 1

end Lax342547.HoleRelation
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
namespace Lax342547.RawFrames

open Lax342547.MomentSpace

variable (B H N : Type) [Fintype B] [Fintype H] [Fintype N]

structure Frame (E : Matrix B B Binary) where
  P : Matrix N B Binary
  Q : Matrix N B Binary
  X : Matrix N H Binary
  Y : Matrix N H Binary
  plus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => P.mulVec z.1 + X.mulVec z.2)
  minus_injective : Function.Injective
    (fun z : (B → Binary) × (H → Binary) => Q.mulVec z.1 + Y.mulVec z.2)
  gram : P.transpose * Q = E
  plus_annihilator : X.transpose * Q = 0
  minus_annihilator : P.transpose * Y = 0

variable {B H N}

abbrev FrameData := Matrix N B Binary × Matrix N B Binary × Matrix N H Binary × Matrix N H Binary

def frameData {E : Matrix B B Binary} (F : Frame B H N E) : FrameData (B := B) (H := H) (N := N) :=
  (F.P, F.Q, F.X, F.Y)

theorem frameData_injective {E : Matrix B B Binary} :
    Function.Injective (frameData (E := E) (H := H) (N := N)) := by
  intro F G h
  cases F
  cases G
  simp only [frameData, Prod.mk.injEq] at h
  obtain ⟨hP, hQ, hX, hY⟩ := h
  cases hP
  cases hQ
  cases hX
  cases hY
  rfl

noncomputable instance {E : Matrix B B Binary} : Fintype (Frame B H N E) :=
  by classical exact Fintype.ofInjective frameData frameData_injective

def sandwich (P Q : Matrix N B Binary) : Matrix B B Binary →ₗ[Binary] Matrix N N Binary where
  toFun Z := P * Z * Q.transpose
  map_add' Z W := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.smul_mul]

def contraction {E : Matrix B B Binary} (F : Frame B H N E) :
    Matrix N N Binary →ₗ[Binary] Binary where
  toFun Z := Matrix.trace (F.X * F.Y.transpose * Z)
  map_add' Z W := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c Z := by simp [Matrix.mul_smul, Matrix.trace_smul]

variable {Comp : Type}

def profileMap {E : Matrix B B Binary} (F : Comp → Frame B H N E) :
    (Comp → Matrix B B Binary) →ₗ[Binary] (Comp → Matrix N N Binary) where
  toFun x e := sandwich (F e).P (F e).Q (x e)
  map_add' x y := by ext e i j; simp
  map_smul' c x := by ext e i j; simp

def profileContraction [Fintype Comp] {E : Matrix B B Binary} (F : Comp → Frame B H N E) :
    (Comp → Matrix N N Binary) →ₗ[Binary] Binary :=
  ∑ e, (contraction (F e)).comp (LinearMap.proj e)

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

noncomputable instance (k : ℕ) : DecidableEq (Component (Tag k)) := Classical.decEq _

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

-- Lax342547.RawLaw
section
namespace Lax342547.RawLaw
end Lax342547.RawLaw
end

-- Lax342547.SampledGraph
section
namespace Lax342547
end Lax342547

namespace Lax342547.SampledGraph
end Lax342547.SampledGraph
end

-- Lax342547.ConcreteModel
section
namespace Lax342547.ConcreteModel

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

open Lax342547.CutProfiles Lax342547.ConcreteCut Lax342547.RawFrames

open Lax342547.HoleRelation Lax342547.SampledGraph

open scoped ENNReal

abbrev RawVertex {k n b degree r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (h N : ℕ) :=
  Component (Tag k) → Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)

abbrev Ambient (k N : ℕ) := Component (Tag k) → Matrix (Fin N) (Fin N) Binary

structure Model {k n b degree r J h N : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) where
  testers : Testers (k := k) (b := b) (degree := degree) hr
  frame : Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M)
  holes : HoleData (RawVertex (k := k) hr hd M h N) (Profile k n b degree) (Ambient k N)
  role_eq : holes.a = testers.role
  gradient_eq : holes.T = gradient testers L R
  embedding_eq : ∀ o, holes.U o = (profileMap o).comp (Profile k n b degree).subtype
  contraction_eq : ∀ o, holes.u o = profileContraction o
  hole_symmetric : ∀ {i j}, Hole holes i j → Hole holes j i
  law : PMF (RawVertex (k := k) hr hd M h N)
  law_uniform : ∀ o, law o = (Fintype.card (RawVertex (k := k) hr hd M h N) : ℝ≥0∞)⁻¹

axiom exists_model {k n b degree r J h N : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (hN : 2 * (Fintype.card (Coordinate k n b degree) + h) ≤ N) :
    Nonempty (Model (h := h) (N := N) hr hd M L R)

end Lax342547.ConcreteModel
end

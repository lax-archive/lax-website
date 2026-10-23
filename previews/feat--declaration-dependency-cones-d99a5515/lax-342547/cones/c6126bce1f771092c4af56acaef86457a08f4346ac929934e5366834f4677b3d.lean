-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

def SelectorCoordinates (b degree : ℕ) :=
  {S : Finset (Fin b) // S.card ≤ degree}

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.ExactPins
section
namespace Lax342547.ExactPins

open Lax342547.MomentSpace

def Pin (Axis I N : Type) :=
  Σ S : Axis → Submodule Binary (I → Binary), ∀ a, S a →ₗ[Binary] (N → Binary)

namespace Pin

variable {Axis I N : Type}

def space (P : Pin Axis I N) (a : Axis) : Submodule Binary (I → Binary) := P.1 a

end Pin

end Lax342547.ExactPins
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

-- Lax342547.RawLaw
section
namespace Lax342547.RawLaw
end Lax342547.RawLaw
end

-- Lax342547.FrameSymmetry
section
namespace Lax342547.FrameSymmetry.Change
end Lax342547.FrameSymmetry.Change

namespace Lax342547.FrameSymmetry

open Lax342547.MomentSpace Lax342547.RawFrames

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N] [DecidableEq N]

abbrev Injection (I N : Type) [Fintype I] :=
  {A : Matrix N I Binary // Function.Injective A.mulVec}

def plus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.P F.X, by
    intro x y h
    have h' := F.plus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

def minus {E : Matrix B B Binary} (F : Frame B H N E) : Injection (B ⊕ H) N :=
  ⟨Matrix.fromCols F.Q F.Y, by
    intro x y h
    have h' := F.minus_injective (a₁ := (x ∘ Sum.inl, x ∘ Sum.inr))
      (a₂ := (y ∘ Sum.inl, y ∘ Sum.inr)) (by simpa [Matrix.fromCols_mulVec] using h)
    funext i
    cases i with
    | inl b => exact congrFun (congrArg Prod.fst h') b
    | inr h => exact congrFun (congrArg Prod.snd h') h⟩

end Lax342547.FrameSymmetry
end

-- Lax342547.FiniteLinearLaw
section
namespace Lax342547.FiniteLinearLaw
end Lax342547.FiniteLinearLaw
end

-- Lax342547.AffineImages
section
namespace Lax342547.AffineImages
end Lax342547.AffineImages
end

-- Lax342547.GramColumns
section
namespace Lax342547.GramColumns
end Lax342547.GramColumns
end

-- Lax342547.ConditionalMinus
section
namespace Lax342547.ConditionalMinus
end Lax342547.ConditionalMinus
end

-- Lax342547.GramNormalization
section
namespace Lax342547.GramNormalization
end Lax342547.GramNormalization
end

-- Lax342547.InjectiveFrames
section
namespace Lax342547.InjectiveFrames
end Lax342547.InjectiveFrames
end

-- Lax342547.ProductImages
section
namespace Lax342547.ProductImages

open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.RawFrames

open scoped ENNReal

def jointMatrix {Draw I N : Type} (A : Draw → Matrix N I Binary) : Matrix N (Draw × I) Binary :=
  fun n j => A j.1 n j.2

end Lax342547.ProductImages
end

-- Lax342547.ProductMinusImages
section
namespace Lax342547.ProductMinusImages
end Lax342547.ProductMinusImages
end

-- Lax342547.ReferenceImages
section
namespace Lax342547.ReferenceImages
end Lax342547.ReferenceImages
end

-- Lax342547.ImageScale
section
namespace Lax342547.ImageScale
end Lax342547.ImageScale
end

-- Lax342547.ReferencePins
section
namespace Lax342547.ReferencePins

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

open Lax342547.ProductImages Lax342547.ExactPins

open scoped ENNReal

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]

def observationMatrix {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : Matrix N (Fin 2 × (B ⊕ H)) Binary :=
  if a.2 then jointMatrix (fun i => (plus (o i a.1)).val)
  else jointMatrix (fun i => (minus (o i a.1)).val)

def observation {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (a : Comp × Bool) : ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary) :=
  (observationMatrix o a).mulVecLin

end Lax342547.ReferencePins
end

-- Lax342547.ProjectedPins
section
namespace Lax342547.ProjectedPins

open Lax342547.MomentSpace Lax342547.ExactPins

def primalProjection {B H : Type} (i : Fin 2) :
    ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (B → Binary) where
  toFun v b := v (i, Sum.inl b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projected {Comp B H N : Type} (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (i : Fin 2) (a : Comp × Bool) : Submodule Binary (B → Binary) :=
  (P.space a).map (primalProjection i)

def tensorSpace {B : Type} (S T : Submodule Binary (B → Binary)) :
    Submodule Binary (Matrix B B Binary) :=
  Submodule.span Binary {M | ∃ v ∈ S, ∃ w ∈ T, M = Matrix.vecMulVec v w}

def effective {Comp B H N : Type} (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) : Submodule Binary X where
  carrier := {x | ∀ e, x.val e ∈ tensorSpace (projected P i (e, true)) (projected P i (e, false))}
  zero_mem' := fun _e => (tensorSpace _ _).zero_mem
  add_mem' := fun hx hy e => (tensorSpace _ _).add_mem (hx e) (hy e)
  smul_mem' := fun c _ hx e => (tensorSpace _ _).smul_mem c (hx e)

end Lax342547.ProjectedPins
end

-- Lax342547.TableSpaces
section
namespace Lax342547.TableSpaces

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins

def primalEmbedding {B H : Type} (i : Fin 2) :
    (B → Binary) →ₗ[Binary] ((Fin 2 × (B ⊕ H)) → Binary) where
  toFun v x := if x.1 = i then Sum.elim v (fun _ => 0) x.2 else 0
  map_add' v w := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]
  map_smul' c v := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]

def channelEmbedding {B H : Type} (i : Fin 2) :
    (H → Binary) →ₗ[Binary] ((Fin 2 × (B ⊕ H)) → Binary) where
  toFun v x := if x.1 = i then Sum.elim (fun _ => 0) v x.2 else 0
  map_add' v w := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]
  map_smul' c v := by ext ⟨j, b | h⟩ <;> by_cases hj : j = i <;> simp [hj]

def tableSpace {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) :
    Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary) where
  carrier := {v | ∀ i, primalProjection i v ∈ projected P i a}
  zero_mem' := fun i => (projected P i a).zero_mem
  add_mem' := fun hv hw i => (projected P i a).add_mem (hv i) (hw i)
  smul_mem' := fun c _ hv i => (projected P i a).smul_mem c (hv i)

end Lax342547.TableSpaces
end

-- Lax342547.SmallTables
section
namespace Lax342547.SmallTables

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

variable {Comp B H N : Type}

structure Table (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) where
  forward : ∀ e, tableSpace P (e, true) →ₗ[Binary] tableSpace Q (e, false) →ₗ[Binary] Binary
  reverse : ∀ e, tableSpace Q (e, true) →ₗ[Binary] tableSpace P (e, false) →ₗ[Binary] Binary

def tableChannel (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) (i : Fin 2) :
    (H → Binary) →ₗ[Binary] tableSpace P a where
  toFun v := ⟨channelEmbedding i v, by
    intro j
    have hz : primalProjection j (channelEmbedding (B := B) i v) = 0 := by
      ext b
      simp [primalProjection, channelEmbedding]
    rw [hz]
    exact (projected P j a).zero_mem⟩
  map_add' v w := Subtype.ext ((channelEmbedding i).map_add v w)
  map_smul' c v := Subtype.ext ((channelEmbedding i).map_smul c v)

variable [Fintype N] {ΩA ΩB : Type}

end Lax342547.SmallTables
end

-- Lax342547.HoleRelation
section
namespace Lax342547
end Lax342547

namespace Lax342547.HoleRelation
end Lax342547.HoleRelation

namespace Lax342547.HoleRelation.HoleData
end Lax342547.HoleRelation.HoleData
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

abbrev Vector (k n b degree : ℕ) := Coordinate k n b degree → Binary

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

def blockForm {k n b degree r : ℕ} (h : 2 * r ≤ n) (c : Fin n → Base k n) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ ρ : Fin r, GradientForm.rankOne
    (LinearMap.proj (emptySelector b degree, some (c (pairLeft h ρ))))
    (LinearMap.proj (emptySelector b degree, some (c (pairRight h ρ))))

def sharpForm {k n b degree : ℕ} (h : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) :
    LinearMap.BilinForm Binary (Vector k n b degree) :=
  ∑ a : Fin b, ∑ i : Fin n, ∑ j : Fin n, M a i j •
    (GradientForm.rankOne (LinearMap.proj (bitSelector h a, some (sharp i)))
      (LinearMap.proj (emptySelector b degree, some (sharp j))) +
    GradientForm.rankOne (LinearMap.proj (emptySelector b degree, some (sharp i)))
      (LinearMap.proj (bitSelector h a, some (sharp j))))

def matrixPair {I : Type} [Fintype I] (E : Matrix I I Binary) :
    Matrix I I Binary →ₗ[Binary] Binary :=
  ∑ i, ∑ j, E i j • matrixEntry i j

end Lax342547.ConcreteGeometry
end

-- Lax342547.TensorContractions
section
namespace Lax342547.TensorContractions

open Lax342547.MomentSpace Lax342547.ProjectedPins Lax342547.ConcreteGeometry

variable {B H : Type} [Fintype B] [Fintype H]

noncomputable def ambient (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Matrix B B Binary →ₗ[Binary] Binary := by
  classical
  exact matrixPair (LinearMap.BilinForm.toMatrix' ((dotProductBilin Binary Binary).compl₁₂ f g))

noncomputable def extend {S : Submodule Binary (B → Binary)} (f : S →ₗ[Binary] (H → Binary)) :
    (B → Binary) →ₗ[Binary] (H → Binary) := Classical.choose f.exists_extend

noncomputable def contraction {S T : Submodule Binary (B → Binary)}
    (f : S →ₗ[Binary] (H → Binary)) (g : T →ₗ[Binary] (H → Binary)) :
    tensorSpace S T →ₗ[Binary] Binary :=
  (ambient (extend f) (extend g)).comp (tensorSpace S T).subtype

end Lax342547.TensorContractions
end

-- Lax342547.TableContractions
section
namespace Lax342547.TableContractions

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.TableSpaces Lax342547.SmallTables

structure CrossForms (Comp B H : Type) where
  forward : Comp → LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary)
  reverse : Comp → LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary)

def Extends {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (F : CrossForms Comp B H) (T : Table P Q) : Prop :=
  (∀ e (v : tableSpace P (e, true)) (w : tableSpace Q (e, false)),
    F.forward e v.val w.val = T.forward e v w) ∧
  (∀ e (v : tableSpace Q (e, true)) (w : tableSpace P (e, false)),
    F.reverse e v.val w.val = T.reverse e v w)

def primalToTable {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) (i : Fin 2) :
    projected P i a →ₗ[Binary] tableSpace P a where
  toFun v := ⟨primalEmbedding i v.val, by
    intro j
    by_cases hji : j = i
    · subst j
      simp [primalProjection, primalEmbedding]
    · have hz : primalProjection j (primalEmbedding (H := H) i v.val) = 0 := by
        ext b
        simp [primalProjection, primalEmbedding, hji]
      rw [hz]
      exact (projected P j a).zero_mem⟩
  map_add' v w := Subtype.ext ((primalEmbedding i).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((primalEmbedding i).map_smul c v.val)

noncomputable def plus {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (e : Comp) (i z : Fin 2) : projected P i (e, true) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => T.forward e (primalToTable P (e, true) i v)
        (tableChannel Q (e, false) z (Pi.single h 1))
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

noncomputable def minus {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (e : Comp) (i z : Fin 2) : projected P i (e, false) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => T.reverse e (tableChannel Q (e, true) z (Pi.single h 1))
        (primalToTable P (e, false) i v)
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

def component {Comp B H N : Type} (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (e : Comp) :
    effective X P i →ₗ[Binary] tensorSpace (projected P i (e, true)) (projected P i (e, false)) where
  toFun x := ⟨x.val.val e, x.property e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def starContraction {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) :
    effective X P i →ₗ[Binary] Binary :=
  ∑ e, (TensorContractions.contraction (plus T e i z) (minus T e i z)).comp (component X P i e)

end Lax342547.TableContractions
end

-- Lax342547.RawContractions
section
namespace Lax342547.RawContractions

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins Lax342547.ProjectedPins

open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions

open Lax342547.ReferencePins

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N] {E : Matrix B B Binary}

def rawForms (oA oB : Fin 2 → Comp → Frame B H N E) : CrossForms Comp B H :=
  ⟨fun e => (dotProductBilin Binary Binary).compl₁₂ (observation oA (e, true))
      (observation oB (e, false)),
    fun e => (dotProductBilin Binary Binary).compl₁₂ (observation oB (e, true))
      (observation oA (e, false))⟩

axiom raw_star_contraction [Fintype Comp] (oA oB : Fin 2 → Comp → Frame B H N E)
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (hT : TableContractions.Extends (rawForms oA oB) T)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) (x : effective X P i) :
    starContraction T X i z x = profileContraction (oB z) (profileMap (oA i) x.val.val)

end Lax342547.RawContractions
end

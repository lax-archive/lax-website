-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.DeriveFintype

-- Lax109476.LinearProgram
section
open scoped BigOperators

namespace Lax109476.LinearProgram

/-- Coefficients of a maximization program with `m` inequalities and `n`
nonnegative variables. -/
structure Program (K : Type) (m n : ℕ) where
  /-- The constraint matrix. -/
  A : Fin m → Fin n → K
  /-- The upper bounds on the constraint rows. -/
  b : Fin m → K
  /-- The coefficients of the maximized objective. -/
  c : Fin n → K

/-- The value of one constraint row at a primal point. -/
def rowValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) (i : Fin m) : K :=
  ∑ j, P.A i j * x j

/-- One component of the transposed matrix applied to a dual point. -/
def columnValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) (j : Fin n) : K :=
  ∑ i, P.A i j * y i

/-- The primal objective value. -/
def primalValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) : K :=
  ∑ j, P.c j * x j

/-- The dual objective value. -/
def dualValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) : K :=
  ∑ i, P.b i * y i

/-- A nonnegative primal point satisfies all row upper bounds. -/
def PrimalFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (x : Fin n → K) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, rowValue P x i ≤ P.b i

/-- A nonnegative dual point dominates every objective coefficient. -/
def DualFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ j, P.c j ≤ columnValue P y j

end Lax109476.LinearProgram
end

-- Lax109476.FarkasCertificate
section
namespace Lax109476.FarkasCertificate

open Lax109476.LinearProgram

/-- Nonnegative row multipliers certify an impossible negative upper bound. -/
def IsInfeasibilityCertificate {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ columnValue P y j) ∧ dualValue P y < 0

end Lax109476.FarkasCertificate
end

-- Lax109476.RecessionDirection
section
namespace Lax109476.RecessionDirection

open Lax109476.LinearProgram

/-- A nonnegative direction preserves every upper constraint and improves
the maximized objective. -/
def IsImprovingDirection {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (d : Fin n → K) : Prop :=
  (∀ j, 0 ≤ d j) ∧ (∀ i, rowValue P d i ≤ 0) ∧ 0 < primalValue P d

end Lax109476.RecessionDirection
end

-- Lax109476.RationalCertificates
section
namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

/-- A rational certificate for one of the three possible LP outcomes. -/
inductive Certificate (m n : ℕ)
  /-- Primal and dual points with matching objectives. -/
  | optimal (x : Fin n → ℚ) (y : Fin m → ℚ)
  /-- Separating nonnegative multipliers for an infeasible primal system. -/
  | infeasible (y : Fin m → ℚ)
  /-- A feasible base point and an improving recession direction. -/
  | unbounded (x d : Fin n → ℚ)

/-- The exact rational inequalities and equalities validating a certificate. -/
def IsValidCertificate {m n : ℕ} (P : Program ℚ m n) : Certificate m n → Prop
  | .optimal x y => PrimalFeasible P x ∧ DualFeasible P y ∧ primalValue P x = dualValue P y
  | .infeasible y => IsInfeasibilityCertificate P y
  | .unbounded x d => PrimalFeasible P x ∧ IsImprovingDirection P d

end Lax109476.RationalCertificates
end

-- Lax759944.BinaryWordEncoding
section
set_option backward.isDefEq.respectTransparency false

namespace Lax759944.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

/-- Encode one natural number, including the separator which begins it. -/
def encodeNat (n : ℕ) : List Symbol :=
  .separator :: n.bits.map (fun b => if b then .one else .zero)

/-- The canonical binary encoding of a finite list of natural numbers. -/
def encode (x : List ℕ) : List Symbol :=
  x.flatMap encodeNat

/-- The bit-size of a finite list of natural numbers. -/
def bitSize (x : List ℕ) : ℕ :=
  (encode x).length

end Lax759944.BinaryWordEncoding
end

-- Lax808846.Ram
section
namespace Lax808846
end Lax808846

namespace Lax808846.Ram
end Lax808846.Ram

namespace Lax808846.Ram.Instr
end Lax808846.Ram.Instr

namespace Lax808846.Ram.State
end Lax808846.Ram.State

namespace Lax808846.Ram.run
end Lax808846.Ram.run

namespace Lax808846.Ram.Instr.add
end Lax808846.Ram.Instr.add

namespace Lax808846.Ram.Instr.and
end Lax808846.Ram.Instr.and

namespace Lax808846.Ram.Instr.div
end Lax808846.Ram.Instr.div

namespace Lax808846.Ram.Instr.effect
end Lax808846.Ram.Instr.effect

namespace Lax808846.Ram.Instr.halt
end Lax808846.Ram.Instr.halt

namespace Lax808846.Ram.Instr.inputLength
end Lax808846.Ram.Instr.inputLength

namespace Lax808846.Ram.Instr.inputLoad
end Lax808846.Ram.Instr.inputLoad

namespace Lax808846.Ram.Instr.jeof
end Lax808846.Ram.Instr.jeof

namespace Lax808846.Ram.Instr.jump
end Lax808846.Ram.Instr.jump

namespace Lax808846.Ram.Instr.jzero
end Lax808846.Ram.Instr.jzero

namespace Lax808846.Ram.Instr.load
end Lax808846.Ram.Instr.load

namespace Lax808846.Ram.Instr.mul
end Lax808846.Ram.Instr.mul

namespace Lax808846.Ram.Instr.not
end Lax808846.Ram.Instr.not

namespace Lax808846.Ram.Instr.read
end Lax808846.Ram.Instr.read

namespace Lax808846.Ram.Instr.set
end Lax808846.Ram.Instr.set

namespace Lax808846.Ram.Instr.shiftl
end Lax808846.Ram.Instr.shiftl

namespace Lax808846.Ram.Instr.store
end Lax808846.Ram.Instr.store

namespace Lax808846.Ram.Instr.sub
end Lax808846.Ram.Instr.sub

namespace Lax808846.Ram.Instr.write
end Lax808846.Ram.Instr.write
end

-- Lax759944.RamPolytime
section
namespace Lax759944.RamPolytime
end Lax759944.RamPolytime
end

-- Lax109476.RationalEncoding
section
namespace Lax109476.RationalEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Encode a reduced rational by sign, magnitude, and denominator. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- Encode all coordinates of a rational vector in index order. -/
def encodeVector {n : ℕ} (x : Fin n → ℚ) : List ℕ :=
  (List.ofFn x).flatMap encodeRational

/-- Encode dimensions, row-major coefficients, row bounds, and objective. -/
def encodeProgram {m n : ℕ} (P : Program ℚ m n) : List ℕ :=
  [m, n] ++ (List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap encodeRational ++
    encodeVector P.b ++ encodeVector P.c

/-- Encode the outcome tag and all rational certificate coordinates. -/
def encodeCertificate {m n : ℕ} : Certificate m n → List ℕ
  | .optimal x y => [0] ++ encodeVector x ++ encodeVector y
  | .infeasible y => [1] ++ encodeVector y
  | .unbounded x d => [2] ++ encodeVector x ++ encodeVector d

end Lax109476.RationalEncoding
end

-- Lax109476.SmallCertificates
section
namespace Lax109476.SmallCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding

open Lax759944.BinaryWordEncoding

/-- All rational LP outcomes have certificates of uniformly polynomial bit size. -/
axiom exists_polynomial_size_certificate :
  ∃ C k : ℕ, 0 < C ∧ ∀ (m n : ℕ) (P : Program ℚ m n),
    ∃ certificate : Certificate m n, IsValidCertificate P certificate ∧
      bitSize (encodeCertificate certificate) ≤ C * (bitSize (encodeProgram P) + 1) ^ k

end Lax109476.SmallCertificates
end

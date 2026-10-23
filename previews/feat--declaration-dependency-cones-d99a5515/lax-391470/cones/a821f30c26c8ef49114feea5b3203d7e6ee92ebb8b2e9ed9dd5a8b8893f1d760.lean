-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Real.Basic

-- Lax391470.Scheduling
section
namespace Lax391470.Scheduling

/-- An instance of single machine scheduling with release times and deadlines: `jobs`
jobs, each with a release time, a deadline and a processing time. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The release time `r i` of job `i`. -/
  r : Fin jobs → ℤ
  /-- The deadline `d i` of job `i`. -/
  d : Fin jobs → ℤ
  /-- The processing time `p i` of job `i`. -/
  p : Fin jobs → ℕ

namespace Instance

variable (I : Instance)

/-- A schedule assigns a start time to every job. -/
abbrev Schedule := Fin I.jobs → ℤ

variable {I}

/-- A schedule is *feasible* if every job runs inside its availability interval and no two
jobs run at the same time. -/
def Feasible (t : I.Schedule) : Prop :=
  (∀ i, I.r i ≤ t i ∧ t i + I.p i ≤ I.d i) ∧
  (∀ i j, i ≠ j → t i + I.p i ≤ t j ∨ t j + I.p j ≤ t i)

variable (I)

/-- `I` admits a feasible schedule. -/
def Schedulable : Prop := ∃ t : I.Schedule, Feasible t

/-- Every processing time of `I` is `p` or `q`. -/
def LengthsIn (p q : ℕ) : Prop := ∀ i, I.p i = p ∨ I.p i = q

end Instance

end Lax391470.Scheduling
end

-- Lax391470.AuxiliaryProblem
section
namespace Lax391470.AuxiliaryProblem

open Lax391470.Scheduling

/-- The data of an instance of `AUX(p, q)`: ordinary jobs, each long or short, and
`pairs` connected pairs of pending jobs with an early and a late deadline each. -/
structure Instance where
  /-- The number of ordinary jobs. -/
  ordinary : ℕ
  /-- The release time of an ordinary job. -/
  r : Fin ordinary → ℕ
  /-- The deadline of an ordinary job. -/
  d : Fin ordinary → ℕ
  /-- Whether an ordinary job is long (of length `p`) rather than short (of length `q`). -/
  long : Fin ordinary → Bool
  /-- The number `N` of connected pairs of pending jobs. -/
  pairs : ℕ
  /-- The early deadline `d'_{p,i}` of the `i`-th long pending job. -/
  longEarly : Fin pairs → ℕ
  /-- The late deadline `d_{p,i}` of the `i`-th long pending job. -/
  longDue : Fin pairs → ℕ
  /-- The early deadline `d'_{q,i}` of the `i`-th short pending job. -/
  shortEarly : Fin pairs → ℕ
  /-- The late deadline `d_{q,i}` of the `i`-th short pending job. -/
  shortDue : Fin pairs → ℕ

namespace Instance

variable (A : Instance)

/-- The conditions on the deadlines of the pending jobs: within each sequence the
intervals between early and late deadline are ordered and do not intersect, and in every
connected pair the long job is the more urgent. -/
structure Ordered : Prop where
  /-- `d'_{p,i} ≤ d_{p,i}`. -/
  longEarly_le : ∀ i, A.longEarly i ≤ A.longDue i
  /-- `d_{p,i} ≤ d'_{p,i+1}`. -/
  longDue_le : ∀ i j : Fin A.pairs, (i : ℕ) + 1 = j → A.longDue i ≤ A.longEarly j
  /-- `d'_{q,i} ≤ d_{q,i}`. -/
  shortEarly_le : ∀ i, A.shortEarly i ≤ A.shortDue i
  /-- `d_{q,i} ≤ d'_{q,i+1}`. -/
  shortDue_le : ∀ i j : Fin A.pairs, (i : ℕ) + 1 = j → A.shortDue i ≤ A.shortEarly j
  /-- `d_{p,i} ≤ d'_{q,i}`. -/
  longDue_le_shortEarly : ∀ i, A.longDue i ≤ A.shortEarly i

/-- The scheduling instance underlying `A` at the job lengths `p` and `q`: the ordinary
jobs, then the long pending jobs, then the short pending jobs, the pending jobs released
at `0` and due at their late deadlines. -/
def toInstance (p q : ℕ) : Scheduling.Instance where
  jobs := A.ordinary + A.pairs + A.pairs
  r j := if h : (j : ℕ) < A.ordinary then A.r ⟨j, h⟩ else 0
  d j :=
    if h : (j : ℕ) < A.ordinary then A.d ⟨j, h⟩
    else if h' : (j : ℕ) < A.ordinary + A.pairs then
      A.longDue ⟨j - A.ordinary, by omega⟩
    else A.shortDue ⟨j - A.ordinary - A.pairs, by have := j.isLt; omega⟩
  p j :=
    if h : (j : ℕ) < A.ordinary then (if A.long ⟨j, h⟩ then p else q)
    else if (j : ℕ) < A.ordinary + A.pairs then p
    else q

/-- The `i`-th long pending job, as a job of the underlying instance. -/
def longJob (p q : ℕ) (i : Fin A.pairs) : Fin (A.toInstance p q).jobs :=
  ⟨A.ordinary + i, by have := i.isLt; simp only [toInstance]; omega⟩

/-- The `i`-th short pending job, as a job of the underlying instance. -/
def shortJob (p q : ℕ) (i : Fin A.pairs) : Fin (A.toInstance p q).jobs :=
  ⟨A.ordinary + A.pairs + i, by have := i.isLt; simp only [toInstance]; omega⟩

variable {A}

/-- A schedule *solves* `A` at the lengths `p` and `q`: it is feasible, and in every
connected pair the long job completes by its early deadline or the short one does. -/
def Solves (p q : ℕ) (t : (A.toInstance p q).Schedule) : Prop :=
  Scheduling.Instance.Feasible t ∧
  ∀ i : Fin A.pairs,
    t (A.longJob p q i) + p ≤ A.longEarly i ∨ t (A.shortJob p q i) + q ≤ A.shortEarly i

variable (A)

/-- `A` has a solution at the lengths `p` and `q`. -/
def Solvable (p q : ℕ) : Prop := ∃ t, A.Solves p q t

end Instance

end Lax391470.AuxiliaryProblem
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

end Lax434930.PolynomialTime
end

-- Lax391470.BinaryEncoding
section
namespace Lax391470.BinaryEncoding

open Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An integer as a binary word: one bit for the sign, then the absolute value. -/
def encodeInt (z : ℤ) : Word := decide (z < 0) :: encodeNat z.natAbs

/-- A scheduling instance as a binary word. -/
def encodeInstance (I : Scheduling.Instance) : Word :=
  encodeNat I.jobs ++
    (List.finRange I.jobs).flatMap fun j =>
      encodeInt (I.r j) ++ encodeInt (I.d j) ++ encodeNat (I.p j)

/-- An instance of the auxiliary problem as a binary word. -/
def encodeAux (A : AuxiliaryProblem.Instance) : Word :=
  encodeNat A.ordinary ++ encodeNat A.pairs ++
    ((List.finRange A.ordinary).flatMap fun o =>
      encodeNat (A.r o) ++ encodeNat (A.d o) ++ [A.long o]) ++
    (List.finRange A.pairs).flatMap fun i =>
      encodeNat (A.longEarly i) ++ encodeNat (A.longDue i) ++
        encodeNat (A.shortEarly i) ++ encodeNat (A.shortDue i)

/-- **Scheduling on the lengths `{p, q}`**, as a language. -/
def TwoLengths (p q : ℕ) : Language :=
  {w | ∃ I : Scheduling.Instance, encodeInstance I = w ∧ I.LengthsIn p q ∧ I.Schedulable}

/-- **The auxiliary problem `AUX(p, q)`**, as a language. -/
def AUX (p q : ℕ) : Language :=
  {w | ∃ A : AuxiliaryProblem.Instance, encodeAux A = w ∧ A.Ordered ∧ A.Solvable p q}

end Lax391470.BinaryEncoding
end

-- Lax391470.StackedConstruction
section
namespace Lax391470.StackedConstruction
end Lax391470.StackedConstruction

namespace Lax391470.StackedConstruction.inst
end Lax391470.StackedConstruction.inst
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075.Reductions

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

def ManyOne (A B : Language) : Prop :=
  ∃ f : Word → Word, Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ x, x ∈ A ↔ f x ∈ B

end Lax429075.Reductions
end

-- Lax391470.Lemma1
section
namespace Lax391470.Lemma1

open Lax391470.BinaryEncoding Lax434930.PolynomialTime Lax429075.Reductions

/-- **Lemma 1.** For job lengths `p > q ≥ 1`, `AUX(p, q)` is polynomial-time reducible to
scheduling on the lengths `{p, q}`. -/
axiom aux_manyOne_twoLengths (p q : ℕ) (hq : 0 < q) (hqp : q < p) :
    ManyOne (AUX p q) (TwoLengths p q)

end Lax391470.Lemma1
end

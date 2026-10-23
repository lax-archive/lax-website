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
end Lax391470.AuxiliaryProblem

namespace Lax391470.AuxiliaryProblem.Instance
end Lax391470.AuxiliaryProblem.Instance

namespace Lax391470.AuxiliaryProblem.Instance.Ordered
end Lax391470.AuxiliaryProblem.Instance.Ordered
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

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

/-- **Scheduling on the lengths `{p, q}`**, as a language. -/
def TwoLengths (p q : ℕ) : Language :=
  {w | ∃ I : Scheduling.Instance, encodeInstance I = w ∧ I.LengthsIn p q ∧ I.Schedulable}

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
namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

end Lax434930.Certificates
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax391470.Lemma1
section
namespace Lax391470.Lemma1
end Lax391470.Lemma1
end

-- Lax429075.CNF
section
namespace Lax429075
end Lax429075

namespace Lax429075.CNF
end Lax429075.CNF

namespace Lax429075.CNF.Literal
end Lax429075.CNF.Literal
end

-- Lax391470.SatConstruction
section
namespace Lax391470.SatConstruction
end Lax391470.SatConstruction

namespace Lax391470.SatConstruction.ordRelease
end Lax391470.SatConstruction.ordRelease
end

-- Lax429075.Encoding
section
namespace Lax429075.Encoding
end Lax429075.Encoding

namespace Lax429075.Encoding.decodeCNF
end Lax429075.Encoding.decodeCNF

namespace Lax429075.Encoding.encodeList
end Lax429075.Encoding.encodeList

namespace Lax429075.Encoding.parseList
end Lax429075.Encoding.parseList

namespace Lax429075.Encoding.parseLiteral
end Lax429075.Encoding.parseLiteral

namespace Lax429075.Encoding.parseNat
end Lax429075.Encoding.parseNat
end

-- Lax429075.Satisfiability
section
namespace Lax429075.Satisfiability
end Lax429075.Satisfiability
end

-- Lax391470.Lemma2
section
namespace Lax391470.Lemma2
end Lax391470.Lemma2

namespace Lax391470.Lemma2.reduce
end Lax391470.Lemma2.reduce
end

-- Lax391470.Theorem1
section
namespace Lax391470.Theorem1

open Lax391470.BinaryEncoding Lax434930.PolynomialTime

open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- Scheduling on the lengths `{p, q}` belongs to NP. -/
axiom twoLengths_mem_NP (p q : ℕ) : TwoLengths p q ∈ NP

end Lax391470.Theorem1
end

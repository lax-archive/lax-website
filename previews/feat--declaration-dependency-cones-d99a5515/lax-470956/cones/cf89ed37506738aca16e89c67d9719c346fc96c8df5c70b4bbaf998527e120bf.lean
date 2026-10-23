-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

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

-- Lax470956.Scheduling
section
namespace Lax470956.Scheduling

/-- An instance of interval scheduling with eligible machine sets: `jobs` jobs on
`machines` machines, each job with a processing time, a deadline, a weight, and the set
of machines allowed to run it. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of machines. -/
  machines : ℕ
  /-- The processing time `p j` of job `j`. -/
  p : Fin jobs → ℕ
  /-- The deadline `d j` of job `j`. -/
  d : Fin jobs → ℕ
  /-- The weight `w j` of job `j`. -/
  w : Fin jobs → ℕ
  /-- The machines eligible to run job `j`. -/
  eligible : Fin jobs → Finset (Fin machines)
  /-- Every job takes at least one time unit. -/
  p_pos : ∀ j, 0 < p j
  /-- Every job fits before its deadline. -/
  p_le_d : ∀ j, p j ≤ d j

namespace Instance

variable (I : Instance)

variable {I}

variable (I)

end Instance

end Lax470956.Scheduling
end

-- Lax470956.BinaryEncoding
section
namespace Lax470956.BinaryEncoding

open Lax470956.Scheduling Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. The unary prefix makes the code self-delimiting. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An instance as a binary word: the two counts, the processing times, the deadlines,
the weights, and the eligibility matrix in row order. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.jobs ++ encodeNat I.machines ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.p j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.d j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.w j)) ++
    (List.finRange I.jobs).flatMap
      (fun j => (List.finRange I.machines).map fun i => decide (i ∈ I.eligible j))

end Lax470956.BinaryEncoding
end

-- Lax470956.NPHardness
section
namespace Lax470956.NPHardness

open Lax470956.Scheduling Lax470956.BinaryEncoding

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A property of scheduling instances: a decision problem on them. -/
abbrev Problem := Instance → Prop

/-- `Q` is **NP-hard**: every language in NP reduces to it in polynomial time. -/
def NPHard (Q : Problem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance,
      Nonempty (Turing.TM2ComputableInPolyTime id encodeInstance f) ∧
      ∀ x, x ∈ A ↔ Q (f x)

end Lax470956.NPHardness
end

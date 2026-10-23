-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
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

-- Lax496464.FlowShop
section
namespace Lax496464.FlowShop.Instance.JITSchedule
end Lax496464.FlowShop.Instance.JITSchedule

namespace Lax496464.FlowShop

/-- An instance of the two-stage flexible flow shop: `jobs` jobs, `machines` identical
second-stage machines, and for each job a preprocessing time, a processing time, a due
date and a weight. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of identical second-stage machines. -/
  machines : ℕ
  /-- The first-stage (preprocessing) time `p j` of job `j`. -/
  p : Fin jobs → ℕ
  /-- The second-stage (processing) time `q j` of job `j`. -/
  q : Fin jobs → ℕ
  /-- The due date `d j` of job `j`. -/
  d : Fin jobs → ℕ
  /-- The weight `w j` of job `j`. -/
  w : Fin jobs → ℕ

namespace Instance

variable (I : Instance)

variable {I}

variable (I)

end Instance

end Lax496464.FlowShop
end

-- Lax496464.BinaryEncoding
section
namespace Lax496464.BinaryEncoding

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. The unary prefix makes the code self-delimiting. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An instance as a binary word: the two counts, then the preprocessing times, the
processing times, the due dates and the weights. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.jobs ++ encodeNat I.machines ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.p j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.q j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.d j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.w j))

/-- An instance together with a threshold, as a binary word. -/
def encodeDecisionInstance (I : Instance) (W : ℕ) : Word :=
  encodeInstance I ++ encodeNat W

/-- The largest number appearing in an instance. A reduction witnesses *strong*
NP-hardness when this stays polynomial in the length of its input. -/
def maxNumber (I : Instance) : ℕ :=
  ((List.finRange I.jobs).map fun j =>
      max (max (I.p j) (I.q j)) (max (I.d j) (I.w j))).foldr max (max I.jobs I.machines)

end Lax496464.BinaryEncoding
end

-- Lax496464.NPHardness
section
namespace Lax496464.NPHardness

open Lax496464.FlowShop Lax496464.BinaryEncoding

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A decision problem on instances with a threshold. -/
abbrev Problem := Instance → ℕ → Prop

/-- `Q` is **strongly NP-hard**: it is NP-hard by a reduction whose emitted instances
have all their numbers, and their threshold, bounded by a fixed polynomial in the length
of the input. -/
def StronglyNPHard (Q : Problem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ (f : Word → Instance × ℕ) (c : ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime id
        (fun z : Instance × ℕ => encodeDecisionInstance z.1 z.2) f) ∧
      (∀ x, max (maxNumber (f x).1) (f x).2 ≤ (x.length + 2) ^ c) ∧
      ∀ x, x ∈ A ↔ Q (f x).1 (f x).2

end Lax496464.NPHardness
end

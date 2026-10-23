-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Real.Basic

-- Lax391470.Scheduling
section
namespace Lax391470
end Lax391470

namespace Lax391470.Scheduling
end Lax391470.Scheduling

namespace Lax391470.Scheduling.Instance
end Lax391470.Scheduling.Instance
end

-- Lax391470.AuxiliaryProblem
section
namespace Lax391470.AuxiliaryProblem.Instance.Ordered
end Lax391470.AuxiliaryProblem.Instance.Ordered

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

variable {A}

variable (A)

end Instance

end Lax391470.AuxiliaryProblem
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

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

/-- An instance of the auxiliary problem as a binary word. -/
def encodeAux (A : AuxiliaryProblem.Instance) : Word :=
  encodeNat A.ordinary ++ encodeNat A.pairs ++
    ((List.finRange A.ordinary).flatMap fun o =>
      encodeNat (A.r o) ++ encodeNat (A.d o) ++ [A.long o]) ++
    (List.finRange A.pairs).flatMap fun i =>
      encodeNat (A.longEarly i) ++ encodeNat (A.longDue i) ++
        encodeNat (A.shortEarly i) ++ encodeNat (A.shortDue i)

end Lax391470.BinaryEncoding
end

-- Lax429075.CNF
section
namespace Lax429075.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

abbrev Clause := List Literal

abbrev Formula := List Clause

end Lax429075.CNF
end

-- Lax391470.SatConstruction
section
namespace Lax391470.SatConstruction

open Lax391470.AuxiliaryProblem Lax429075.CNF

variable (p q : ℕ) (F : Formula)

/-- The number `n` of variables: one more than the largest index occurring in `F`, and
`1` if no literal occurs. -/
def numVars : ℕ := (F.flatMap id).foldr (fun l n => max (l.index + 1) n) 1

/-- The number `m` of clauses. -/
def numClauses : ℕ := F.length

/-- The length `S` of a section. -/
def sectionLength : ℕ := p + 2 * q + numClauses F * (p + q) + 1 + q

/-- The start of section `s`. -/
def sectionStart (s : ℕ) : ℕ := sectionLength p q F * s

/-- The literal of section `s`: the sections run `x₀, ¬x₀, x₁, ¬x₁, …`. -/
def literalOf (s : ℕ) : Literal := ⟨s / 2, decide (s % 2 = 0)⟩

/-- The clause block of clause `j` in section `s` is *active*: the literal of the section
occurs in the clause. -/
def active (s j : ℕ) : Bool := decide (literalOf s ∈ F.getD j [])

/-- The start of the clause block of clause `j` in section `s`. -/
def clauseStart (s j : ℕ) : ℕ := sectionStart p q F s + p + 2 * q + j * (p + q)

/-- The early deadline of both pending jobs of a clause block. -/
def clauseEarly (s j : ℕ) : ℕ :=
  clauseStart p q F s j + (if active F s j then p + q else p + q - 1)

/-- The late deadline of both pending jobs of a clause block. -/
def clauseDue (s j : ℕ) : ℕ := clauseStart p q F s j + p + q + 1

/-- The number of ordinary jobs: three for every section, and the `2m` unconnected
pending jobs. -/
def numOrdinary : ℕ := 6 * numVars F + 2 * numClauses F

/-- The release time of the ordinary job `o`. -/
def ordRelease (o : ℕ) : ℕ :=
  if o < 6 * numVars F then
    match o % 3 with
    | 0 => sectionStart p q F (o / 3) + (if (o / 3) % 2 = 0 then 1 else q + 1)
    | 1 => sectionStart p q F (o / 3)
    | _ => sectionStart p q F (o / 3) + sectionLength p q F - q
  else 0

/-- The deadline of the ordinary job `o`. -/
def ordDue (o : ℕ) : ℕ :=
  if o < 6 * numVars F then
    match o % 3 with
    | 0 => sectionStart p q F (o / 3) + (if (o / 3) % 2 = 0 then 2 * q else p + q)
    | 1 => sectionStart p q F (o / 3) + p + 2 * q + 1
    | _ => sectionStart p q F (o / 3) + sectionLength p q F
  else if o < 6 * numVars F + numClauses F then
    clauseEarly p q F (2 * numVars F - 1) (o - 6 * numVars F)
  else
    clauseEarly p q F 0 (o - 6 * numVars F - numClauses F)

/-- Whether the ordinary job `o` is long: the second ordinary job of a block of type `V⁻`,
and the unconnected long jobs of the last section. -/
def ordLong (o : ℕ) : Bool :=
  if o < 6 * numVars F then decide (o % 3 = 1 ∧ (o / 3) % 2 = 1)
  else decide (o < 6 * numVars F + numClauses F)

/-- The number `N = n + (2n - 1) m` of connected pairs. -/
def numPairs : ℕ := numVars F + (2 * numVars F - 1) * numClauses F

/-- The variable whose group the pair `i` belongs to. -/
def groupOf (i : ℕ) : ℕ := i / (1 + 2 * numClauses F)

/-- The position of the pair `i` in its group: `0` for the literal pair. -/
def posOf (i : ℕ) : ℕ := i % (1 + 2 * numClauses F)

/-- The section holding the long job of the clause pair `i`. -/
def pairSection (i : ℕ) : ℕ := 2 * groupOf F i + (posOf F i - 1) / numClauses F

/-- The clause of the clause pair `i`. -/
def pairClause (i : ℕ) : ℕ := (posOf F i - 1) % numClauses F

/-- The early deadline of the long job of pair `i`. -/
def longEarly (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i) + p + q + 1
  else clauseEarly p q F (pairSection F i) (pairClause F i)

/-- The late deadline of the long job of pair `i`. -/
def longDue (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i) + p + 2 * q
  else clauseDue p q F (pairSection F i) (pairClause F i)

/-- The early deadline of the short job of pair `i`, one section after the long job. -/
def shortEarly (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i + 1) + q
  else clauseEarly p q F (pairSection F i + 1) (pairClause F i)

/-- The late deadline of the short job of pair `i`. -/
def shortDue (i : ℕ) : ℕ :=
  if posOf F i = 0 then sectionStart p q F (2 * groupOf F i + 1) + p + 2 * q
  else clauseDue p q F (pairSection F i + 1) (pairClause F i)

/-- **The instance of `AUX(p, q)`** built from the formula `F`. -/
def inst : AuxiliaryProblem.Instance where
  ordinary := numOrdinary F
  r o := ordRelease p q F o
  d o := ordDue p q F o
  long o := ordLong F o
  pairs := numPairs F
  longEarly i := longEarly p q F i
  longDue i := longDue p q F i
  shortEarly i := shortEarly p q F i
  shortDue i := shortDue p q F i

end Lax391470.SatConstruction
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
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax429075.Encoding
section
namespace Lax429075.Encoding.encodeList
end Lax429075.Encoding.encodeList

namespace Lax429075.Encoding

open CNF Lax434930.PolynomialTime

def parseNat : Word → Option (ℕ × Word)
  | [] => none
  | false :: w => some (0, w)
  | true :: w => do
    let (n, rest) ← parseNat w
    pure (n + 1, rest)

def parseLiteral (w : Word) : Option (Literal × Word) := do
  let (n, rest) ← parseNat w
  match rest with
  | [] => none
  | sign :: tail => pure (⟨n, sign⟩, tail)

def parseList {α : Type} (parse : Word → Option (α × Word)) :
    ℕ → Word → Option (List α × Word)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: w => some ([], w)
  | fuel + 1, true :: w => do
    let (a, rest) ← parse w
    let (as, tail) ← parseList parse fuel rest
    pure (a :: as, tail)

def parseClause (w : Word) : Option (Clause × Word) := parseList parseLiteral w.length w

def decodeCNF (w : Word) : Option Formula := do
  let (F, rest) ← parseList parseClause w.length w
  if rest = [] then pure F else none

end Lax429075.Encoding
end

-- Lax429075.Satisfiability
section
namespace Lax429075.Satisfiability
end Lax429075.Satisfiability
end

-- Lax391470.Lemma2
section
namespace Lax391470.Lemma2

open Lax391470.BinaryEncoding Lax434930.PolynomialTime

open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- An instance of the auxiliary problem without a solution, when `q ≥ 1`: one ordinary
short job, released and due at time `0`. -/
def blocked : AuxiliaryProblem.Instance where
  ordinary := 1
  r _ := 0
  d _ := 0
  long _ := false
  pairs := 0
  longEarly := Fin.elim0
  longDue := Fin.elim0
  shortEarly := Fin.elim0
  shortDue := Fin.elim0

/-- **The reduction**, as a map on words: the encoding of a formula is sent to the
encoding of the instance built from it, and every other word to the encoding of
`blocked`. -/
def reduce (p q : ℕ) (w : Word) : Word :=
  match Lax429075.Encoding.decodeCNF w with
  | some F => encodeAux (SatConstruction.inst p q F)
  | none => encodeAux blocked

/-- **The reduction runs in polynomial time.** -/
axiom reduce_polyTime (p q : ℕ) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (reduce p q))

end Lax391470.Lemma2
end

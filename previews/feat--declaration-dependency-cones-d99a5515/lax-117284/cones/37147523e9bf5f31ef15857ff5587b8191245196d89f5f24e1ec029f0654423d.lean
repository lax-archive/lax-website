-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
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

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax429075.Satisfiability
section
namespace Lax429075.Satisfiability
end Lax429075.Satisfiability
end

-- Lax117284.TwoSatCNF
section
namespace Lax117284.TwoSatCNF

open Lax429075.CNF Lax429075.Encoding Lax429075.Satisfiability Lax434930.PolynomialTime

/-- The literals of a formula, in order of occurrence. -/
def literals (F : Formula) : List Literal := F.flatMap id

/-- The variables a formula mentions. -/
def vars (F : Formula) : Finset ℕ := ((literals F).map Literal.index).toFinset

/-- The number of distinct variables of a formula. -/
def varCount (F : Formula) : ℕ := (vars F).card

end Lax117284.TwoSatCNF
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

-- Lax808846.RamComputes
section
namespace Lax808846.RamComputes
end Lax808846.RamComputes
end

-- Lax117284.TwoSatRunningTime
section
namespace Lax117284.TwoSatRunningTime

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax117284.TwoSatCNF

open Lax808846.Ram Lax808846.RamComputes

/-- A list of numbers as a binary word: which entries are nonzero. -/
def bitsOf (x : List ℕ) : Word := x.map fun n => decide (n ≠ 0)

/-- The number of distinct variables of the formula a list of bits encodes, and `0` if it
encodes none. -/
def wordVarCount (x : List ℕ) : ℕ := ((decodeCNF (bitsOf x)).map varCount).getD 0

end Lax117284.TwoSatRunningTime
end

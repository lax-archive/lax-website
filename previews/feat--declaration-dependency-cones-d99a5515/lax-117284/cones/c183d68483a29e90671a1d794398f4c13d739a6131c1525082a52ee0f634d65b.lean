-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card

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

-- Lax429075.CNF
section
namespace Lax429075.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

abbrev Clause := List Literal

abbrev Formula := List Clause

abbrev Assignment := ℕ → Bool

def Literal.eval (l : Literal) (ρ : Assignment) : Bool :=
  if l.positive then ρ l.index else !(ρ l.index)

def eval (F : Formula) (ρ : Assignment) : Bool :=
  F.all fun C => C.any fun l => l.eval ρ

def Satisfiable (F : Formula) : Prop := ∃ ρ, eval F ρ = true

end Lax429075.CNF
end

-- Lax429075.Encoding
section
namespace Lax429075.Encoding.decodeCNF
end Lax429075.Encoding.decodeCNF

namespace Lax429075.Encoding.parseList
end Lax429075.Encoding.parseList

namespace Lax429075.Encoding.parseLiteral
end Lax429075.Encoding.parseLiteral

namespace Lax429075.Encoding.parseNat
end Lax429075.Encoding.parseNat

namespace Lax429075.Encoding

open CNF Lax434930.PolynomialTime

def encodeList {α : Type} (encode : α → Word) : List α → Word
  | [] => [false]
  | a :: as => true :: (encode a ++ encodeList encode as)

def encodeNat (n : ℕ) : Word := List.replicate n true ++ [false]

def encodeLiteral (l : Literal) : Word := encodeNat l.index ++ [l.positive]

def encodeClause : Clause → Word := encodeList encodeLiteral

def encodeCNF : Formula → Word := encodeList encodeClause

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

/-- A CNF formula is in **2-CNF** when every clause has at most two literals. -/
def IsTwoCNF (F : Formula) : Prop := ∀ C ∈ F, C.length ≤ 2

/-- **2-SAT**: the encodings of the satisfiable formulas in 2-CNF. It is `SAT` restricted to
the encodings of 2-CNF formulas. -/
def TwoSAT : Language := {w | ∃ F : Formula, encodeCNF F = w ∧ IsTwoCNF F ∧ Satisfiable F}

end Lax117284.TwoSatCNF
end

-- Lax117284.TwoSatInP
section
namespace Lax117284.TwoSatInP

open Lax434930.PolynomialTime Lax117284.TwoSatCNF

/-- **2-SAT ∈ P.** -/
axiom twoSAT_mem_P : TwoSAT ∈ P

end Lax117284.TwoSatInP
end

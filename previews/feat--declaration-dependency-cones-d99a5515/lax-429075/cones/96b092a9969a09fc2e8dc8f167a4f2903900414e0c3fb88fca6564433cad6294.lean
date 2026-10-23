-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

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

end Lax429075.Encoding
end

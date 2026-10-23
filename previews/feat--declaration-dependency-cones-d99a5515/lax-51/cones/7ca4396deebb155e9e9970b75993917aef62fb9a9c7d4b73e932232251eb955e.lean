-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype

-- Lax51.BinaryWordEncoding
section
namespace Lax51.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

end Lax51.BinaryWordEncoding
end

-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Int.Basic

-- Lax489179.IntegerEncoding
section
namespace Lax489179.IntegerEncoding.decodeOption
end Lax489179.IntegerEncoding.decodeOption

namespace Lax489179.IntegerEncoding

def encodeInt : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def encodeOption : Option ℤ → ℕ
  | none => 0
  | some z => encodeInt z + 1

end Lax489179.IntegerEncoding
end

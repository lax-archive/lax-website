-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Int.Basic

-- Lax489179.IntegerEncoding
section
namespace Lax489179.IntegerEncoding.decodeOption
end Lax489179.IntegerEncoding.decodeOption

namespace Lax489179.IntegerEncoding.encodeInt
end Lax489179.IntegerEncoding.encodeInt

namespace Lax489179.IntegerEncoding.encodeOption
end Lax489179.IntegerEncoding.encodeOption

namespace Lax489179.IntegerEncoding

def decodeInt (n : ℕ) : ℤ :=
  if n % 2 = 0 then .ofNat (n / 2) else .negSucc (n / 2)

end Lax489179.IntegerEncoding
end

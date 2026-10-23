-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax194892.MarkedSquaring
section
namespace Lax194892.MarkedSquaring

/-- Marked squaring: `n` copies of an input of length `n`, the first `i` letters
of the `i`-th copy underlined. -/
def markedSquare (A : Type) (w : List A) : List (A ⊕ A) :=
  ((List.range w.length).map
    (fun i => (w.take (i + 1)).map Sum.inl ++ (w.drop (i + 1)).map Sum.inr)).flatten

end Lax194892.MarkedSquaring
end

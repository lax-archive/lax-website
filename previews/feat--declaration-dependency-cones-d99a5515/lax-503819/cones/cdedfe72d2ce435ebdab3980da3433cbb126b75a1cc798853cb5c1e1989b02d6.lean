-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Language
import Mathlib.Data.List.Forall2

-- Lax503819.Words
section
namespace Lax503819.Words

def Below {A : Type} [LE A] (u v : List A) : Prop :=
  List.Forall₂ (· ≤ ·) u v

def upwardClosure {A : Type} [LE A] (L : Language A) : Language A :=
  {v | ∃ u ∈ L, Below u v}

end Lax503819.Words
end

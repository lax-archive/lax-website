-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax132576.StringHomomorphisms
section
namespace Lax132576.StringHomomorphisms

/-- The string homomorphism that applies `φ` to every letter and concatenates the
results. -/
def homOf {A B : Type} (φ : A → List B) : List A → List B := fun w => (w.map φ).flatten

end Lax132576.StringHomomorphisms
end

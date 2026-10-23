-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax68.SeriesParallel
section
set_option autoImplicit false

namespace Lax68.SeriesParallel

def edgeGraph {V : Type*} (s t : V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v =>
    (u = s ∧ v = t) ∨
    (u = t ∧ v = s)

inductive TwoTerminal {V : Type*} : SimpleGraph V → V → V → Prop
  | edge (s t : V) (hne : s ≠ t) :
      TwoTerminal (edgeGraph s t) s t
  | series
      {G H : SimpleGraph V}
      {s m t : V}
      (left : TwoTerminal G s m)
      (right : TwoTerminal H m t)
      (meet :
        ∀ v,
          v ∈ G.support →
          v ∈ H.support →
          v = m) :
      TwoTerminal (G ⊔ H) s t
  | parallel
      {G H : SimpleGraph V}
      {s t : V}
      (left : TwoTerminal G s t)
      (right : TwoTerminal H s t)
      (meet :
        ∀ v,
          v ∈ G.support →
          v ∈ H.support →
          v = s ∨ v = t) :
      TwoTerminal (G ⊔ H) s t

end Lax68.SeriesParallel
end

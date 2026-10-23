-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

-- Lax117284.BipartiteKuhn
section
namespace Lax117284.BipartiteKuhn.runAll
end Lax117284.BipartiteKuhn.runAll

namespace Lax117284.BipartiteKuhn.tryAugment
end Lax117284.BipartiteKuhn.tryAugment

namespace Lax117284.BipartiteKuhn

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- One candidate `r` of the search for `l`: a success already found passes through; a free `r`
is taken; an `r` held by `l'` is taken if `l'` can be re-placed by `tryFrom`, from the matching
with `r` cleared and `r` marked visited. -/
noncomputable def step (adj : L → R → Prop) [DecidableRel adj] (μ : R → Option L) (l : L)
    (tryFrom : (R → Option L) → Finset R → L → Option (R → Option L))
    (acc : Option (R → Option L) × Finset R) (r : R) :
    Option (R → Option L) × Finset R :=
  match acc.1 with
  | some _ => acc
  | none =>
    let visited' := insert r acc.2
    match μ r with
    | none => (some (Function.update μ r (some l)), visited')
    | some l' =>
      match tryFrom (Function.update μ r none) visited' l' with
      | some μ' => (some (Function.update μ' r (some l)), visited')
      | none => (none, visited')

end Lax117284.BipartiteKuhn
end

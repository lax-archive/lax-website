-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card

-- Lax117284.BipartiteKuhn
section
namespace Lax117284.BipartiteKuhn

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The neighbours of a left vertex. -/
noncomputable def nbrs (adj : L → R → Prop) [DecidableRel adj] (l : L) : Finset R :=
  Finset.univ.filter fun r => adj l r

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

/-- **The augmenting search from `l`**: try the unvisited neighbours of `l` in turn, with `fuel`
descents allowed. -/
noncomputable def tryAugment (adj : L → R → Prop) [DecidableRel adj] (fuel : ℕ)
    (μ : R → Option L) (visited : Finset R) (l : L) :
    Option (R → Option L) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    (((nbrs adj l) \ visited).toList.foldl (step adj μ l (tryAugment adj fuel))
      (none, visited)).1

/-- **Try every left vertex in turn**, from an empty visited set, keeping the matching when a
search fails. -/
noncomputable def runAll (adj : L → R → Prop) [DecidableRel adj] (fuel : ℕ) :
    List L → (R → Option L) → (R → Option L)
  | [], μ => μ
  | l :: ls, μ =>
    match tryAugment adj fuel μ ∅ l with
    | some μ' => runAll adj fuel ls μ'
    | none => runAll adj fuel ls μ

/-- **Kuhn's algorithm**: every left vertex, from the empty matching, with fuel enough for any
search. -/
noncomputable def kuhn (adj : L → R → Prop) [DecidableRel adj] : R → Option L :=
  runAll adj (Fintype.card R + 1) Finset.univ.toList (fun _ => none)

end Lax117284.BipartiteKuhn
end

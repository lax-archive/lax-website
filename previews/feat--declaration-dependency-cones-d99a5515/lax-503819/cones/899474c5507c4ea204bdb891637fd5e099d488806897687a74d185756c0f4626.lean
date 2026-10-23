-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Reduce

-- Lax503819.Mortality
section
namespace Lax503819.Mortality

abbrev Instruction := ℕ × ℕ × Bool

structure Machine where
  statesMinusOne : ℕ
  symbolsMinusOne : ℕ
  table : List (List (Option Instruction))

structure Configuration where
  state : ℕ
  tape : List ℕ
  head : ℕ

/-- A step on a finite tape; leaving its boundary halts. -/
def step (m : Machine) (c : Configuration) : Option Configuration := do
  let a ← c.tape[c.head]?
  let (q, b, right) ← (m.table.getD c.state []).getD a none
  if !right && c.head == 0 then none else
    let h := if right then c.head + 1 else c.head - 1
    if h < c.tape.length then
      some ⟨q % (m.statesMinusOne + 1),
        c.tape.set c.head (b % (m.symbolsMinusOne + 1)), h⟩
    else none

/-- After n attempts to take a step, `none` means that the run has halted. -/
def run (m : Machine) : ℕ → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c => (step m c).bind (run m n)

end Lax503819.Mortality
end

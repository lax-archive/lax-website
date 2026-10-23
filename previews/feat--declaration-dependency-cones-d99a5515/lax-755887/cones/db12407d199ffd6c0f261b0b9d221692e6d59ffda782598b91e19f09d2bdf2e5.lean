-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax755887.PersistentQueue
section
namespace Lax755887.PersistentQueue

structure Charge where
  work : ℕ
  before : ℕ
  after : ℕ

def totalWork (trace : List Charge) : ℕ := (trace.map Charge.work).sum

def dequeue (n : ℕ) : Charge := ⟨n + 1, n, 0⟩

end Lax755887.PersistentQueue
end

-- Lax755887.PersistentQueueControls
section
namespace Lax755887.PersistentQueueControls

open Lax755887.PersistentQueue

axiom actual_work (n : ℕ) :
    totalWork (List.replicate (n + 1) (dequeue n)) = (n + 1) ^ 2

end Lax755887.PersistentQueueControls
end

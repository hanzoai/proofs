/-
  On-Chain Anchor

  The anchor precompile stores Merkle roots at (app, height).
  Heights are monotonic — once height N is anchored, anything ≤ N
  is rejected. This gives off-chain CRDT state a tamper-evident
  durability backstop: if the root a user computes locally differs
  from the root on-chain, the server's state diverged.

  Maps to:
  - lux/precompile/anchor/contract.go  (Submit, Get, GetLatest)
  - hanzo/base/crdt/anchor.go          (Anchorer interface, RPCAnchorer)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace CRDT.Anchor

abbrev App := Nat
abbrev Height := Nat
abbrev Root := Nat

/-- The on-chain store. `roots` maps (app, height) to the anchored
    Merkle root; `latest` tracks the highest height per app. -/
structure Store where
  roots  : App → Height → Option Root
  latest : App → Height

/-- Submit an anchor. Succeeds only when the new height exceeds the
    current latest for that app. This is the monotonicity invariant
    that prevents retroactive root substitution. -/
def submit (s : Store) (app : App) (h : Height) (root : Root) : Option Store :=
  if h > s.latest app then
    some {
      roots := fun a ht => if a = app ∧ ht = h then some root else s.roots a ht,
      latest := fun a => if a = app then h else s.latest a,
    }
  else none

def get (s : Store) (app : App) (h : Height) : Option Root := s.roots app h

/-- A successful submit advances the latest height. -/
theorem submit_bumps (s s' : Store) (app : App) (h : Height) (root : Root)
    (ok : submit s app h root = some s') :
    s'.latest app = h ∧ h > s.latest app := by
  simp [submit] at ok
  split at ok
  · obtain ⟨rfl⟩ := ok; simp; assumption
  · simp at ok

/-- Heights at or below the current latest are rejected.
    An attacker cannot rewrite an earlier root without a chain reorg. -/
theorem old_rejected (s : Store) (app : App) (h : Height) (root : Root)
    (low : h ≤ s.latest app) :
    submit s app h root = none := by
  simp [submit, Nat.not_lt.mpr low]

/-- The root is retrievable immediately after submitting it.
    This is the read-your-writes guarantee: a user who submits an
    anchor can verify it was recorded in the same block. -/
theorem read_after_write (s s' : Store) (app : App) (h : Height) (root : Root)
    (ok : submit s app h root = some s') :
    get s' app h = some root := by
  simp [submit] at ok
  split at ok
  · obtain ⟨rfl⟩ := ok; simp [get]
  · simp at ok

/-- Submitting for one app does not affect another app's anchors.
    Each app's data is fully isolated even though they share a
    precompile address. -/
theorem apps_isolated (s s' : Store) (a₁ a₂ : App) (h₁ h₂ : Height) (root : Root)
    (ne : a₁ ≠ a₂) (ok : submit s a₁ h₁ root = some s') :
    get s' a₂ h₂ = get s a₂ h₂ := by
  simp [submit] at ok
  split at ok
  · obtain ⟨rfl⟩ := ok; simp [get, ne]
  · simp at ok

end CRDT.Anchor

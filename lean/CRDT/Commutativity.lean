/-
  CRDT Merge Properties

  Every CRDT merge must satisfy three properties:
    commutative:  merge(a, b) = merge(b, a)
    associative:  merge(merge(a, b), c) = merge(a, merge(b, c))
    idempotent:   merge(a, a) = a

  Together these form a join-semilattice, which guarantees that
  replicas converge to the same state regardless of the order they
  receive operations or how many times they see the same op.

  Maps to:
  - hanzo/base/crdt/types.go  (GCounter.Merge, PNCounter.Merge)
  - hanzo/base/crdt/types.go  (ORSet = grow-only Finset union for nullifiers)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace CRDT.Merge

-- ── GCounter ─────────────────────────────────────────────────
-- Each node tracks its own count. Merge takes the pointwise max.

abbrev GCounter := Nat → Nat

def gcMerge (a b : GCounter) : GCounter := fun n => max (a n) (b n)

theorem gc_comm (a b : GCounter) : gcMerge a b = gcMerge b a := by
  ext n; simp [gcMerge, Nat.max_comm]

theorem gc_assoc (a b c : GCounter) :
    gcMerge (gcMerge a b) c = gcMerge a (gcMerge b c) := by
  ext n; simp [gcMerge, Nat.max_assoc]

theorem gc_idem (a : GCounter) : gcMerge a a = a := by
  ext n; simp [gcMerge]

-- ── PNCounter ────────────────────────────────────────────────
-- Two GCounters: one for increments, one for decrements.
-- Value = positive.sum - negative.sum. Merge = merge each side.

structure PNCounter where
  pos : GCounter
  neg : GCounter

def pnMerge (a b : PNCounter) : PNCounter :=
  { pos := gcMerge a.pos b.pos, neg := gcMerge a.neg b.neg }

theorem pn_comm (a b : PNCounter) : pnMerge a b = pnMerge b a := by
  simp [pnMerge, gc_comm]

theorem pn_assoc (a b c : PNCounter) :
    pnMerge (pnMerge a b) c = pnMerge a (pnMerge b c) := by
  simp [pnMerge, gc_assoc]

theorem pn_idem (a : PNCounter) : pnMerge a a = a := by
  simp [pnMerge, gc_idem]

-- ── G-Set (grow-only set) ────────────────────────────────────
-- Used for nullifier sets in the Z-Chain ZK-UTXO model.
-- Merge = set union. Union is a textbook semilattice.

theorem set_comm (a b : Finset Nat) : a ∪ b = b ∪ a := Finset.union_comm a b
theorem set_assoc (a b c : Finset Nat) : (a ∪ b) ∪ c = a ∪ (b ∪ c) := Finset.union_assoc a b c
theorem set_idem (a : Finset Nat) : a ∪ a = a := Finset.union_idempotent a

-- ── Typeclass ────────────────────────────────────────────────
-- Any type whose merge commutes, associates, and is idempotent.
-- This is the contract every new CRDT type must satisfy.

class Mergeable (α : Type) where
  merge : α → α → α
  comm  : ∀ a b, merge a b = merge b a
  assoc : ∀ a b c, merge (merge a b) c = merge a (merge b c)
  idem  : ∀ a, merge a a = a

instance : Mergeable GCounter where
  merge := gcMerge; comm := gc_comm; assoc := gc_assoc; idem := gc_idem

instance : Mergeable PNCounter where
  merge := pnMerge; comm := pn_comm; assoc := pn_assoc; idem := pn_idem

instance : Mergeable (Finset Nat) where
  merge := (· ∪ ·); comm := set_comm; assoc := set_assoc; idem := set_idem

end CRDT.Merge

/-
  Rate Limiting Fairness

  Token bucket rate limiting. Fair across tenants.
  No single tenant can starve others.

  Maps to:
  - hanzo/gateway: rate limiting middleware
  - hanzo/iam: tenant-level quotas

  Properties:
  - Fairness: each tenant gets their quota
  - No starvation: below-quota requests always pass
  - Burst: allows short bursts up to bucket size
  - Recovery: bucket refills over time

  Author: Woo Bin
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Gateway.RateLimit

structure TokenBucket where
  tokens : Nat        -- current tokens
  capacity : Nat      -- max tokens (burst size)
  refillRate : Nat    -- tokens per second

def tryConsume (b : TokenBucket) (cost : Nat) : Option TokenBucket :=
  if cost ≤ b.tokens then some { b with tokens := b.tokens - cost }
  else none

def refill (b : TokenBucket) (seconds : Nat) : TokenBucket :=
  { b with tokens := min (b.tokens + seconds * b.refillRate) b.capacity }

/-- FAIRNESS: If you have tokens, request passes -/
theorem has_tokens_passes (b : TokenBucket) (cost : Nat)
    (h : cost ≤ b.tokens) :
    (tryConsume b cost).isSome = true := by
  simp [tryConsume, h]

/-- RATE LIMITED: No tokens → blocked -/
theorem no_tokens_blocked (b : TokenBucket) (cost : Nat)
    (h : cost > b.tokens) :
    tryConsume b cost = none := by
  simp [tryConsume, Nat.not_le.mpr h]

/-- BURST: Bucket never exceeds capacity -/
theorem refill_capped (b : TokenBucket) (seconds : Nat) :
    (refill b seconds).tokens ≤ b.capacity := by
  simp [refill]

/-- RECOVERY: Refill never loses tokens, for any bucket at or under
    capacity. The cap is what makes the bound need `hb`: a bucket already
    over capacity would be clamped down by a refill. -/
theorem refill_increases (b : TokenBucket) (seconds : Nat)
    (hb : b.tokens ≤ b.capacity) :
    (refill b seconds).tokens ≥ b.tokens := by
  simp only [refill]
  exact le_min (Nat.le_add_right _ _) hb

/-- CONSUMPTION DECREASES: Using tokens reduces count -/
theorem consume_decreases (b b' : TokenBucket) (cost : Nat)
    (h : tryConsume b cost = some b') (hc : cost > 0) :
    b'.tokens < b.tokens := by
  simp [tryConsume] at h
  obtain ⟨hcost, rfl⟩ := h
  show b.tokens - cost < b.tokens
  omega

end Gateway.RateLimit

/-
  Compute Billing Protocol (HIP-0025)

  Agent wallet RPC billing. Every API call costs $AI.
  Pre-paid balance, per-call deduction, rate limiting.

  Maps to:
  - HIP-0025: Bot/Agent Wallet RPC Billing Protocol
  - HIP-0096: AI Compute Contribution Rewards
  - hanzo/gateway: billing middleware
  - hanzo/formal/lean/Agent/Identity.lean: session budgets

  Properties:
  - Prepaid: balance checked before execution
  - Metered: each call has a known cost
  - Rate limited: max calls per second
  - Accretive rewards: compute providers earn $AI
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Compute.Billing

/-- Billing account state -/
structure Account where
  balance : Nat          -- $AI balance (in smallest unit)
  totalSpent : Nat       -- lifetime spend
  callsThisSecond : Nat  -- rate limit counter
  rateLimit : Nat        -- max calls per second

/-- API call with cost -/
structure APICall where
  method : String
  cost : Nat             -- cost in $AI
  computeUnits : Nat     -- compute consumed

/-- Execute a billed API call -/
def executeCall (a : Account) (c : APICall) : Option Account :=
  if c.cost ≤ a.balance && a.callsThisSecond < a.rateLimit then
    some { a with
      balance := a.balance - c.cost
      totalSpent := a.totalSpent + c.cost
      callsThisSecond := a.callsThisSecond + 1 }
  else none

/-- PREPAID: Insufficient balance → rejected -/
theorem insufficient_balance_rejected (a : Account) (c : APICall)
    (h : c.cost > a.balance) :
    executeCall a c = none := by
  simp [executeCall, Nat.not_le.mpr h]

/-- RATE LIMITED: Exceeded rate → rejected -/
theorem rate_limited (a : Account) (c : APICall)
    (h : a.callsThisSecond ≥ a.rateLimit) :
    executeCall a c = none := by
  simp [executeCall, Nat.not_lt.mpr h]
  intro; exact Bool.and_false _

/-- BALANCE CONSERVATION: balance + totalSpent is constant -/
theorem balance_conservation (a a' : Account) (c : APICall)
    (h : executeCall a c = some a') :
    a'.balance + a'.totalSpent = a.balance + a.totalSpent := by
  simp [executeCall] at h; split at h <;> simp_all; omega

/-- BALANCE DECREASES: Each call reduces balance -/
theorem balance_decreases (a a' : Account) (c : APICall)
    (h : executeCall a c = some a') (hc : c.cost > 0) :
    a'.balance < a.balance := by
  simp [executeCall] at h; split at h <;> simp_all; omega

/-- SPEND MONOTONE: totalSpent only increases -/
theorem spend_monotone (a a' : Account) (c : APICall)
    (h : executeCall a c = some a') :
    a'.totalSpent ≥ a.totalSpent := by
  simp [executeCall] at h; split at h <;> simp_all; omega

/-- FREE CALLS: Zero-cost calls don't reduce balance -/
theorem free_call_preserves (a : Account) (c : APICall)
    (hc : c.cost = 0) (hr : a.callsThisSecond < a.rateLimit) :
    ∃ a', executeCall a c = some a' ∧ a'.balance = a.balance := by
  simp [executeCall, hc, hr]

end Compute.Billing

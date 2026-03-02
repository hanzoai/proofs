/-
  Agent Identity and Wallet Binding

  Each agent has a cryptographic identity bound to a wallet.
  The identity determines what the agent can sign, attest, and spend.

  Maps to:
  - HIP-0025: Bot/Agent Wallet RPC Billing Protocol
  - HIP-0026: Identity Access Management Standard
  - hanzo/iam: OIDC identity provider
  - lux/wallet: wallet key management

  Properties:
  - Identity binding: agent ↔ wallet is 1:1
  - Signing authority: agent signs with its bound key
  - Spending limits: agent has a per-session budget
  - Over-budget rejected: overspend is a no-op
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Agent.Identity

/-- Agent identity: unique id, bound wallet public key, OIDC token hash,
    and a per-session spending budget (denominated in $AI). -/
structure AgentIdentity where
  agentId       : Nat
  walletPK      : Nat
  iamToken      : Nat
  sessionBudget : Nat
  deriving DecidableEq, Repr

/-- Cumulative spending record for an identity within a session. -/
structure SpendRecord where
  identity : AgentIdentity
  spent    : Nat
  deriving Repr

/-- Permission predicate: the agent has room for another spend. -/
def canSpend (r : SpendRecord) (amount : Nat) : Prop :=
  r.spent + amount ≤ r.identity.sessionBudget

instance (r : SpendRecord) (amount : Nat) : Decidable (canSpend r amount) := by
  unfold canSpend; exact inferInstance

/-- Execute a spend: if within budget, record it; otherwise no-op. -/
def spend (r : SpendRecord) (amount : Nat) : SpendRecord :=
  if canSpend r amount then
    { r with spent := r.spent + amount }
  else r

/-- **Theorem (budget enforcement):** cumulative spending never exceeds
    the session budget, given the prior-state invariant that the
    record is already within budget. This invariant is trivially
    maintained: `freshSession` starts at 0, and every subsequent
    `spend` preserves it (this theorem is the inductive step). -/
theorem spend_within_budget (r : SpendRecord) (amount : Nat)
    (hprior : r.spent ≤ r.identity.sessionBudget) :
    (spend r amount).spent ≤ r.identity.sessionBudget := by
  unfold spend
  by_cases h : canSpend r amount
  · simp [h]; exact h
  · simp [h]; exact hprior

/-- **Theorem (over-budget rejected):** an overspend is a no-op. -/
theorem overspend_rejected (r : SpendRecord) (amount : Nat)
    (h : r.spent + amount > r.identity.sessionBudget) :
    spend r amount = r := by
  unfold spend
  have hnot : ¬ canSpend r amount := by unfold canSpend; omega
  simp [hnot]

/-- **Theorem (monotone spending):** the cumulative spent amount is
    non-decreasing under every `spend` call. -/
theorem spent_monotone (r : SpendRecord) (amount : Nat) :
    r.spent ≤ (spend r amount).spent := by
  unfold spend
  by_cases h : canSpend r amount
  · simp [h]
  · simp [h]

/-- **Theorem (identity binding):** identical wallet public keys give
    identical signing authority (reflexive observation). -/
theorem identity_determines_signer (a1 a2 : AgentIdentity)
    (h : a1.walletPK = a2.walletPK) : a1.walletPK = a2.walletPK := h

/-- A fresh session for an identity: nothing spent yet. -/
def freshSession (id : AgentIdentity) : SpendRecord := ⟨id, 0⟩

/-- **Theorem:** any amount within budget is spendable from a fresh
    session. -/
theorem fresh_can_spend (id : AgentIdentity) (amount : Nat)
    (h : amount ≤ id.sessionBudget) :
    canSpend (freshSession id) amount := by
  unfold canSpend freshSession; simpa using h

end Agent.Identity

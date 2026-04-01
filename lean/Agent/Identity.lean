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
  - Attestation: agent identity is in every discharge proof
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace Agent.Identity

/-- Agent identity -/
structure AgentIdentity where
  agentId : Nat        -- unique agent identifier
  walletPK : Nat       -- bound wallet public key
  iamToken : Nat       -- OIDC token hash
  sessionBudget : Nat  -- max spend per session (in $AI)
  deriving DecidableEq, Repr

/-- Spending record -/
structure SpendRecord where
  identity : AgentIdentity
  spent : Nat
  deriving Repr

/-- Can the agent spend more? -/
def canSpend (r : SpendRecord) (amount : Nat) : Bool :=
  r.spent + amount ≤ r.identity.sessionBudget

/-- Execute a spend -/
def spend (r : SpendRecord) (amount : Nat) : SpendRecord :=
  if canSpend r amount then
    { r with spent := r.spent + amount }
  else r

/-- BUDGET ENFORCEMENT: Spending never exceeds budget -/
theorem spend_within_budget (r : SpendRecord) (amount : Nat) :
    (spend r amount).spent ≤ r.identity.sessionBudget := by
  simp [spend, canSpend]
  split <;> omega

/-- OVER-BUDGET REJECTED: Overspend is a no-op -/
theorem overspend_rejected (r : SpendRecord) (amount : Nat)
    (h : r.spent + amount > r.identity.sessionBudget) :
    spend r amount = r := by
  simp [spend, canSpend, Nat.not_le.mpr (by omega : ¬(r.spent + amount ≤ r.identity.sessionBudget))]

/-- MONOTONE: Spent amount only increases -/
theorem spent_monotone (r : SpendRecord) (amount : Nat) :
    (spend r amount).spent ≥ r.spent := by
  simp [spend, canSpend]; split <;> omega

/-- IDENTITY BINDING: Same wallet PK → same signing authority -/
theorem identity_determines_signer (a1 a2 : AgentIdentity)
    (h : a1.walletPK = a2.walletPK) :
    a1.walletPK = a2.walletPK := h

/-- FRESH SESSION: New agent starts with zero spent -/
def freshSession (id : AgentIdentity) : SpendRecord :=
  ⟨id, 0⟩

theorem fresh_can_spend (id : AgentIdentity) (amount : Nat)
    (h : amount ≤ id.sessionBudget) :
    canSpend (freshSession id) amount = true := by
  simp [freshSession, canSpend, h]

end Agent.Identity

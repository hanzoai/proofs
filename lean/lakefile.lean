import Lake
open Lake DSL

package hanzoFormal where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Hanzo-native proofs (agents, gateway, platform, KMS, compute)

@[default_target]
lean_lib Agent where
  srcDir := "."
  roots := #[
    `Agent.Safety,
    `Agent.MCP,
    `Agent.Delegation,
    `Agent.Workflow,
    `Agent.Identity,
    `Agent.Memory
  ]

lean_lib Gateway where
  srcDir := "."
  roots := #[
    `Gateway.Auth,
    `Gateway.RateLimit
  ]

lean_lib Platform where
  srcDir := "."
  roots := #[
    `Platform.Deploy,
    `Platform.SBOM,
    `Platform.Monitoring
  ]

lean_lib KMS where
  srcDir := "."
  roots := #[
    `KMS.Secrets
  ]

lean_lib Compute where
  srcDir := "."
  roots := #[
    `Compute.PoAI,
    `Compute.ConfidentialCompute,
    `Compute.Swarm,
    `Compute.Billing
  ]

-- Infrastructure proofs (from Lux L1 foundation)

lean_lib Consensus where
  srcDir := "."
  roots := #[
    `Consensus.BFT,
    `Consensus.Safety,
    `Consensus.Liveness,
    `Consensus.Finality,
    `Consensus.Validator,
    `Consensus.Quasar
  ]

lean_lib Crypto where
  srcDir := "."
  roots := #[
    `Crypto.BLS,
    `Crypto.FROST,
    `Crypto.Ringtail,
    `Crypto.MLDSA,
    `Crypto.Hybrid,
    `Crypto.SLHDSA,
    `Crypto.MLKEM,
    `Crypto.FHE.TFHE,
    `Crypto.FHE.CKKS,
    `Crypto.Threshold.CGGMP21,
    `Crypto.Threshold.LSS,
    `Crypto.Threshold.Composition,
    `Crypto.VerkleTree
  ]

lean_lib Trust where
  srcDir := "."
  roots := #[
    `Trust.Authority,
    `Trust.Vouch,
    `Trust.Revocation
  ]

lean_lib Warp where
  srcDir := "."
  roots := #[
    `Warp.Delivery,
    `Warp.Ordering,
    `Warp.Security
  ]

lean_lib Network where
  srcDir := "."
  roots := #[
    `Network.PeerDiscovery
  ]

-- GPU acceleration proofs (from Zoo)

lean_lib GPU where
  srcDir := "."
  roots := #[
    `GPU.EVMScaling,
    `GPU.FHEScaling,
    `GPU.ConsensusScaling,
    `GPU.DEXScaling
  ]

-- CRDT proofs (privacy, commutativity, on-chain anchoring)

lean_lib CRDT where
  srcDir := "."
  roots := #[
    `CRDT.Privacy,
    `CRDT.Commutativity,
    `CRDT.Anchor
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

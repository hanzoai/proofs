# Hanzo Formal Proofs

Machine-checked and paper proofs for Hanzo AI Chain (= Lux A-Chain
under Hanzo branding) and the Hanzo agent / inference settlement
stack.

## Inventory

| File | Topic | Status |
|---|---|---|
| `hanzo-ai-chain-soundness.tex` | A-Chain (AIVM) attestation pipeline soundness | paper |
| `hanzo-adopts-liquidity-protocol.tex` | Hanzo formal adoption of the Liquidity Protocol (2026-04-20) | paper |
| `lean/` | Lean 4 sources (shared with `luxfi/proofs/lean/`) | typecheck |

## Provenance

The Hanzo AI Chain is the Lux A-Chain (AIVM) deployed under the Hanzo
brand. All low-level consensus, finality, and post-quantum security
properties are inherited verbatim from `luxfi/proofs`:

- `quasar-cert-soundness.tex` (LP-105 / Theorems 7.5-7.8)
- `lean/Consensus/Quasar.lean`
- `lean/Crypto/{BLS,MLDSA,Ringtail}.lean`
- `lean/Consensus/DAGEVM.lean` (Block-STM serialisability)

This repo adds AI-specific lemmas:

1. Model-provenance commitment (every inference receipt commits to a
   model-hash).
2. Agent-identity binding via DID (`did:lux:agent:*`).
3. TEE attestation chain (Nitro Enclaves + AMD SEV-SNP, Hanzo
   attestation pre-compile per LP-127).
4. Inference-receipt settlement atomicity over the Liquidity Protocol
   (post 2026-04-20 adoption).

## Build

```bash
cd lean && lake build           # Lean 4 (shared with luxfi/proofs)
tectonic hanzo-ai-chain-soundness.tex
tectonic hanzo-adopts-liquidity-protocol.tex
```

## Citations

Canonical references:

- `~/work/lux/lps/TAXONOMY.md` (forbidden upstream names; A-Chain = AIVM)
- `~/work/lux/lps/LP-127-attestation.md`
- `~/work/lux/lps/LP-130-ai.md`
- `~/work/lux/lps/LP-134-lux-chain-topology.md`
- `~/work/hanzo/papers/hanzo-ai-chain/hanzo-ai-chain.tex`
- `~/work/liquidity/proofs/liquidity-protocol/liquidity-protocol.tex`

## Chronology

See `CHRONOLOGY.md`.

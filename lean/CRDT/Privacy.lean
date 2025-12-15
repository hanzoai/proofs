/-
  CRDT Privacy

  Every operation is sealed before it leaves the process and opened
  when it arrives. The wire format carries only sealed envelopes —
  there is no plaintext field, so a downgrade injection cannot be
  expressed as a valid message.

  Each envelope binds the document ID into the authenticated payload.
  An envelope captured from document A cannot be replayed against
  document B even when both share a key, because the opener checks
  the embedded ID against its own.

  Maps to:
  - hanzo/base/crdt/privacy.go   (Privacy interface: Name, EncryptOp, DecryptOp)
  - hanzo/base/crdt/document.go  (SealOps / OpenOps with docID wrapping)
  - hanzo/base/crdt/sync.go      (SyncMessage has Envelopes only, resolveOps is one line)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace CRDT.Privacy

abbrev Op := Nat
abbrev Tag := String
abbrev DocID := String
abbrev Ciphertext := Nat

/-- A privacy backend seals and opens operations. The `recovers` field
    is the contract: open always undoes seal. -/
structure Backend where
  name     : Tag
  seal     : Op → Ciphertext
  open_    : Ciphertext → Option Op
  recovers : ∀ op, open_ (seal op) = some op

/-- An envelope pairs the backend's tag with the ciphertext.
    The tag lets the receiver verify the op was sealed by a
    compatible backend before attempting to decrypt. -/
structure Envelope where
  tag : Tag
  ct  : Ciphertext

def seal (b : Backend) (op : Op) : Envelope :=
  { tag := b.name, ct := b.seal op }

def open_ (b : Backend) (env : Envelope) : Option Op :=
  if env.tag = b.name then b.open_ env.ct else none

/-- Seal then open gives back the original op. -/
theorem seal_then_open (b : Backend) (op : Op) :
    open_ b (seal b op) = some op := by
  simp [open_, seal, b.recovers]

/-- An envelope sealed by one backend cannot be opened by another.
    This is the tag-mismatch check that prevents a peer from
    swapping backends mid-stream. -/
theorem wrong_tag (b₁ b₂ : Backend) (h : b₁.name ≠ b₂.name) (op : Op) :
    open_ b₂ (seal b₁ op) = none := by
  simp [open_, seal, Ne.symm h]

-- ── DocID binding ────────────────────────────────────────────

/-- A bound envelope extends Envelope with the document ID.
    In the Go code this ID is prepended inside the ciphertext
    via wrapDocID; here we model it as a field for clarity. -/
structure BoundEnvelope extends Envelope where
  docID : DocID

def sealFor (b : Backend) (doc : DocID) (op : Op) : BoundEnvelope :=
  { tag := b.name, ct := b.seal op, docID := doc }

def openFor (b : Backend) (doc : DocID) (env : BoundEnvelope) : Option Op :=
  if env.tag = b.name ∧ env.docID = doc then b.open_ env.ct else none

/-- Seal then open works when the document matches. -/
theorem same_doc (b : Backend) (doc : DocID) (op : Op) :
    openFor b doc (sealFor b doc op) = some op := by
  simp [openFor, sealFor, b.recovers]

/-- An envelope sealed for one document fails on a different document.
    This is the cross-document replay defence: the attacker has a valid
    ciphertext from doc A, but doc B's opener sees the wrong docID
    inside the payload and rejects it. -/
theorem wrong_doc (b : Backend) (d₁ d₂ : DocID) (h : d₁ ≠ d₂) (op : Op) :
    openFor b d₂ (sealFor b d₁ op) = none := by
  simp [openFor, sealFor, h]

-- ── Wire format ──────────────────────────────────────────────

/-- SyncMessage carries bound envelopes only. There is no bare-ops
    field — the downgrade injection that existed when the message had
    both Ops and Envelopes is structurally impossible in this type. -/
structure Message where
  docID     : DocID
  envelopes : List BoundEnvelope

/-- Open every envelope in a message. If any one fails the whole
    message is rejected — no partial application. -/
def resolve (b : Backend) (doc : DocID) (msg : Message) : Option (List Op) :=
  msg.envelopes.mapM (openFor b doc)

/-- A message where every envelope was sealed for the right doc and
    the right backend resolves to the original ops. -/
theorem good_message (b : Backend) (doc : DocID) (ops : List Op) :
    resolve b doc { docID := doc, envelopes := ops.map (sealFor b doc) } = some ops := by
  simp [resolve, List.mapM_map, same_doc]

/-- A message sealed for the wrong document is rejected entirely.
    Even one mismatched docID poisons the mapM chain. -/
theorem bad_message (b : Backend) (d₁ d₂ : DocID) (h : d₁ ≠ d₂)
    (ops : List Op) (hne : ops ≠ []) :
    resolve b d₂ { docID := d₁, envelopes := ops.map (sealFor b d₁) } = none := by
  simp [resolve]
  cases ops with
  | nil => exact absurd rfl hne
  | cons hd tl => simp [List.mapM, openFor, sealFor, h]

end CRDT.Privacy

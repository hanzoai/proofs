/-
  CRDT Privacy

  Every operation is wrapped before it leaves the process and unwrapped
  when it arrives. The wire format carries only wrapped envelopes —
  there is no plaintext field, so a downgrade injection cannot be
  expressed as a valid message.

  Each envelope binds the document ID into the authenticated payload.
  An envelope captured from document A cannot be replayed against
  document B even when both share a key, because the opener checks
  the embedded ID against its own.

  `seal` and `open` are Lean commands, so the backend operations here
  carry the names the Go interface uses (EncryptOp / DecryptOp) and the
  envelope layer is wrap / unwrap (Go: SealOps / OpenOps).

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

/-- A privacy backend encrypts and decrypts operations. The `recovers`
    field is the contract: decrypt always undoes encrypt. -/
structure Backend where
  name     : Tag
  encrypt  : Op → Ciphertext
  decrypt  : Ciphertext → Option Op
  recovers : ∀ op, decrypt (encrypt op) = some op

/-- An envelope pairs the backend's tag with the ciphertext.
    The tag lets the receiver verify the op was encrypted by a
    compatible backend before attempting to decrypt. -/
structure Envelope where
  tag : Tag
  ct  : Ciphertext

def wrap (b : Backend) (op : Op) : Envelope :=
  { tag := b.name, ct := b.encrypt op }

def unwrap (b : Backend) (env : Envelope) : Option Op :=
  if env.tag = b.name then b.decrypt env.ct else none

/-- Wrap then unwrap gives back the original op. -/
theorem wrap_then_unwrap (b : Backend) (op : Op) :
    unwrap b (wrap b op) = some op := by
  simp [unwrap, wrap, b.recovers]

/-- An envelope wrapped by one backend cannot be unwrapped by another.
    This is the tag-mismatch check that prevents a peer from
    swapping backends mid-stream. -/
theorem wrong_tag (b₁ b₂ : Backend) (h : b₁.name ≠ b₂.name) (op : Op) :
    unwrap b₂ (wrap b₁ op) = none := by
  simp [unwrap, wrap, h]

-- ── DocID binding ────────────────────────────────────────────

/-- A bound envelope extends Envelope with the document ID.
    In the Go code this ID is prepended inside the ciphertext
    via wrapDocID; here we model it as a field for clarity. -/
structure BoundEnvelope extends Envelope where
  docID : DocID

def wrapFor (b : Backend) (doc : DocID) (op : Op) : BoundEnvelope :=
  { tag := b.name, ct := b.encrypt op, docID := doc }

def unwrapFor (b : Backend) (doc : DocID) (env : BoundEnvelope) : Option Op :=
  if env.tag = b.name ∧ env.docID = doc then b.decrypt env.ct else none

/-- Wrap then unwrap works when the document matches. -/
theorem same_doc (b : Backend) (doc : DocID) (op : Op) :
    unwrapFor b doc (wrapFor b doc op) = some op := by
  simp [unwrapFor, wrapFor, b.recovers]

/-- An envelope wrapped for one document fails on a different document.
    This is the cross-document replay defence: the attacker has a valid
    ciphertext from doc A, but doc B's opener sees the wrong docID
    inside the payload and rejects it. -/
theorem wrong_doc (b : Backend) (d₁ d₂ : DocID) (h : d₁ ≠ d₂) (op : Op) :
    unwrapFor b d₂ (wrapFor b d₁ op) = none := by
  simp [unwrapFor, wrapFor, h]

-- ── Wire format ──────────────────────────────────────────────

/-- SyncMessage carries bound envelopes only. There is no bare-ops
    field — the downgrade injection that existed when the message had
    both Ops and Envelopes is structurally impossible in this type. -/
structure Message where
  docID     : DocID
  envelopes : List BoundEnvelope

/-- Unwrap every envelope in a message. If any one fails the whole
    message is rejected — no partial application. -/
def resolve (b : Backend) (doc : DocID) (msg : Message) : Option (List Op) :=
  msg.envelopes.mapM (unwrapFor b doc)

/-- A message where every envelope was wrapped for the right doc and
    the right backend resolves to the original ops. -/
theorem good_message (b : Backend) (doc : DocID) (ops : List Op) :
    resolve b doc { docID := doc, envelopes := ops.map (wrapFor b doc) } = some ops := by
  simp only [resolve, ← List.mapM'_eq_mapM]
  induction ops with
  | nil => rfl
  | cons hd tl ih => simp [same_doc, ih]

/-- A message wrapped for the wrong document is rejected entirely.
    Even one mismatched docID poisons the mapM chain. -/
theorem bad_message (b : Backend) (d₁ d₂ : DocID) (h : d₁ ≠ d₂)
    (ops : List Op) (hne : ops ≠ []) :
    resolve b d₂ { docID := d₁, envelopes := ops.map (wrapFor b d₁) } = none := by
  cases ops with
  | nil => exact absurd rfl hne
  | cons hd tl =>
    simp only [resolve, ← List.mapM'_eq_mapM]
    simp [unwrapFor, wrapFor, h]

end CRDT.Privacy

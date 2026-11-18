import CausalMohawkBridge.KrumSpec
import CausalMohawkBridge.EpochTransition

/-!
# Multi-Krum refinement — ported from Sovereign-Mohawk-Proto

Port of the row-12 refinement lemmas from
`proofs/Refinement/MultiKrum.lean` and `proofs/Refinement/BFT.lean`
(`github.com/rwilliamspbg-ops/Sovereign-Mohawk-Proto`), plus the bridge that
identifies this project's `Mohawk.krumEnvelope` with the upstream
`bftImplSafe` predicate.

All proofs here are Mathlib-free (`omega` / `simp`), so they compile on this
project's Lean 4.14.0 toolchain.
-/

namespace CausalMohawkBridge.KrumRefinement

open KrumSpec Mohawk

/-- Go's `MultiKrumSelect` derives its neighbor count as `n - f - 2` from the
    Byzantine bound `f`, and requires `n > 2f + 2` before ever calling the
    scoring routine. Under that precondition the derived neighbor count is a
    valid, non-degenerate `k`: at least 1, and strictly below `n - 1`. -/
theorem go_neighbors_valid (n f : Nat) (h : n > 2 * f + 2) :
    1 ≤ n - f - 2 ∧ n - f - 2 < n - 1 := by
  omega

/-- Consequence for the Lean spec: `multiKrumSelectImpl`'s internal
    `Nat.min k (gradients.length - 1)` clamp never fires when `k` is Go's
    derived neighbor count under Go's precondition. -/
theorem go_neighbors_no_clamp (n f : Nat) (h : n > 2 * f + 2) :
    Nat.min (n - f - 2) (n - 1) = n - f - 2 := by
  have hv := go_neighbors_valid n f h
  exact Nat.min_eq_left (by omega)

/-- The Lean spec function is deterministic (same inputs, same output). -/
theorem multiKrumSelectImpl_deterministic (nodes : List Node) (k : Nat) :
    multiKrumSelectImpl nodes k = multiKrumSelectImpl nodes k := rfl

/-- `multiKrumSelectSafe` delegates to `multiKrumSelectImpl` exactly when Go's
    `n > 2f + 2` precondition holds. -/
theorem multiKrumSelectSafe_eq_impl (nodes : List Node) (f : Nat)
    (h : nodes.length > 2 * f + 2) :
    multiKrumSelectSafe nodes f = multiKrumSelectImpl nodes (nodes.length - f - 2) := by
  simp [multiKrumSelectSafe, h]

/-- `multiKrumSelectSafe` returns `none` outside Go's safety envelope. -/
theorem multiKrumSelectSafe_none_outside_envelope (nodes : List Node) (f : Nat)
    (h : nodes.length ≤ 2 * f + 2) :
    multiKrumSelectSafe nodes f = none := by
  simp [multiKrumSelectSafe, Nat.not_lt.mpr h]

/-! ## BFT refinement: Go's stricter precondition implies the Lean spec safety -/

/-- Spec (Lean) safety: `2*f < n`. -/
def bftSpecSafe (n f : Nat) : Prop := 2 * f < n

/-- Impl (Go) safety precondition: `n > 2*f + 2`. -/
def bftImplSafe (n f : Nat) : Prop := 2 * f + 2 < n

/-- Refinement: Go's stricter precondition implies Lean's spec safety. -/
theorem bft_impl_refines_spec (n f : Nat) (h : bftImplSafe n f) : bftSpecSafe n f := by
  unfold bftImplSafe bftSpecSafe at *
  omega

/-- Gap witness: `n=4, f=1` is spec-safe (`2 < 4`) but impl-unsafe (`4 ≮ 4`). -/
theorem bft_gap_witness : bftSpecSafe 4 1 ∧ ¬ bftImplSafe 4 1 := by
  constructor
  · simp [bftSpecSafe]
  · simp [bftImplSafe]

/-- Concrete guard: 7 nodes, 2 Byzantine — both spec-safe and impl-safe. -/
theorem bft_concrete_guard : bftSpecSafe 7 2 ∧ bftImplSafe 7 2 := by
  constructor <;> simp [bftSpecSafe, bftImplSafe]

/-! ## Bridge to this project's `Mohawk.EpochState` -/

/-- `Mohawk.krumEnvelope` is exactly the upstream impl-safety predicate. -/
theorem krumEnvelope_iff_bftImplSafe (s : EpochState) :
    krumEnvelope s ↔ bftImplSafe s.n s.f := by
  unfold krumEnvelope bftImplSafe
  exact Iff.rfl

/-- The Krum envelope therefore implies the Lean BFT spec-safety condition. -/
theorem krumEnvelope_bftSpecSafe {s : EpochState} (h : krumEnvelope s) :
    bftSpecSafe s.n s.f :=
  bft_impl_refines_spec s.n s.f ((krumEnvelope_iff_bftImplSafe s).mp h)

/-- The envelope implies the neighbour-count positivity guard used by the
    epoch-transition development. -/
theorem krumEnvelope_neighbors_pos {s : EpochState} (h : krumEnvelope s) :
    0 < s.n - s.f - 2 :=
  neighbors_pos h

end CausalMohawkBridge.KrumRefinement

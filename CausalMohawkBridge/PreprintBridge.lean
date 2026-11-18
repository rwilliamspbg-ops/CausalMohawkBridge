import CausalMohawkBridge.EpochTransition
import CausalMohawkBridge.EpochRot
import CausalMohawkBridge.NullCoordinates
import CausalMohawkBridge.ParityQuotient

/-!
# Bridge: Theorem 3.1 causal geometry ↔ epoch-transition model

States the correspondences that *do* hold between the preprint's null-
coordinate causal lattice and this project's epoch model.

What is established:
* for even `n`, the parity sector descends to the spatial quotient (`q_parity`);
* inside the window `K_B` (lattice spacing `sp`), if the circumference `n·sp`
  exceeds `4B`, quotient reachability lifts to genuine causal reachability
  (`reach_of_qReach_of_noWinding`, the discrete `ℓ_n > 4B`);
* the number of epoch rotations induced by a causal path equals the sum of the
  null-coordinate increments (`epoch_count_eq_rl`), so spatial quotienting
  preserves the epoch count;
* the pair (parity sector, Krum envelope) is a compositional invariant of the
  combined causal/epoch step.

`theorem31` packages the first three as one numbered statement. The
probabilistic Chernoff bound and the Lorentz common-domain machinery are proved
in `Chernoff`/`Lorentz`/`Composition` and are deliberately not part of this
bridge.

Mathlib-free; Lean 4.14.0.
-/

namespace CausalMohawkBridge.PreprintBridge

open CausalLattice Mohawk

/-- The combined invariant: the event stays in its parity sector and the epoch
    state stays inside the Multi-Krum safety envelope. -/
def PEvent (e : Event) (s : EpochState) : Prop := OnParity e ∧ krumEnvelope s

/-- The combined invariant is preserved by one causal step plus one epoch
    rotation. -/
theorem PEvent_step {e e' : Event} {s s' : EpochState}
    (hr : Reach e e') (hs : Step s s') (hp : PEvent e s) : PEvent e' s' :=
  ⟨Reach.parity hr hp.1, step_envelope hs⟩

/-- The epoch rotation count induced by a causal path is exactly the sum of the
    null-coordinate increments. -/
theorem epoch_count_eq_rl {e₁ e₂ : Event} (hr : Reach e₁ e₂)
    (s : EpochState) (h : krumEnvelope s) :
    ∃ s' L, EpochRot.Rot s s' L ∧ krumEnvelope s' ∧
      (L : Int) = (NullCoordinates.r e₂ - NullCoordinates.r e₁) +
        (NullCoordinates.l e₂ - NullCoordinates.l e₁) := by
  obtain ⟨s', L, hrot, he, hep, hL⟩ := EpochRot.reach_to_rot hr s h
  refine ⟨s', L, hrot, he, ?_⟩
  rw [hL, NullCoordinates.reach_t_eq_rl hr]

/-- Quotienting preserves the time advance (and hence the null increments). -/
theorem qReach_t_advance {n : Nat} {e₁ e₂ : Event}
    (_h : ParityQuotient.QReach n (ParityQuotient.q n e₁) (ParityQuotient.q n e₂)) :
    (ParityQuotient.q n e₂).t - (ParityQuotient.q n e₁).t = e₂.t - e₁.t := rfl

/-- Under the no-winding condition, a quotient path induces the same epoch
    rotation count as its lifted realisation: the count is the sum of the
    null-coordinate increments, computed in the lift. Generalised to lattice
    spacing `sp` (`ℓ_n = n·sp > 4B`). -/
theorem epoch_count_quotient {n : Nat} {B sp : Int} {e₁ e₂ : Event}
    {s : EpochState} (hsp : 0 < sp) (hn : 4 * B < n * sp) (hn2 : 2 ≤ n)
    (h₁ : ParityQuotient.Window B sp e₁) (h₂ : ParityQuotient.Window B sp e₂)
    (hq : ParityQuotient.QReach n (ParityQuotient.q n e₁) (ParityQuotient.q n e₂))
    (h : krumEnvelope s) :
    ∃ s' L, EpochRot.Rot s s' L ∧ krumEnvelope s' ∧
      (L : Int) = (NullCoordinates.r e₂ - NullCoordinates.r e₁) +
        (NullCoordinates.l e₂ - NullCoordinates.l e₁) := by
  have hr : Reach e₁ e₂ :=
    ParityQuotient.reach_of_qReach_of_noWinding hsp hn hn2 h₁ h₂ hq
  exact epoch_count_eq_rl hr s h

/-- **Theorem 3.1 (composite).** For even `n ≥ 2`, spacing `sp > 0` and
    `n·sp > 4B`, inside the window `K_B`: (i) the parity sector descends to the
    quotient, (ii) quotient reachability lifts to genuine causal reachability,
    and (iii) the induced epoch rotation count is the sum of the
    null-coordinate increments. -/
theorem theorem31 {n : Nat} {B sp : Int} {e₁ e₂ : Event} {s : EpochState}
    (hnpar : n % 2 = 0) (hsp : 0 < sp) (hn : 4 * B < n * sp) (hn2 : 2 ≤ n)
    (h₁ : ParityQuotient.Window B sp e₁) (h₂ : ParityQuotient.Window B sp e₂)
    (hq : ParityQuotient.QReach n (ParityQuotient.q n e₁) (ParityQuotient.q n e₂))
    (h : krumEnvelope s) :
    (ParityQuotient.q n e₁ = ParityQuotient.q n e₂ → (OnParity e₁ ↔ OnParity e₂)) ∧
      Reach e₁ e₂ ∧
      ∃ s' L, EpochRot.Rot s s' L ∧ krumEnvelope s' ∧
        (L : Int) = (NullCoordinates.r e₂ - NullCoordinates.r e₁) +
          (NullCoordinates.l e₂ - NullCoordinates.l e₁) := by
  refine ⟨ParityQuotient.q_parity (n := n) hnpar (e := e₁) (e' := e₂), ?_, ?_⟩
  · exact ParityQuotient.reach_of_qReach_of_noWinding hsp hn hn2 h₁ h₂ hq
  · exact epoch_count_quotient hsp hn hn2 h₁ h₂ hq h

end CausalMohawkBridge.PreprintBridge

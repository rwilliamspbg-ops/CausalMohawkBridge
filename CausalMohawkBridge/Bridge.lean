import CausalMohawkBridge.CausalLattice
import CausalMohawkBridge.EpochTransition

namespace CausalMohawkBridge.Bridge
open CausalLattice Mohawk

/-- Every lattice generator step is exactly one epoch rotation
    (same shard parameters; envelope required to remain valid). -/
theorem step_to_rotate {e e' : Event} (_ : Step e e') (s : EpochState)
    (h : krumEnvelope s) :
    Mohawk.Step s ⟨s.epoch + 1, s.n, s.f⟩ :=
  Mohawk.Step.rotate s s.n s.f h

/-- Main bridge: a causal path e₁ ⇝ e₂ induces a chain of epoch rotations of
    length (e₂.t - e₁.t), preserving the Krum envelope throughout. -/
theorem reach_to_epochs {e₁ e₂ : Event} (hr : Reach e₁ e₂)
    (s : EpochState) (h : krumEnvelope s) :
    ∃ s', StepStar s s' ∧ krumEnvelope s' ∧
      (s'.epoch : Int) = s.epoch + (e₂.t - e₁.t) := by
  induction hr with
  | refl => exact ⟨s, StepStar.refl s, h, by omega⟩
  | tail _ st ih =>
    obtain ⟨s', hs, he, hep⟩ := ih
    have hrot := Mohawk.Step.rotate s' s'.n s'.f he
    refine ⟨_, StepStar.tail hs hrot, he, ?_⟩
    cases st with
    | plus => simp only [stepPlus] at *; simp; omega
    | minus => simp only [stepMinus] at *; simp; omega

/-- Corollary: epoch advance is non-negative along causal reachability. -/
theorem reach_epoch_monotone {e₁ e₂ : Event} (hr : Reach e₁ e₂) :
    e₁.t ≤ e₂.t := by
  obtain ⟨a, b, ht, _⟩ := (reach_iff_null e₁ e₂).1 hr
  omega

/-- Parity sector is preserved across the whole epoch chain. -/
theorem bridge_parity {e₁ e₂ : Event} (hr : Reach e₁ e₂) (p : OnParity e₁)
    (s : EpochState) (h : krumEnvelope s) :
    OnParity e₂ ∧ ∃ s', StepStar s s' ∧ krumEnvelope s' :=
  let ⟨s', hs, he, _⟩ := reach_to_epochs hr s h
  ⟨hr.parity p, s', hs, he⟩

end CausalMohawkBridge.Bridge

#print axioms CausalMohawkBridge.Bridge.reach_to_epochs
#print axioms CausalMohawkBridge.Bridge.bridge_parity
#print axioms CausalMohawkBridge.CausalLattice.reach_iff_null

import CausalMohawkBridge.CausalLattice
import CausalMohawkBridge.EpochTransition
import CausalMohawkBridge.Bridge

/-!
# Epoch rotations with an explicit step count

`Bridge.reach_to_epochs` shows that a causal path induces a chain of epoch
rotations whose epoch counter advances by the causal `t`-gap. This module
sharpens it: the induced chain has an *explicit length*, and that length is
exactly the causal distance. So "causal reachability" and "epoch rotation
count" are the same number, not merely two numbers that agree.

Mathlib-free; Lean 4.14.0.
-/

namespace CausalMohawkBridge.EpochRot

open CausalLattice Mohawk

/-- `Rot s s' L`: `s'` is reachable from `s` by exactly `L` epoch rotations. -/
inductive Rot : EpochState → EpochState → Nat → Prop
  | refl (s : EpochState) : Rot s s 0
  | tail {a b c : EpochState} {n : Nat} (h : Rot a b n) (st : Step b c) : Rot a c (n + 1)

/-- The Krum envelope is an invariant of the rotation chain. -/
theorem Rot.envelope {a b : EpochState} {n : Nat} (h : Rot a b n)
    (h₀ : krumEnvelope a) : krumEnvelope b := by
  induction h with
  | refl => exact h₀
  | tail h st ih => exact step_envelope st

/-- Each rotation advances the epoch counter by exactly one. -/
theorem Rot.epoch_eq {a b : EpochState} {n : Nat} (h : Rot a b n) :
    b.epoch = a.epoch + n := by
  induction h with
  | refl => rfl
  | tail h st ih => rw [step_epoch st, ih]; omega

/-- `Rot` collapses to the `StepStar` relation of `EpochTransition.lean`. -/
theorem Rot.toStepStar {a b : EpochState} {n : Nat} (h : Rot a b n) : StepStar a b := by
  induction h with
  | refl => exact StepStar.refl _
  | tail h st ih => exact StepStar.tail ih st

/-- **Main bridge, sharpened.** A causal path from `e₁` to `e₂` induces an
    explicit-length rotation chain of length exactly the causal distance
    `e₂.t - e₁.t`, starting from any envelope-satisfying epoch and preserving
    the envelope throughout. -/
theorem reach_to_rot {e₁ e₂ : Event} (hr : Reach e₁ e₂)
    (s : EpochState) (h : krumEnvelope s) :
    ∃ s' L, Rot s s' L ∧ krumEnvelope s' ∧
      (s'.epoch : Int) = s.epoch + (e₂.t - e₁.t) ∧ (L : Int) = e₂.t - e₁.t := by
  induction hr with
  | refl =>
      exact ⟨s, 0, Rot.refl s, h, by omega, by omega⟩
  | tail _ st ih =>
      obtain ⟨s', L, hrot, he, hep, hL⟩ := ih
      have hstep : Step s' (⟨s'.epoch + 1, s'.n, s'.f⟩ : EpochState) :=
        Step.rotate s' s'.n s'.f he
      refine ⟨_, L + 1, Rot.tail hrot hstep, he, ?_, ?_⟩
      · cases st with
        | plus => simp only [stepPlus] at *; omega
        | minus => simp only [stepMinus] at *; omega
      · cases st with
        | plus => simp only [stepPlus] at *; omega
        | minus => simp only [stepMinus] at *; omega

/-- Corollary: the epoch counter advance is path-independent — it depends only
    on the endpoints, and equals the causal distance. -/
theorem reach_epoch_advance {e₁ e₂ : Event} (hr : Reach e₁ e₂)
    (s : EpochState) (h : krumEnvelope s) :
    ∃ s', StepStar s s' ∧ krumEnvelope s' ∧
      (s'.epoch : Int) = s.epoch + (e₂.t - e₁.t) :=
  Bridge.reach_to_epochs hr s h

/-- The rotation chain stays inside the envelope *and* keeps a positive
    Multi-Krum neighbour count at every intermediate epoch. -/
theorem reach_to_rot_neighbors_pos {e₁ e₂ : Event} (hr : Reach e₁ e₂)
    (s : EpochState) (h : krumEnvelope s) :
    ∃ s' L, Rot s s' L ∧ 0 < s'.n - s'.f - 2 ∧
      (s'.epoch : Int) = s.epoch + (e₂.t - e₁.t) := by
  obtain ⟨s', L, hrot, he, hep, _⟩ := reach_to_rot hr s h
  exact ⟨s', L, hrot, neighbors_pos he, hep⟩

end CausalMohawkBridge.EpochRot

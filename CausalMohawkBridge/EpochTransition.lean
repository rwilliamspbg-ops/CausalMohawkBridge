namespace CausalMohawkBridge.Mohawk

/-- Epoch state: active participants `n`, tolerated Byzantine count `f`. -/
structure EpochState where
  epoch : Nat
  n     : Nat
  f     : Nat
  deriving DecidableEq, Repr

/-- Go's MultiKrumSelect safety envelope (matrix row 12): n > 2f + 2. -/
def krumEnvelope (s : EpochState) : Prop := 2 * s.f + 2 < s.n

/-- Neighbour count n - f - 2 is positive inside the envelope. -/
theorem neighbors_pos {s : EpochState} (h : krumEnvelope s) : 0 < s.n - s.f - 2 := by
  unfold krumEnvelope at h; omega

inductive Step : EpochState → EpochState → Prop
  | rotate (s : EpochState) (n' f' : Nat) (h : 2 * f' + 2 < n') :
      Step s ⟨s.epoch + 1, n', f'⟩

inductive StepStar : EpochState → EpochState → Prop
  | refl (s : EpochState) : StepStar s s
  | tail {a b c : EpochState} : StepStar a b → Step b c → StepStar a c

theorem step_envelope {s₁ s₂ : EpochState} (h : Step s₁ s₂) : krumEnvelope s₂ := by
  cases h with
  | rotate n' f' h' => exact h'

theorem step_epoch {s₁ s₂ : EpochState} (h : Step s₁ s₂) : s₂.epoch = s₁.epoch + 1 := by
  cases h; rfl

theorem stepStar_epoch_ge {s₁ s₂ : EpochState} (h : StepStar s₁ s₂) :
    s₁.epoch ≤ s₂.epoch := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ st ih => rw [step_epoch st]; omega

theorem stepStar_envelope {s₁ s₂ : EpochState} (h : StepStar s₁ s₂)
    (h₀ : krumEnvelope s₁) : krumEnvelope s₂ := by
  cases h with
  | refl => exact h₀
  | tail _ st => exact step_envelope st

end CausalMohawkBridge.Mohawk

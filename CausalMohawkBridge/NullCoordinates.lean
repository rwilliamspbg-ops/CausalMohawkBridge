import CausalMohawkBridge.CausalLattice
import CausalMohawkBridge.CausalOrder

/-!
# Null coordinates `r = (t+j)/2`, `l = (t-j)/2`

The Theorem 3.1 formulation of the causal lattice: on the parity sector
`Γ = {t+j even}`, directed reachability is exactly coordinatewise order in the
null coordinates, and each permitted step increments exactly one of them by
one. This is the discrete causal-geometry reading of `CausalLattice.lean`.

`r` and `l` are `Int` (floor division by 2); on `Γ` they are the exact halves
`u/2` and `v/2`.
-/

namespace CausalMohawkBridge.NullCoordinates

open CausalLattice

/-- Null coordinate `r = (t+j)/2`. -/
def r (e : Event) : Int := u e / 2

/-- Null coordinate `l = (t-j)/2`. -/
def l (e : Event) : Int := v e / 2

/-- A `+1` spatial step increments `r` and fixes `l`. -/
theorem stepPlus_r (e : Event) : r (stepPlus e) = r e + 1 := by
  simp only [r, u, stepPlus]; omega

theorem stepPlus_l (e : Event) : l (stepPlus e) = l e := by
  simp only [l, v, stepPlus]; omega

/-- A `-1` spatial step fixes `r` and increments `l`. -/
theorem stepMinus_r (e : Event) : r (stepMinus e) = r e := by
  simp only [r, u, stepMinus]; omega

theorem stepMinus_l (e : Event) : l (stepMinus e) = l e + 1 := by
  simp only [l, v, stepMinus]; omega

/-- Each permitted step increments exactly one null coordinate by one. -/
theorem step_null (e e' : Event) (h : Step e e') :
    (r e' = r e + 1 ∧ l e' = l e) ∨ (r e' = r e ∧ l e' = l e + 1) := by
  cases h with
  | plus => exact Or.inl ⟨stepPlus_r e, stepPlus_l e⟩
  | minus => exact Or.inr ⟨stepMinus_r e, stepMinus_l e⟩

/-- Time advance equals the sum of the two null-coordinate increments. -/
theorem step_t_eq (e e' : Event) (h : Step e e') :
    (e'.t - e.t : Int) = (r e' - r e) + (l e' - l e) := by
  cases h with
  | plus => simp only [stepPlus, r, l, u, v]; omega
  | minus => simp only [stepMinus, r, l, u, v]; omega

/-- **Theorem 3.1(i) analogue.** On the parity sector `Γ`, reachability is
    exactly coordinatewise order in the null coordinates. -/
theorem reach_iff_rl_order {e₁ e₂ : Event} (hp₁ : OnParity e₁) (hp₂ : OnParity e₂) :
    Reach e₁ e₂ ↔ r e₁ ≤ r e₂ ∧ l e₁ ≤ l e₂ := by
  have hu₁ : (e₁.t + e₁.j) % 2 = 0 := hp₁
  have hu₂ : (e₂.t + e₂.j) % 2 = 0 := hp₂
  rw [CausalOrder.reach_iff_uv_order]
  constructor
  · rintro ⟨huv, hvv, _⟩
    simp only [r, l, u, v] at huv hvv ⊢
    omega
  · rintro ⟨hr, hl⟩
    simp only [r, l, u, v] at hr hl
    simp only [u, v]
    have huv : e₁.t + e₁.j ≤ e₂.t + e₂.j := by omega
    have hvv : e₁.t - e₁.j ≤ e₂.t - e₂.j := by omega
    refine ⟨huv, hvv, ?_⟩
    refine ⟨(e₂.t + e₂.j) / 2 - (e₁.t + e₁.j) / 2, ?_⟩
    omega

/-- Causal distance is the sum of the null-coordinate increments. -/
theorem reach_t_eq_rl {e₁ e₂ : Event} (h : Reach e₁ e₂) :
    (e₂.t - e₁.t : Int) = (r e₂ - r e₁) + (l e₂ - l e₁) := by
  obtain ⟨a, b, ht, hj⟩ := (reach_iff_null e₁ e₂).1 h
  simp only [r, l, u, v]
  omega

/-- Reachability is a partial order on `Γ`: antisymmetry. -/
theorem reach_antisymm {e₁ e₂ : Event} (hp₁ : OnParity e₁) (hp₂ : OnParity e₂)
    (h₁₂ : Reach e₁ e₂) (h₂₁ : Reach e₂ e₁) : e₁ = e₂ := by
  have h₁ := (reach_iff_rl_order hp₁ hp₂).mp h₁₂
  have h₂ := (reach_iff_rl_order hp₂ hp₁).mp h₂₁
  cases e₁ with
  | mk t₁ j₁ =>
    cases e₂ with
    | mk t₂ j₂ =>
      simp only [OnParity, u, v, r, l] at hp₁ hp₂ h₁ h₂
      have ht : t₁ = t₂ := by omega
      have hj : j₁ = j₂ := by omega
      rw [ht, hj]

end CausalMohawkBridge.NullCoordinates

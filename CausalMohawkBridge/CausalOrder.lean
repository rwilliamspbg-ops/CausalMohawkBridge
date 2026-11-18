import CausalMohawkBridge.CausalLattice

/-!
# Causal order structure on the lattice

New results about the causal lattice in `CausalLattice.lean`, obtained by
combining it with the Sovereign-Mohawk-Proto null-coordinate / Krum
vocabulary. The headline is a strengthening of the existing
`reach_iff_null`: generator reachability is *exactly* the product order on
the two null coordinates `u = t + j`, `v = t - j`, up to the parity of the
`u`-gap.

Everything here is Mathlib-free and compiles on Lean 4.14.0.
-/

namespace CausalMohawkBridge.CausalOrder
open CausalLattice

/-- Even integer, defined locally so the development stays Mathlib-free. -/
def EvenZ (z : Int) : Prop := ∃ k : Int, z = 2 * k

/-- `% 2 = 0` is the same as being twice an integer. -/
theorem evenZ_of_emod_two {z : Int} (h : z % 2 = 0) : EvenZ z :=
  Int.dvd_iff_emod_eq_zero (a := 2) (b := z) |>.mpr h

/-- **Null-coordinate order.** `NullReachable e₁ e₂` holds iff both null
    coordinates are non-decreasing and the `u`-gap is even.

    The parity clause is a genuine obstruction, not decoration: `(1, 0)`
    dominates `(0, 0)` in both null coordinates (`u`: 0→1, `v`: 0→1) but is
    not generator-reachable, because a single generator step changes `u` by
    `±2`. -/
theorem null_iff_uv_order {e₁ e₂ : Event} :
    NullReachable e₁ e₂ ↔ u e₁ ≤ u e₂ ∧ v e₁ ≤ v e₂ ∧ EvenZ (u e₂ - u e₁) := by
  constructor
  · intro h
    obtain ⟨a, b, ht, hj⟩ := h
    have ha : (a : Int) ≥ 0 := Int.ofNat_nonneg a
    have hb : (b : Int) ≥ 0 := Int.ofNat_nonneg b
    have hdu : u e₂ - u e₁ = 2 * (a : Int) := by simp only [u]; omega
    have hdv : v e₂ - v e₁ = 2 * (b : Int) := by simp only [v]; omega
    exact ⟨by omega, by omega, a, hdu⟩
  · intro h
    obtain ⟨huv, hvv, k, hk⟩ := h
    simp only [u, v] at huv hvv hk
    have hk0 : 0 ≤ k := by omega
    have hz : 0 ≤ e₂.t - e₁.t - k := by omega
    have h1 : (k.toNat : Int) = k := Int.toNat_of_nonneg hk0
    have h2 : ((e₂.t - e₁.t - k).toNat : Int) = e₂.t - e₁.t - k := Int.toNat_of_nonneg hz
    refine ⟨k.toNat, (e₂.t - e₁.t - k).toNat, ?_, ?_⟩
    · rw [h1, h2]; omega
    · rw [h1, h2]; omega

/-- **Reachability = null-coordinate order.** The strengthening of
    `reach_iff_null` promised above. -/
theorem reach_iff_uv_order {e₁ e₂ : Event} :
    Reach e₁ e₂ ↔ u e₁ ≤ u e₂ ∧ v e₁ ≤ v e₂ ∧ EvenZ (u e₂ - u e₁) :=
  (reach_iff_null e₁ e₂).trans null_iff_uv_order

/-- Inside a parity sector, the parity clause becomes `OnParity e₂` and the
    characterization is pure product order. -/
theorem reach_iff_uv_order_of_parity {e₁ e₂ : Event} (hp : OnParity e₁) :
    Reach e₁ e₂ ↔ u e₁ ≤ u e₂ ∧ v e₁ ≤ v e₂ ∧ OnParity e₂ := by
  constructor
  · intro h
    obtain ⟨huv, hvv, _⟩ := (reach_iff_uv_order.mp h)
    exact ⟨huv, hvv, Reach.parity h hp⟩
  · rintro ⟨huv, hvv, hp₂⟩
    have hdvd : (2 : Int) ∣ u e₂ - u e₁ := by
      have h1 : (2 : Int) ∣ u e₁ := Int.dvd_iff_emod_eq_zero (a := 2) (b := u e₁) |>.mpr hp
      have h2 : (2 : Int) ∣ u e₂ := Int.dvd_iff_emod_eq_zero (a := 2) (b := u e₂) |>.mpr hp₂
      exact Int.dvd_sub h2 h1
    exact (reach_iff_uv_order.mpr ⟨huv, hvv, hdvd⟩)

/-- The `u`- and `v`-gaps have the same parity, so the parity clause may be
    stated on either coordinate. -/
theorem null_iff_uv_order' {e₁ e₂ : Event} :
    NullReachable e₁ e₂ ↔ u e₁ ≤ u e₂ ∧ v e₁ ≤ v e₂ ∧ EvenZ (v e₂ - v e₁) := by
  constructor
  · intro h
    obtain ⟨huv, hvv, k, hk⟩ := (null_iff_uv_order.mp h)
    have hdv : v e₂ - v e₁ = 2 * (e₂.t - e₁.t - k) := by
      simp only [u, v] at hk ⊢
      omega
    exact ⟨huv, hvv, e₂.t - e₁.t - k, hdv⟩
  · intro h
    obtain ⟨huv, hvv, k, hk⟩ := h
    have hdu : u e₂ - u e₁ = 2 * (e₂.t - e₁.t - k) := by
      simp only [u, v] at hk ⊢
      omega
    exact (null_iff_uv_order.mpr ⟨huv, hvv, e₂.t - e₁.t - k, hdu⟩)

/-- Composability: reachable pairs compose, and the composite's causal
    distance is the sum of the parts. -/
theorem reach_trans_dist {e₁ e₂ e₃ : Event} (h₁₂ : Reach e₁ e₂) (h₂₃ : Reach e₂ e₃) :
    Reach e₁ e₃ ∧ (e₃.t - e₁.t : Int) = (e₂.t - e₁.t) + (e₃.t - e₂.t) := by
  exact ⟨Reach.trans h₁₂ h₂₃, by omega⟩

/-- Causal distance is non-negative and coincides with the number of generator
    steps in any path realizing the reachability. -/
theorem causalDist_nonneg {e₁ e₂ : Event} (h : Reach e₁ e₂) : 0 ≤ e₂.t - e₁.t := by
  obtain ⟨a, b, ht, _⟩ := (reach_iff_null e₁ e₂).1 h
  omega

end CausalMohawkBridge.CausalOrder

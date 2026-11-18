import CausalMohawkBridge.CausalLattice
import CausalMohawkBridge.NullCoordinates

/-!
# Spatial parity quotient `j mod n` and the no-winding condition

The Theorem 3.1 parity-quotient construction: events live on the lifted
parity lattice `Γ = {t+j even}`, time is unwrapped, and space is identified
modulo an even `n ≥ 4`. Evenness preserves the parity sector; a bounded
observation window plus `n > 4B` (the discrete `ℓ_n > 4B`) prevents the
quotient from introducing causal relations that are absent from the lift.

Mathlib-free; Lean 4.14.0.
-/

namespace CausalMohawkBridge.ParityQuotient

open CausalLattice

/-- Quotient event: unwrapped time, spatial coordinate reduced mod `n`. -/
structure QEvent where
  t : Int
  j : Int

/-- Spatial quotient map: time untouched, `j` reduced mod `n`. -/
def q (n : Nat) (e : Event) : QEvent := ⟨e.t, e.j % (n : Int)⟩

/-- One quotient step: time `+1`, space `±1` mod `n`. -/
inductive QStep (n : Nat) : QEvent → QEvent → Prop
  | plus (a : QEvent) : QStep n a ⟨a.t + 1, (a.j + 1) % (n : Int)⟩
  | minus (a : QEvent) : QStep n a ⟨a.t + 1, (a.j - 1) % (n : Int)⟩

/-- Reflexive-transitive closure of the quotient step. -/
inductive QReach (n : Nat) : QEvent → QEvent → Prop
  | refl (a : QEvent) : QReach n a a
  | tail {a b c : QEvent} : QReach n a b → QStep n b c → QReach n a c

/-- Physical observation window `K_B = [-B,B]²` with lattice spacing `sp`:
    `sp * e.t` and `sp * e.j` are the physical coordinates of `e`, and `B` is
    the window half-width in physical units. The circumference is `n * sp`, so
    `4 * B < n * sp` is the discrete `ℓ_n = n · a_n > 4B` with `a_n = sp`. -/
def Window (B sp : Int) (e : Event) : Prop :=
  -B ≤ sp * e.t ∧ sp * e.t ≤ B ∧ -B ≤ sp * e.j ∧ sp * e.j ≤ B

/-! ## Modular helpers -/

private theorem emod_add_one {n : Int} (hn : 1 < n) (a : Int) :
    (a + 1) % n = ((a % n) + 1) % n := by
  rw [Int.add_emod,
    Int.emod_eq_of_lt (a := 1) (b := n) (by omega : (0:Int) ≤ 1) hn]

private theorem emod_sub_one {n : Int} (hn : 1 < n) (a : Int) :
    (a - 1) % n = ((a % n) - 1) % n := by
  rw [Int.sub_emod,
    Int.emod_eq_of_lt (a := 1) (b := n) (by omega : (0:Int) ≤ 1) hn]

/-! ## Quotient homomorphism -/

theorem q_stepPlus {n : Nat} (hn : 2 ≤ n) (e : Event) :
    q n (stepPlus e) = ⟨e.t + 1, ((q n e).j + 1) % (n : Int)⟩ := by
  simp only [q, stepPlus]
  congr 1
  exact emod_add_one (by omega) e.j

theorem q_stepMinus {n : Nat} (hn : 2 ≤ n) (e : Event) :
    q n (stepMinus e) = ⟨e.t + 1, ((q n e).j - 1) % (n : Int)⟩ := by
  simp only [q, stepMinus]
  congr 1
  exact emod_sub_one (by omega) e.j

theorem q_stepPlus' {n : Nat} (hn : 2 ≤ n) {e : Event} {b : QEvent}
    (h : q n e = b) :
    q n (stepPlus e) = ⟨b.t + 1, (b.j + 1) % (n : Int)⟩ := by
  rw [q_stepPlus hn e, h]
  rw [show e.t = b.t from congrArg QEvent.t h]

theorem q_stepMinus' {n : Nat} (hn : 2 ≤ n) {e : Event} {b : QEvent}
    (h : q n e = b) :
    q n (stepMinus e) = ⟨b.t + 1, (b.j - 1) % (n : Int)⟩ := by
  rw [q_stepMinus hn e, h]
  rw [show e.t = b.t from congrArg QEvent.t h]

theorem step_to_qStep {n : Nat} (hn : 2 ≤ n) {e e' : Event} (h : Step e e') :
    QStep n (q n e) (q n e') := by
  cases h with
  | plus => rw [q_stepPlus hn e]; exact QStep.plus (q n e)
  | minus => rw [q_stepMinus hn e]; exact QStep.minus (q n e)

/-- Every lifted causal path projects to a quotient path. -/
theorem reach_to_qReach {n : Nat} (hn : 2 ≤ n) {e₁ e₂ : Event}
    (h : Reach e₁ e₂) : QReach n (q n e₁) (q n e₂) := by
  induction h with
  | refl => exact QReach.refl _
  | tail _ st ih => exact QReach.tail ih (step_to_qStep hn st)

/-! ## Evenness preserves the parity sector -/

/-- For even `n`, quotient-equivalent events lie in the same parity sector. -/
theorem q_parity {n : Nat} (hn : n % 2 = 0) {e e' : Event}
    (hq : q n e = q n e') : OnParity e ↔ OnParity e' := by
  have ht : e.t = e'.t := congrArg QEvent.t hq
  have hj : e.j % (n : Int) = e'.j % (n : Int) := congrArg QEvent.j hq
  have hdiv : (n : Int) ∣ (e'.j - e.j) := by
    have hmod : (e'.j - e.j) % (n : Int) = 0 := by
      rw [Int.sub_emod, hj, Int.sub_self, Int.zero_emod]
    exact Int.dvd_iff_emod_eq_zero.mpr hmod
  have h2n : (2 : Int) ∣ (n : Int) := by
    have hmod : (n : Int) % (2 : Int) = 0 := by
      have h := Int.ofNat_emod n 2
      rw [hn] at h
      exact h.symm
    exact Int.dvd_iff_emod_eq_zero.mpr hmod
  have h2 : (2 : Int) ∣ (e'.j - e.j) := Int.dvd_trans h2n hdiv
  have hdiff : u e' - u e = e'.j - e.j := by simp only [u]; omega
  constructor
  · intro hp
    unfold OnParity
    have h0 : (u e' - u e) % 2 = 0 := by
      rw [hdiff]
      exact Int.dvd_iff_emod_eq_zero.mp h2
    unfold OnParity at hp
    omega
  · intro hp
    unfold OnParity
    have h0 : (u e - u e') % 2 = 0 := by
      rw [show u e - u e' = -(u e' - u e) by omega, hdiff]
      exact Int.dvd_iff_emod_eq_zero.mp (Int.dvd_neg.mpr h2)
    unfold OnParity at hp
    omega

/-! ## No-winding -/

theorem eq_zero_of_dvd_of_abs_lt {n : Int} {d : Int}
    (hd : n ∣ d) (h : -n < d ∧ d < n) : d = 0 := by
  rcases Int.lt_trichotomy d 0 with hd0 | rfl | hd0
  · have hpos : 0 < -d := by omega
    have hle : n ≤ -d := Int.le_of_dvd hpos (Int.dvd_neg.mpr hd)
    omega
  · rfl
  · have hle : n ≤ d := Int.le_of_dvd hd0 hd
    omega

/-- A causal path of length `Δt` moves the spatial coordinate by at most `Δt`. -/
theorem reach_j_bound {e₁ e₂ : Event} (h : Reach e₁ e₂) :
    -(e₂.t - e₁.t : Int) ≤ e₂.j - e₁.j ∧ e₂.j - e₁.j ≤ (e₂.t - e₁.t : Int) := by
  induction h with
  | refl => omega
  | tail _ st ih =>
      cases st with
      | plus => simp only [stepPlus]; omega
      | minus => simp only [stepMinus]; omega

/-- A causal path of length `Δt` moves the spatial coordinate by at most
    `Δt`, scaled by the lattice spacing. -/
theorem reach_j_bound_smul {sp : Int} (hsp : 0 < sp) {e₁ e₂ : Event}
    (h : Reach e₁ e₂) :
    -(sp * (e₂.t - e₁.t)) ≤ sp * (e₂.j - e₁.j) ∧
      sp * (e₂.j - e₁.j) ≤ sp * (e₂.t - e₁.t) := by
  obtain ⟨h1, h2⟩ := reach_j_bound h
  have h3 : sp * (-(e₂.t - e₁.t)) ≤ sp * (e₂.j - e₁.j) :=
    Int.mul_le_mul_of_nonneg_left h1 (by omega : (0:Int) ≤ sp)
  have h4 : sp * (e₂.j - e₁.j) ≤ sp * (e₂.t - e₁.t) :=
    Int.mul_le_mul_of_nonneg_left h2 (by omega : (0:Int) ≤ sp)
  rw [Int.mul_neg] at h3
  exact ⟨h3, h4⟩

/-- A quotient path lifts to a genuine causal path with the same endpoints
    modulo the spatial identification. -/
theorem qReach_lift {n : Nat} (hn : 2 ≤ n) {e₁ : Event} {b : QEvent}
    (h : QReach n (q n e₁) b) :
    ∃ e₂', Reach e₁ e₂' ∧ q n e₂' = b := by
  induction h with
  | refl => exact ⟨e₁, Reach.refl e₁, rfl⟩
  | tail hq hs ih =>
      obtain ⟨e', hre', hqe'⟩ := ih
      cases hs with
      | plus =>
          exact ⟨stepPlus e', Reach.tail hre' (Step.plus e'), q_stepPlus' hn hqe'⟩
      | minus =>
          exact ⟨stepMinus e', Reach.tail hre' (Step.minus e'), q_stepMinus' hn hqe'⟩

/-- **No-winding / no-new-causal-relations.** Inside the physical window
    `K_B = [-B,B]²` (lattice spacing `sp`), if the circumference `n·sp`
    exceeds `4B`, quotient reachability implies genuine lifted reachability.
    This is the discrete `ℓ_n = n·a_n > 4B` condition with `a_n = sp`. -/
theorem reach_of_qReach_of_noWinding {n : Nat} {B sp : Int} {e₁ e₂ : Event}
    (hsp : 0 < sp) (hn : 4 * B < n * sp) (hn2 : 2 ≤ n)
    (h₁ : Window B sp e₁) (h₂ : Window B sp e₂)
    (h : QReach n (q n e₁) (q n e₂)) : Reach e₁ e₂ := by
  obtain ⟨e₂', hre', hq'⟩ := qReach_lift hn2 h
  have ht : e₂'.t = e₂.t := congrArg QEvent.t hq'
  have hjmod : e₂'.j % (n : Int) = e₂.j % (n : Int) := congrArg QEvent.j hq'
  have hdiv : (n : Int) ∣ (e₂'.j - e₂.j) := by
    have hmod : (e₂'.j - e₂.j) % (n : Int) = 0 := by
      rw [Int.sub_emod, hjmod, Int.sub_self, Int.zero_emod]
    exact Int.dvd_iff_emod_eq_zero.mpr hmod
  have hjb : -(sp * (e₂'.t - e₁.t)) ≤ sp * (e₂'.j - e₁.j) ∧
      sp * (e₂'.j - e₁.j) ≤ sp * (e₂'.t - e₁.t) :=
    reach_j_bound_smul hsp hre'
  have hL : sp * (e₂'.t - e₁.t) ≤ 2 * B := by
    unfold Window at h₁ h₂
    rw [Int.mul_sub, ht]
    omega
  have hL' : -2 * B ≤ sp * (e₂'.t - e₁.t) := by
    unfold Window at h₁ h₂
    rw [Int.mul_sub, ht]
    omega
  have hjbound : -4 * B ≤ sp * (e₂'.j - e₂.j) ∧
      sp * (e₂'.j - e₂.j) ≤ 4 * B := by
    unfold Window at h₁ h₂
    rw [Int.mul_sub]
    have hsplit : sp * e₂'.j = sp * e₁.j + sp * (e₂'.j - e₁.j) := by
      rw [← Int.mul_add]; congr 1; omega
    omega
  have hjlt : -(n * sp : Int) < sp * (e₂'.j - e₂.j) ∧
      sp * (e₂'.j - e₂.j) < n * sp := by
    have hnsp : 0 < n * sp := Int.mul_pos (by omega) hsp
    omega
  have hwind : (n * sp : Int) ∣ sp * (e₂'.j - e₂.j) := by
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨k, ?_⟩
    rw [hk, ← Int.mul_assoc, Int.mul_comm sp (↑n)]
  have hzero : sp * (e₂'.j - e₂.j) = 0 :=
    eq_zero_of_dvd_of_abs_lt hwind hjlt
  have hj : e₂'.j = e₂.j := by
    rcases Int.mul_eq_zero.mp hzero with h | h
    · exact absurd h (Int.ne_of_gt hsp)
    · omega
  cases e₂'
  case mk t₂' j₂' =>
    cases e₂
    case mk t₂ j₂ =>
      simp only at ht hj
      rw [ht, hj] at hre'
      exact hre'

/-- The `sp = 1` case recovers the unit-lattice window. -/
theorem reach_of_qReach_of_noWinding_unit {n : Nat} {B : Int} {e₁ e₂ : Event}
    (hn : 4 * B < n) (hn2 : 2 ≤ n)
    (h₁ : Window B 1 e₁) (h₂ : Window B 1 e₂)
    (h : QReach n (q n e₁) (q n e₂)) : Reach e₁ e₂ :=
  reach_of_qReach_of_noWinding (sp := 1) (by omega) (by omega) hn2 h₁ h₂ h

/-! ## Negative controls (the hypotheses are load-bearing) -/

/-- **Negative control.** Without `4B < n·sp` the no-winding lift fails: the
    two events below are quotient-equivalent (same `t`, `j` differing by `n`),
    so a trivial quotient path joins them, but no lifted causal path does. -/
theorem noWinding_hypothesis_load_bearing {n : Nat} (hn : 2 ≤ n) :
    QReach n (q n (⟨0, 0⟩ : Event)) (q n (⟨0, n⟩ : Event)) ∧
      Window n 1 (⟨0, n⟩ : Event) ∧ Window n 1 (⟨0, 0⟩ : Event) ∧
      ¬ Reach (⟨0, 0⟩ : Event) (⟨0, n⟩ : Event) := by
  have hq : q n (⟨0, 0⟩ : Event) = q n (⟨0, n⟩ : Event) := by
    simp [q]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq]; exact QReach.refl _
  · unfold Window; dsimp only; omega
  · unfold Window; dsimp only; omega
  · intro h
    have hnull : NullReachable (⟨0, 0⟩ : Event) (⟨0, n⟩ : Event) :=
      (reach_iff_null _ _).mp h
    obtain ⟨a, b, ht, hj⟩ := hnull
    simp only at ht hj
    omega

/-- **Negative control.** `q_parity` fails for odd `n`: `q 3` identifies
    `(0,0)` and `(0,3)`, which lie in different parity sectors. -/
theorem q_parity_odd_counterexample :
    q 3 (⟨0, 0⟩ : Event) = q 3 (⟨0, 3⟩ : Event) ∧
      ¬ (OnParity (⟨0, 0⟩ : Event) ↔ OnParity (⟨0, 3⟩ : Event)) := by
  simp [q, OnParity, u]

end CausalMohawkBridge.ParityQuotient

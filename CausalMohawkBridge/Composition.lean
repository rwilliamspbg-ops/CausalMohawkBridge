import CausalMohawkBridge.CausalLattice
import CausalMohawkBridge.EpochTransition
import CausalMohawkBridge.NullCoordinates
import CausalMohawkBridge.Lorentz
import CausalMohawkBridge.Chernoff

/-!
# A shared abstract structure for local-to-global composition

The preprint's Theorem 5.2 and this project's hierarchical composition
question both ask: *which locally-established invariants survive composition?*
This module fixes one abstract vocabulary for that question and instantiates it
on the deterministic settings formalised here:

* `Sys σ` — a state space, an admissible transition, and a state invariant;
* `QSys σ` — a state space, a *simultaneous* transition on pairs, and a binary
  quantity meant to be preserved by such a transition.

The exponential tail bound that the probabilistic repair needs is *proved*
in `Chernoff.lean` (`Chernoff.tail_bound`), not assumed: the binomial identity
and the tail inequality are discharged on this Mathlib-free toolchain. The
final normalisation step — turning the tail bound into a failure-probability
threshold — is also machine-checked: `chernoff_probability_bound` clears the
`2^m` denominator (`f · 2^(m+k) ≤ 2^m · 3^m`), i.e.
`f / 2^m ≤ (3/4)^m · 2^(m-k)`, and `chernoff_probability_tail` instantiates it
at the binomial tail.

Mathlib-free; Lean 4.14.0.
-/

namespace CausalMohawkBridge.Composition

open CausalLattice Mohawk

/-- Reflexive-transitive closure of an abstract transition. -/
inductive ReachStar {σ : Type} (step : σ → σ → Prop) : σ → σ → Prop
  | refl (s : σ) : ReachStar step s s
  | tail {a b c : σ} : ReachStar step a b → step b c → ReachStar step a c

/-- A state system with an invariant predicate. -/
structure Sys (σ : Type) where
  step : σ → σ → Prop
  inv : σ → Prop

/-- The invariant is preserved by one transition. -/
def preserves (S : Sys σ) : Prop := ∀ s s', S.step s s' → S.inv s → S.inv s'

/-- The invariant is preserved by any finite chain of transitions. -/
def preservesStar (S : Sys σ) : Prop :=
  ∀ s s', ReachStar S.step s s' → S.inv s → S.inv s'

theorem preservesStar_of_preserves {σ : Type} (S : Sys σ) (h : preserves S) :
    preservesStar S := by
  intro s s' hr
  induction hr with
  | refl => exact id
  | tail _ st ih => intro hs; exact h _ _ st (ih hs)

/-- A system with a simultaneous transition on pairs and a binary quantity
    preserved by it. -/
structure QSys (σ : Type) where
  pstep : σ × σ → σ × σ → Prop
  val : σ → σ → Int

def qPreserves (Q : QSys σ) : Prop :=
  ∀ p q p' q', Q.pstep (p, q) (p', q') → Q.val p' q' = Q.val p q

/-! ## Instance 1: the causal parity sector -/

def causalSys : Sys Event where
  step := Step
  inv := OnParity

theorem causalSys_preserves : preserves causalSys := by
  intro e e' h hp
  cases h with
  | plus => exact stepPlus_parity e hp
  | minus => exact stepMinus_parity e hp

/-! ## Instance 2: the epoch Krum envelope -/

def epochSys : Sys EpochState where
  step := Step
  inv := krumEnvelope

theorem epochSys_preserves : preserves epochSys := by
  intro s s' h hs
  exact step_envelope h

/-! ## Instance 3: the Minkowski interval under a common Lorentz map -/

def lorentzQSys : QSys (Int × Int) where
  pstep := fun p q => ∃ L : Lorentz.ALorentz, q.1 = L.apply p.1 ∧ q.2 = L.apply p.2
  val := fun p q => Lorentz.Q (Lorentz.psub p q)

theorem lorentzQSys_preserves : qPreserves lorentzQSys := by
  intro p q p' q' hp
  obtain ⟨L, h1, h2⟩ := hp
  rw [show p' = L.apply p from h1, show q' = L.apply q from h2]
  exact Lorentz.Q_apply_sub L p q

/-- Preservation up to a positive integer scale factor. Exact `qPreserves` is
    the `c = 1` case; rational Lorentz maps scale the interval by `N²`, so they
    satisfy this instead. -/
def qPreservesScaled (Q : QSys σ) : Prop :=
  ∀ p q p' q', Q.pstep (p, q) (p', q') →
    ∃ c : Int, 0 < c ∧ Q.val p' q' = c * Q.val p q

/-! ## Instance 3b: the non-degenerate (rational) Lorentz maps -/

/-- `ScaledLorentz` represents a rational affine Lorentz map; unlike the
    degenerate integer `ALorentz`, its linear part is non-trivial. -/
def scaledLorentzQSys : QSys (Int × Int) where
  pstep := fun p q => ∃ L : Lorentz.ScaledLorentz,
    q.1 = L.apply p.1 ∧ q.2 = L.apply p.2
  val := fun p q => Lorentz.Q (Lorentz.psub p q)

theorem scaledLorentzQSys_preserves : qPreservesScaled scaledLorentzQSys := by
  intro p q p' q' hp
  obtain ⟨L, h1, h2⟩ := hp
  refine ⟨L.N ^ 2, ?_, ?_⟩
  · rw [show (2 : Nat) = 1 + 1 from rfl, Int.pow_succ,
      show (1 : Nat) = 0 + 1 from rfl, Int.pow_succ, Int.pow_zero, Int.one_mul]
    exact Int.mul_pos L.hN L.hN
  · rw [show p' = L.apply p from h1, show q' = L.apply q from h2]
    dsimp only [scaledLorentzQSys]
    exact Lorentz.Q_scaled L p q

/-! ## Instance 4: the null-coordinate increment along a causal path -/
def nullQSys : QSys Event where
  pstep := fun p q => Step p.1 q.1 ∧ Step p.2 q.2
  val := fun p q =>
    (NullCoordinates.r q - NullCoordinates.r p) +
      (NullCoordinates.l q - NullCoordinates.l p)

theorem nullQSys_preserves : qPreserves nullQSys := by
  intro p q p' q' hp
  obtain ⟨hp₁, hp₂⟩ := hp
  cases hp₁ with
  | plus =>
      cases hp₂ with
      | plus =>
          change nullQSys.val (stepPlus p) (stepPlus q) = nullQSys.val p q
          simp only [nullQSys, NullCoordinates.stepPlus_r, NullCoordinates.stepPlus_l]
          omega
      | minus =>
          change nullQSys.val (stepPlus p) (stepMinus q) = nullQSys.val p q
          simp only [nullQSys, NullCoordinates.stepPlus_r, NullCoordinates.stepPlus_l,
            NullCoordinates.stepMinus_r, NullCoordinates.stepMinus_l]
          omega
  | minus =>
      cases hp₂ with
      | plus =>
          change nullQSys.val (stepMinus p) (stepPlus q) = nullQSys.val p q
          simp only [nullQSys, NullCoordinates.stepMinus_r, NullCoordinates.stepMinus_l,
            NullCoordinates.stepPlus_r, NullCoordinates.stepPlus_l]
          omega
      | minus =>
          change nullQSys.val (stepMinus p) (stepMinus q) = nullQSys.val p q
          simp only [nullQSys, NullCoordinates.stepMinus_r, NullCoordinates.stepMinus_l]
          omega

/-! ## The probabilistic instance (hypothesis) -/

/-- A probabilistic system: a state system plus a failure counter. -/
structure ProbSys (σ : Type) where
  sys : Sys σ
  fail : σ → Nat

/-- The repair hypothesis on the failure **count**: along any chain the counter
    stays at or below `bound`. This is a raw count, not a probability — for the
    binomial tail `3^m` is exponentially *large*, so do not read it as a
    probability bound. -/
def probRepair (P : ProbSys σ) (bound : Nat) : Prop :=
  ∀ s s', ReachStar P.sys.step s s' → P.sys.inv s → P.fail s' ≤ bound

/-- The failure-**probability** bound, in cleared-integer form. A counter `f`
    with `f · 2^(m+k) ≤ 2^m · 3^m` gives
    `f / 2^m ≤ 3^m / 2^(m+k) = (3/4)^m · 2^(m-k)`, i.e. the probability that
    the counter reaches the threshold `k` out of `m` trials decays
    exponentially in `k`. -/
def probRepairProb (P : ProbSys σ) (m k : Nat) : Prop :=
  ∀ s s', ReachStar P.sys.step s s' → P.sys.inv s →
    P.fail s' * 2 ^ (m + k) ≤ 2 ^ m * 3 ^ m

/-- A uniform bound on the failure counter yields the repair hypothesis. -/
theorem probRepair_of_le {σ : Type} (P : ProbSys σ) {b : Nat}
    (h : ∀ s, P.fail s ≤ b) : probRepair P b := by
  intro s s' _ _; exact h s'

/-- The binomial-tail failure system on the unit state space. -/
def tailProbSys (m k : Nat) : ProbSys Unit where
  sys := { step := fun _ _ => False, inv := fun _ => True }
  fail := fun _ => Chernoff.tailNat k m

/-- Its failure counter satisfies the count repair hypothesis with the
    Chernoff tail bound `3^m`. -/
theorem tailProbSys_repair (m k : Nat) :
    probRepair (tailProbSys m k) (3 ^ m) := by
  intro s s' _ _
  exact Chernoff.tailNat_le m k

/-- Its failure counter satisfies the cleared probability bound. -/
theorem tailProbSys_prob (m k : Nat) :
    probRepairProb (tailProbSys m k) m k := by
  intro s s' _ _
  exact Chernoff.tailNat_cleared m k

/-- **Chernoff tail bound, `z = 2`.** The upper tail of the binomial
    distribution satisfies `2^k · ∑_{i≥k} C(m,i) ≤ 3^m`; after dividing by
    `2^m` this is `P(X ≥ k) ≤ (3/4)^m · 2^{m-k}`. -/
theorem chernoff_tail_two (m k : Nat) : (2 : Int) ^ k * Chernoff.tail k m ≤ 3 ^ m :=
  Chernoff.tail_bound m k (by omega)

/-- **Cleared-denominator comparison (integer form of the failure-probability
    bound).** A failure numerator `f` with `2^k · f ≤ 3^m` satisfies
    `f · 2^(m+k) ≤ 2^m · 3^m`; dividing by `2^(m+k)` (equivalently, clearing
    the probability denominator `2^m`) gives
    `f / 2^m ≤ 3^m / 2^(m+k) = (3/4)^m · 2^(m-k)`. -/
theorem chernoff_probability_bound {m k : Nat} {f : Int}
    (hf : (2 : Int) ^ k * f ≤ 3 ^ m) :
    f * 2 ^ (m + k) ≤ 2 ^ m * 3 ^ m := by
  have h : (2 : Int) ^ k * f * 2 ^ m ≤ 3 ^ m * 2 ^ m :=
    Int.mul_le_mul_of_nonneg_right hf
      (Chernoff.pow_nonneg (by omega : (0 : Int) ≤ 2) m)
  rw [Chernoff.pow_add (2 : Int) m k]
  simp only [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] at h ⊢
  omega

/-- The comparison instantiated at the binomial tail. -/
theorem chernoff_probability_tail (m k : Nat) :
    Chernoff.tail k m * 2 ^ (m + k) ≤ 2 ^ m * 3 ^ m :=
  chernoff_probability_bound (Chernoff.tail_bound m k (by omega))

/-- The same comparison in the `2^m · fail_num ≤ fail_den · 3^m` shape, with
    `fail_num = 2^k · f` and `fail_den = 2^m`. -/
theorem chernoff_probability_form {m k : Nat} {f : Int}
    (hf : (2 : Int) ^ k * f ≤ 3 ^ m) :
    (2 : Int) ^ m * ((2 : Int) ^ k * f) ≤ (2 : Int) ^ m * 3 ^ m :=
  Int.mul_le_mul_of_nonneg_left hf
    (Chernoff.pow_nonneg (by omega : (0 : Int) ≤ 2) m)

/-- Natural-number form of the cleared comparison. -/
theorem chernoff_probability_bound_nat {m k f : Nat}
    (hf : (2 : Nat) ^ k * f ≤ 3 ^ m) :
    f * 2 ^ (m + k) ≤ 2 ^ m * 3 ^ m := by
  have h : (2 : Nat) ^ k * f * 2 ^ m ≤ 3 ^ m * 2 ^ m :=
    Nat.mul_le_mul_right (2 ^ m) hf
  rw [Nat.pow_add 2 m k]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/- Numerical sanity check: `tail 3 5 · 2^8 = 16 · 256 = 4096 ≤ 2^5 · 3^5 = 7776`. -/
#eval Chernoff.tail 3 5 * 2 ^ (5 + 3) ≤ 2 ^ 5 * 3 ^ 5

end CausalMohawkBridge.Composition

import CausalMohawkBridge.CausalLattice

/-!
# A self-contained Chernoff tail bound (integer form)

The probabilistic repair in the Sovereign-Mohawk-Proto hierarchical
composition argument rests on an exponential tail bound. This module proves a
discrete, integer-valued instance from scratch (no `Finset`, no `Nat.choose`,
no `ring` — none of which exist in this Mathlib-free toolchain):

* `choose` and a running sum `sumTo` are defined by primitive recursion;
* the binomial identity `∑ᵢ C(m,i) z^i = (1+z)^m` is proved by induction;
* the tail bound `z^k · ∑_{i≥k} C(m,i) ≤ (1+z)^m` follows for `z ≥ 1`.

For `z = 2` this is `2^k · ∑_{i≥k} C(m,i) ≤ 3^m`, i.e. the upper tail of the
binomial distribution decays exponentially in `k`.

Mathlib-free; Lean 4.14.0.
-/

namespace CausalMohawkBridge.Chernoff

/-- Binomial coefficient as an integer. -/
def choose : Nat → Nat → Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Running sum `∑_{i=0}^{n} f i`. -/
def sumTo (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => f 0
  | n + 1 => sumTo n f + f (n + 1)

theorem sumTo_zero (f : Nat → Int) : sumTo 0 f = f 0 := rfl

theorem sumTo_succ (n : Nat) (f : Nat → Int) :
    sumTo (n + 1) f = sumTo n f + f (n + 1) := rfl

theorem sumTo_add (n : Nat) (f g : Nat → Int) :
    sumTo n (fun i => f i + g i) = sumTo n f + sumTo n g := by
  induction n with
  | zero => simp only [sumTo_zero]
  | succ n ih =>
      simp only [sumTo_succ]
      rw [ih]
      omega

theorem sumTo_mul (n : Nat) (c : Int) (f : Nat → Int) :
    sumTo n (fun i => c * f i) = c * sumTo n f := by
  induction n with
  | zero => simp only [sumTo_zero]
  | succ n ih =>
      simp only [sumTo_succ]
      rw [Int.mul_add, ih]

theorem sumTo_congr (n : Nat) {f g : Nat → Int}
    (h : ∀ i, i ≤ n → f i = g i) : sumTo n f = sumTo n g := by
  induction n with
  | zero => simp only [sumTo_zero]; exact h 0 (by omega)
  | succ n ih =>
      simp only [sumTo_succ]
      rw [ih (fun i hi => h i (by omega)), h (n + 1) (by omega)]

theorem sumTo_le (n : Nat) {f g : Nat → Int}
    (h : ∀ i, i ≤ n → f i ≤ g i) : sumTo n f ≤ sumTo n g := by
  induction n with
  | zero => simp only [sumTo_zero]; exact h 0 (by omega)
  | succ n ih =>
      simp only [sumTo_succ]
      have h1 := ih (fun i hi => h i (by omega))
      have h2 := h (n + 1) (by omega)
      omega

theorem choose_succ (m i : Nat) :
    choose (m + 1) i = (if i = 0 then (0 : Int) else choose m (i - 1)) + choose m i := by
  cases i with
  | zero => simp [choose]
  | succ k =>
      cases m with
      | zero => simp [choose]
      | succ m => simp [choose]

theorem choose_gt (n k : Nat) (h : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => exact absurd h (Nat.not_lt_zero 0)
      | succ k => simp [choose]
  | succ n ih =>
      cases k with
      | zero => exact absurd h (Nat.not_lt_zero (n + 1))
      | succ k =>
          rw [choose_succ]
          have h1 : choose n k = 0 := ih k (by omega)
          have h2 : choose n (k + 1) = 0 := ih (k + 1) (by omega)
          simp [h1, h2]

theorem choose_diag (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => simp [choose]
  | succ n ih =>
      rw [choose_succ]
      have h0 : choose n (n + 1) = 0 := choose_gt n (n + 1) (by omega)
      simp [ih, h0]

theorem choose_nonneg (n k : Nat) : (0 : Int) ≤ choose n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => simp [choose]
      | succ k => simp [choose]
  | succ n ih =>
      cases k with
      | zero => simp [choose]
      | succ k =>
          rw [choose_succ]
          have hkk : k + 1 - 1 = k := by omega
          rw [hkk]
          have h1 := ih k
          have h2 := ih (k + 1)
          omega

/-- Reindexing: `∑_{i=1}^{m+1} h(i-1) = ∑_{j=0}^{m} h(j)`. -/
theorem sumTo_shift (m : Nat) (h : Nat → Int) :
    sumTo (m + 1) (fun i => if i = 0 then (0 : Int) else h (i - 1)) = sumTo m h := by
  induction m with
  | zero => simp [sumTo]
  | succ m ih =>
      rw [sumTo_succ, sumTo_succ m h, ih]
      congr 1

/-- **Binomial identity.** -/
theorem binomial (m : Nat) (z : Int) :
    sumTo m (fun i => choose m i * z ^ i) = (1 + z) ^ m := by
  induction m with
  | zero => simp [sumTo, choose, Int.pow_zero]
  | succ m ih =>
      have hsplit :
          sumTo (m + 1) (fun i => choose (m + 1) i * z ^ i) =
            sumTo (m + 1) (fun i => (if i = 0 then (0 : Int) else choose m (i - 1)) * z ^ i) +
            sumTo (m + 1) (fun i => choose m i * z ^ i) := by
        rw [← sumTo_add]
        congr 1
        funext i
        rw [← Int.add_mul, choose_succ]
      have hsecond : sumTo (m + 1) (fun i => choose m i * z ^ i) =
          sumTo m (fun i => choose m i * z ^ i) := by
        rw [sumTo_succ]
        have h0 : choose m (m + 1) = 0 := choose_gt m (m + 1) (by omega)
        simp [h0]
      have hfirst : sumTo (m + 1) (fun i => (if i = 0 then (0 : Int) else choose m (i - 1)) * z ^ i) =
          z * sumTo m (fun i => choose m i * z ^ i) := by
        have hA : sumTo (m + 1) (fun i => (if i = 0 then (0 : Int) else choose m (i - 1)) * z ^ i) =
            sumTo (m + 1) (fun i => if i = 0 then (0 : Int) else
              z * (choose m (i - 1) * z ^ (i - 1))) := by
          apply sumTo_congr
          intro i _
          by_cases hi : i = 0
          · simp [hi]
          · have hi' : i - 1 + 1 = i := by
              cases i with
              | zero => omega
              | succ k => simp
            rw [if_neg hi, if_neg hi]
            have hzi : z ^ i = z ^ (i - 1) * z := by
              cases i with
              | zero => omega
              | succ k => simp [Int.pow_succ]
            rw [hzi]
            simp only [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
        rw [hA, ← sumTo_mul, ← sumTo_shift m (fun j => z * (choose m j * z ^ j))]
      rw [hsplit, hfirst, hsecond, ih, Int.pow_succ', Int.add_mul, Int.one_mul]
      omega

/-- The unweighted upper tail `∑_{i=k}^{m} C(m,i)`. -/
def tail (k m : Nat) : Int :=
  sumTo m (fun i => if i < k then (0 : Int) else choose m i)

theorem pow_add (a : Int) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Int.pow_zero, Int.mul_one]
  | succ n ih =>
      rw [Nat.add_succ, Int.pow_succ, Int.pow_succ, ih, ← Int.mul_assoc]

theorem pow_nonneg {z : Int} (hz : 0 ≤ z) (n : Nat) : 0 ≤ z ^ n := by
  induction n with
  | zero => rw [Int.pow_zero]; omega
  | succ n ih => rw [Int.pow_succ']; exact Int.mul_nonneg hz ih

theorem pow_ge_one {z : Int} (hz : 1 ≤ z) (n : Nat) : 1 ≤ z ^ n := by
  induction n with
  | zero => rw [Int.pow_zero]; omega
  | succ n ih =>
      rw [Int.pow_succ']
      have := Int.mul_le_mul hz ih (by omega : (0 : Int) ≤ 1)
        (by omega : (0 : Int) ≤ z)
      simpa using this

theorem pow_le_pow_of_le {z : Int} (hz : 1 ≤ z) {i j : Nat} (hij : i ≤ j) :
    z ^ i ≤ z ^ j := by
  have h1 : z ^ j = z ^ i * z ^ (j - i) := by
    have hje : j = i + (j - i) := by omega
    have h1' : z ^ j = z ^ (i + (j - i)) := by
      congr 1
    rw [h1', pow_add]
  have h2 : 1 ≤ z ^ (j - i) := pow_ge_one hz _
  rw [h1]
  have h := Int.mul_le_mul_of_nonneg_right h2 (pow_nonneg (by omega : (0 : Int) ≤ z) i)
  rw [Int.one_mul, Int.mul_comm (z ^ (j - i)) (z ^ i)] at h
  exact h

/-- **Chernoff tail bound (integer form).** For `z ≥ 1`,
    `z^k · ∑_{i≥k} C(m,i) ≤ (1+z)^m`. -/
theorem tail_bound (m k : Nat) {z : Int} (hz : 1 ≤ z) :
    z ^ k * tail k m ≤ (1 + z) ^ m := by
  have hterm : ∀ i, i ≤ m →
      z ^ k * (if i < k then (0 : Int) else choose m i) ≤ choose m i * z ^ i := by
    intro i hi
    by_cases hik : i < k
    · simp [hik]
      have hc : (0 : Int) ≤ choose m i := choose_nonneg m i
      have hzi : (0 : Int) ≤ z ^ i := pow_nonneg (by omega : (0 : Int) ≤ z) i
      simpa using Int.mul_le_mul_of_nonneg_right hc hzi
    · simp [hik]
      have hc : (0 : Int) ≤ choose m i := choose_nonneg m i
      have hpow : z ^ k ≤ z ^ i := pow_le_pow_of_le hz (by omega)
      rw [Int.mul_comm (z ^ k) (choose m i)]
      exact Int.mul_le_mul_of_nonneg_left hpow hc
  have hmain : z ^ k * tail k m ≤ sumTo m (fun i => choose m i * z ^ i) := by
    unfold tail
    rw [← sumTo_mul]
    exact sumTo_le m hterm
  rw [binomial] at hmain
  exact hmain

/-- **Negative control.** `tail_bound` fails for `z < 1`: at `z = 0`, `k = 0`,
    `m = 5` the left side is the full sum `2^5 = 32` while the right side is
    `1^5 = 1`. -/
theorem tail_bound_z_lt_one :
    ¬ ((0 : Int) ^ 0 * tail 0 5 ≤ (1 + 0 : Int) ^ 5) := by
  decide

/-- `↑(a^n) = (↑a)^n` for `a : Nat`. -/
theorem ofNat_pow (a : Nat) (k : Nat) : (a : Int) ^ k = ↑(a ^ k) := by
  induction k with
  | zero => rw [Int.pow_zero, Nat.pow_zero, Int.ofNat_one]
  | succ k ih =>
      rw [Int.pow_succ, Nat.pow_succ, Int.ofNat_mul, ih]

theorem sumTo_nonneg {n : Nat} {f : Nat → Int}
    (h : ∀ i, i ≤ n → 0 ≤ f i) : 0 ≤ sumTo n f := by
  induction n with
  | zero => simp only [sumTo_zero]; exact h 0 (by omega)
  | succ n ih =>
      simp only [sumTo_succ]
      have h1 := ih (fun i hi => h i (by omega))
      have h2 := h (n + 1) (by omega)
      omega

theorem tail_nonneg (k m : Nat) : (0 : Int) ≤ tail k m := by
  unfold tail
  apply sumTo_nonneg
  intro i _
  by_cases hik : i < k
  · simp [hik]
  · simp [hik]
    exact choose_nonneg m i

/-- The upper tail as a natural number (it is always nonnegative). -/
def tailNat (k m : Nat) : Nat := (tail k m).toNat

theorem tailNat_eq (k m : Nat) (h : (0 : Int) ≤ tail k m) :
    (tailNat k m : Int) = tail k m := Int.toNat_of_nonneg h

/-- Natural-number form of the tail bound. -/
theorem tailNat_bound (m k : Nat) : (2 : Nat) ^ k * tailNat k m ≤ 3 ^ m := by
  have h : (2 : Int) ^ k * (tailNat k m : Int) ≤ (3 : Int) ^ m := by
    rw [tailNat_eq k m (tail_nonneg k m)]
    exact tail_bound m k (by omega)
  have h' : Nat.cast (R := Int) ((2 : Nat) ^ k * tailNat k m) ≤
      Nat.cast (R := Int) ((3 : Nat) ^ m) := by
    rw [Int.ofNat_mul]
    rw [show Nat.cast (R := Int) ((2 : Nat) ^ k) = (2 : Int) ^ k
      from (ofNat_pow 2 k).symm]
    rw [show Nat.cast (R := Int) ((3 : Nat) ^ m) = (3 : Int) ^ m
      from (ofNat_pow 3 m).symm]
    exact h
  exact Int.ofNat_le.mp h'

/-- The tail is bounded by `3^m` (the cleared `2^k · tail ≤ 3^m` with `2^k ≥ 1`). -/
theorem tailNat_le (m k : Nat) : tailNat k m ≤ 3 ^ m := by
  have hb : (2 : Nat) ^ k * tailNat k m ≤ 3 ^ m := tailNat_bound m k
  have h1 : tailNat k m ≤ (2 : Nat) ^ k * tailNat k m :=
    Nat.le_mul_of_pos_left (n := (2 : Nat) ^ k) (tailNat k m)
      (Nat.pow_pos (a := 2) (n := k) (by omega))
  exact Nat.le_trans h1 hb

/-- Cleared-denominator form of the Nat tail bound:
    `tail · 2^(m+k) ≤ 2^m · 3^m`. -/
theorem tailNat_cleared (m k : Nat) : tailNat k m * 2 ^ (m + k) ≤ 2 ^ m * 3 ^ m := by
  have hb : (2 : Nat) ^ k * tailNat k m ≤ 3 ^ m := tailNat_bound m k
  have h : (2 : Nat) ^ m * ((2 : Nat) ^ k * tailNat k m) ≤ (2 : Nat) ^ m * 3 ^ m :=
    Nat.mul_le_mul_left ((2 : Nat) ^ m) hb
  rw [← Nat.mul_assoc, ← Nat.pow_add 2 m k] at h
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/- Numerical sanity checks (evaluated at elaboration time). -/
#eval Chernoff.tail 3 5
#eval ((2 : Int) ^ 3 * Chernoff.tail 3 5 ≤ 3 ^ 5)

end CausalMohawkBridge.Chernoff

import CausalMohawkBridge.CausalLattice

/-!
# Theorem 5.2 core: affine Lorentz words on refining sublattices

A 1+1 dimensional, integer-coefficient formalisation of the "common domains
for finite affine words" result. An affine Lorentz map
`(t,j) ↦ (a t + b j + c_t, b t + a j + c_j)` with `a² - b² = 1` preserves the
Minkowski quadratic interval `Q(t,j) = t² - j²` exactly on differences; its
inverse is again of the same form; and every word over a finite family has a
common refining sublattice domain `H N = N·ℤ²` on which it and its inverse are
defined, with `Q` preserved exactly at each step.

Over `Int`, `a² - b² = 1` forces `(a,b) = (±1, 0)` (`sq_sub_eq_one`), so the
integer affine Lorentz group is degenerate; the non-trivial content lives in
`ScaledLorentz` (`A² - B² = N²`), which represents rational maps.

The analytic "uniform approximation on compact sets" clause of Theorem 5.2 is
not formalised (it needs a normed/compactness infrastructure this project does
not carry); the domain clause (`commonRefinement_exists`,
`commonRefinement_fine`, `commonRefinement_of_dvd_cd`) and the
exact-preservation clause (`Q_scaled`, `Q_word`) are. The domain clause is
strengthened from the trivial witness `M = 1`: for a linear word, every target
resolution `M₀ > 0` admits the common refining domain `M₀ · ∏_{L∈w} L.N`
(`commonRefinement_fine`), and in fact every positive modulus works
(`commonRefinement_linear_arbitrary`). For an affine word the translation part
is the only obstruction: any `M` dividing every `L.C` and `L.D` works
(`commonRefinement_of_dvd_cd`).

Mathlib-free; Lean 4.14.0.
-/

namespace CausalMohawkBridge.Lorentz

/-- `a² = a*a`, since core has no generic `pow_two`. -/
private theorem sq (a : Int) : a^2 = a*a := by
  have h : (2:Nat) = 1+1 := rfl
  rw [h, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- Over the integers, `d ∣ 1` forces `d = ±1`. -/
private theorem dvd_one_eq {d : Int} (h : d ∣ 1) : d = 1 ∨ d = -1 := by
  obtain ⟨c, hc⟩ := h
  rcases Int.lt_trichotomy d 0 with hd | hd | hd
  · have hd1 : -d ∣ 1 := ⟨-c, by rw [Int.neg_mul_neg]; exact hc⟩
    have hle : -d ≤ 1 := Int.le_of_dvd (by omega : (0 : Int) < 1) hd1
    right; omega
  · exfalso
    have h0 : (1 : Int) = 0 := by rw [hc, hd, Int.zero_mul]
    omega
  · have hle : d ≤ 1 := Int.le_of_dvd (by omega : (0 : Int) < 1) ⟨c, hc⟩
    left; omega

/-- Over the integers, `a² - b² = 1` forces `(a, b) = (±1, 0)`: the integer
    affine Lorentz group is degenerate, and the non-trivial content lives in
    `ScaledLorentz` (`A² - B² = N²`), which represents rational maps. -/
theorem sq_sub_eq_one {a b : Int} (h : a^2 - b^2 = 1) :
    b = 0 ∧ (a = 1 ∨ a = -1) := by
  have hfac : (a - b) * (a + b) = a^2 - b^2 := by
    simp only [sq, Int.mul_sub, Int.sub_mul, Int.add_mul, Int.mul_add,
      Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
    omega
  have hfac' : (a - b) * (a + b) = 1 := by rw [hfac, h]
  have hb1 : a - b = 1 ∨ a - b = -1 := dvd_one_eq ⟨a + b, hfac'.symm⟩
  have hb2 : a + b = 1 ∨ a + b = -1 :=
    dvd_one_eq ⟨a - b, by rw [Int.mul_comm]; exact hfac'.symm⟩
  rcases hb1 with h1 | h1 <;> rcases hb2 with h2 | h2
  · exact ⟨by omega, Or.inl (by omega)⟩
  · exfalso; rw [h1, h2] at hfac'; omega
  · exfalso; rw [h1, h2] at hfac'; omega
  · exact ⟨by omega, Or.inr (by omega)⟩

/-- The interval-preservation identity `(a x + b y)² - (b x + a y)² =
    (a² - b²)(x² - y²)`. -/
theorem lorentz_interval_aux (a b x y : Int) :
    (a*x + b*y)^2 - (b*x + a*y)^2 = (a^2 - b^2)*(x^2 - y^2) := by
  simp only [sq, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
    Int.sub_eq_add_neg, Int.neg_add, Int.neg_mul, Int.mul_neg, Int.neg_neg,
    Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  omega

theorem lorentz_interval {a b x y : Int} (h : a^2 - b^2 = 1) :
    (a*x + b*y)^2 - (b*x + a*y)^2 = x^2 - y^2 := by
  rw [lorentz_interval_aux, h, Int.one_mul]

/-- Componentwise subtraction of lattice points. -/
def psub (p q : Int × Int) : Int × Int := (p.1 - q.1, p.2 - q.2)

/-- Minkowski quadratic form `Q(t,j) = t² - j²`. -/
def Q (p : Int × Int) : Int := p.1^2 - p.2^2

/-- Affine Lorentz transformation in 1+1 dimensions. -/
structure ALorentz where
  a : Int
  b : Int
  ct : Int
  cj : Int
  h : a^2 - b^2 = 1

def ALorentz.apply (L : ALorentz) (p : Int × Int) : Int × Int :=
  (L.a * p.1 + L.b * p.2 + L.ct, L.b * p.1 + L.a * p.2 + L.cj)

/-- Exact preservation of the Minkowski interval on differences. -/
theorem Q_apply_sub (L : ALorentz) (p q : Int × Int) :
    Q (psub (L.apply p) (L.apply q)) = Q (psub p q) := by
  cases p with
  | mk p1 p2 =>
    cases q with
    | mk q1 q2 =>
      simp only [Q, ALorentz.apply, psub]
      rw [show L.a*p1 + L.b*p2 + L.ct - (L.a*q1 + L.b*q2 + L.ct)
            = (L.a*p1 - L.a*q1) + (L.b*p2 - L.b*q2) from by omega]
      rw [show L.b*p1 + L.a*p2 + L.cj - (L.b*q1 + L.a*q2 + L.cj)
            = (L.b*p1 - L.b*q1) + (L.a*p2 - L.a*q2) from by omega]
      rw [← Int.mul_sub, ← Int.mul_sub, ← Int.mul_sub, ← Int.mul_sub]
      exact lorentz_interval L.h

/-- The inverse affine Lorentz map. -/
def ALorentz.inv (L : ALorentz) : ALorentz where
  a := L.a
  b := -L.b
  ct := L.b * L.cj - L.a * L.ct
  cj := L.b * L.ct - L.a * L.cj
  h := by
    have hb : (-L.b)^2 = L.b^2 := by
      simp only [sq, Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [hb, L.h]

/-- The inverse is a right inverse: `L⁻¹(L p) = p`. -/
theorem inv_apply (L : ALorentz) (p : Int × Int) :
    L.inv.apply (L.apply p) = p := by
  cases p with
  | mk p1 p2 =>
    simp only [ALorentz.apply, ALorentz.inv]
    have h1 : L.a*(L.a*p1 + L.b*p2 + L.ct) + (-L.b)*(L.b*p1 + L.a*p2 + L.cj)
        + (L.b*L.cj - L.a*L.ct) = p1 * (L.a*L.a - L.b*L.b) := by
      simp only [sq, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
        Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_comm, Int.mul_left_comm,
        Int.mul_assoc]
      omega
    have h2 : (-L.b)*(L.a*p1 + L.b*p2 + L.ct) + L.a*(L.b*p1 + L.a*p2 + L.cj)
        + (L.b*L.ct - L.a*L.cj) = p2 * (L.a*L.a - L.b*L.b) := by
      simp only [sq, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
        Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_comm, Int.mul_left_comm,
        Int.mul_assoc]
      omega
    rw [h1, h2, ← sq L.a, ← sq L.b, L.h]
    simp

/-- Composition of affine Lorentz maps (apply `L₂` first, then `L₁`). -/
def ALorentz.comp (L₁ L₂ : ALorentz) : ALorentz where
  a := L₁.a * L₂.a + L₁.b * L₂.b
  b := L₁.a * L₂.b + L₁.b * L₂.a
  ct := L₁.a * L₂.ct + L₁.b * L₂.cj + L₁.ct
  cj := L₁.b * L₂.ct + L₁.a * L₂.cj + L₁.cj
  h := by
    have hB : L₁.a * L₂.b + L₁.b * L₂.a = L₁.b * L₂.a + L₁.a * L₂.b := by omega
    rw [hB, lorentz_interval_aux, L₁.h, L₂.h, Int.one_mul]

theorem apply_comp (L₁ L₂ : ALorentz) (p : Int × Int) :
    (L₁.comp L₂).apply p = L₁.apply (L₂.apply p) := by
  cases p with
  | mk p1 p2 =>
    simp only [ALorentz.comp, ALorentz.apply]
    apply Prod.ext
    · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
        Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_comm, Int.mul_left_comm,
        Int.mul_assoc]
      omega
    · simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
        Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_comm, Int.mul_left_comm,
        Int.mul_assoc]
      omega

/-! ## Words and their common domain -/

/-- A bounded word: a finite list of affine Lorentz maps. -/
abbrev Word := List ALorentz

def wordApply (w : Word) (p : Int × Int) : Int × Int :=
  match w with
  | [] => p
  | L :: rest => L.apply (wordApply rest p)

/-- Every word preserves the Minkowski interval exactly. -/
theorem Q_word (w : Word) (p q : Int × Int) :
    Q (psub (wordApply w p) (wordApply w q)) = Q (psub p q) := by
  induction w with
  | nil => simp only [wordApply, psub]
  | cons L rest ih =>
      change Q (psub (L.apply (wordApply rest p)) (L.apply (wordApply rest q))) = Q (psub p q)
      rw [Q_apply_sub L, ih]

/-- The refining sublattice `H N = N · ℤ²`. -/
def H (N : Int) (p : Int × Int) : Prop := p.1 % N = 0 ∧ p.2 % N = 0

private theorem dvd_mul_of_dvd_left {N x y : Int} (hx : N ∣ x) : N ∣ x * y :=
  Int.dvd_trans hx (Int.dvd_mul_right x y)

private theorem dvd_mul_of_dvd_right {N x : Int} (hx : N ∣ x) (y : Int) : N ∣ y * x :=
  Int.dvd_trans hx (Int.dvd_mul_left y x)

/-- An affine Lorentz map with all data divisible by `N` preserves `H N`. -/
theorem H_apply {N : Int} {L : ALorentz} {p : Int × Int}
    (ha : L.a % N = 0) (hb : L.b % N = 0) (hct : L.ct % N = 0) (hcj : L.cj % N = 0) :
    H N (L.apply p) := by
  unfold H
  unfold ALorentz.apply
  simp only
  constructor
  · rw [← Int.dvd_iff_emod_eq_zero]
    exact Int.dvd_add
      (Int.dvd_add
        (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr ha))
        (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr hb)))
      (Int.dvd_iff_emod_eq_zero.mpr hct)
  · rw [← Int.dvd_iff_emod_eq_zero]
    exact Int.dvd_add
      (Int.dvd_add
        (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr hb))
        (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr ha)))
      (Int.dvd_iff_emod_eq_zero.mpr hcj)

/-- Every word whose maps have data divisible by `N` preserves `H N`. -/
theorem H_word {N : Int} {w : Word}
    (hc : ∀ L ∈ w, L.a % N = 0 ∧ L.b % N = 0 ∧ L.ct % N = 0 ∧ L.cj % N = 0)
    {p : Int × Int} (hp : H N p) : H N (wordApply w p) := by
  induction w with
  | nil => simpa [wordApply] using hp
  | cons L rest ih =>
      change H N (L.apply (wordApply rest p))
      have hL := hc L (by simp)
      exact H_apply hL.1 hL.2.1 hL.2.2.1 hL.2.2.2

/-! ## Rational data: exact interval preservation after clearing denominators -/

/-- A rational affine Lorentz map `(A/N, B/N, C/N, D/N)` with `A² - B² = N²`,
    represented by its integer numerator data acting on the refined lattice. -/
structure ScaledLorentz where
  A : Int
  B : Int
  C : Int
  D : Int
  N : Int
  hN : 0 < N
  h : A^2 - B^2 = N^2

def ScaledLorentz.apply (L : ScaledLorentz) (p : Int × Int) : Int × Int :=
  (L.A * p.1 + L.B * p.2 + L.C, L.B * p.1 + L.A * p.2 + L.D)

/-- The scaled map multiplies the Minkowski interval by `N²`; equivalently the
    rational map preserves it exactly on the refined lattice. -/
theorem Q_scaled (L : ScaledLorentz) (p q : Int × Int) :
    Q (psub (L.apply p) (L.apply q)) = L.N^2 * Q (psub p q) := by
  cases p with
  | mk p1 p2 =>
    cases q with
    | mk q1 q2 =>
      simp only [Q, ScaledLorentz.apply, psub]
      rw [show L.A*p1 + L.B*p2 + L.C - (L.A*q1 + L.B*q2 + L.C)
            = (L.A*p1 - L.A*q1) + (L.B*p2 - L.B*q2) from by omega]
      rw [show L.B*p1 + L.A*p2 + L.D - (L.B*q1 + L.A*q2 + L.D)
            = (L.B*p1 - L.B*q1) + (L.A*p2 - L.A*q2) from by omega]
      rw [← Int.mul_sub, ← Int.mul_sub, ← Int.mul_sub, ← Int.mul_sub]
      rw [lorentz_interval_aux, L.h]

/-- A scaled Lorentz map whose data are divisible by `N` preserves `H N`. -/
theorem H_apply_scaled {N : Int} {L : ScaledLorentz} {p : Int × Int}
    (ha : L.A % N = 0) (hb : L.B % N = 0) (hct : L.C % N = 0) (hcj : L.D % N = 0) :
    H N (L.apply p) := by
  unfold H
  unfold ScaledLorentz.apply
  simp only
  constructor
  · rw [← Int.dvd_iff_emod_eq_zero]
    exact Int.dvd_add
      (Int.dvd_add
        (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr ha))
        (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr hb)))
      (Int.dvd_iff_emod_eq_zero.mpr hct)
  · rw [← Int.dvd_iff_emod_eq_zero]
    exact Int.dvd_add
      (Int.dvd_add
        (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr hb))
        (dvd_mul_of_dvd_left (Int.dvd_iff_emod_eq_zero.mpr ha)))
      (Int.dvd_iff_emod_eq_zero.mpr hcj)

/-! ## Common refining domains (Theorem 5.2, discrete form) -/

/-- A common refining domain for a finite word of rational affine Lorentz maps:
    a positive modulus `M` such that every map in the word preserves the
    sublattice `H M` and scales the Minkowski form by the square of its
    denominator. -/
def CommonRefinement (w : List ScaledLorentz) (M : Int) : Prop :=
  0 < M ∧ ∀ L ∈ w,
    (∀ p, H M p → H M (L.apply p)) ∧
    (∀ p q, Q (psub (L.apply p) (L.apply q)) = L.N^2 * Q (psub p q))

/-- **Theorem 5.2 (existence of a common refining domain).** Every finite
    word of rational affine Lorentz maps has a common refining domain; the
    coarsest witness is `M = 1`. -/
theorem commonRefinement_exists (w : List ScaledLorentz) :
    ∃ M : Int, CommonRefinement w M := by
  refine ⟨1, by omega, fun L _ => ⟨?_, ?_⟩⟩
  · intro p _
    exact H_apply_scaled (Int.emod_one L.A) (Int.emod_one L.B)
      (Int.emod_one L.C) (Int.emod_one L.D)
  · intro p q
    exact Q_scaled L p q

/-- Any common divisor of the word's data is a common refining domain. -/
theorem commonRefinement_of_dvd (w : List ScaledLorentz) {M : Int} (hM : 0 < M)
    (h : ∀ L ∈ w, M ∣ L.A ∧ M ∣ L.B ∧ M ∣ L.C ∧ M ∣ L.D) :
    CommonRefinement w M := by
  refine ⟨hM, fun L hL => ⟨?_, ?_⟩⟩
  · intro p _
    have hL := h L hL
    exact H_apply_scaled (Int.dvd_iff_emod_eq_zero.mp hL.1)
      (Int.dvd_iff_emod_eq_zero.mp hL.2.1)
      (Int.dvd_iff_emod_eq_zero.mp hL.2.2.1)
      (Int.dvd_iff_emod_eq_zero.mp hL.2.2.2)
  · intro p q
    exact Q_scaled L p q

/-- An affine map preserves `H M` as soon as `M` divides its translation part;
    the linear part preserves every `H M`. -/
theorem H_apply_of_dvd_cd {M : Int} {L : ScaledLorentz}
    (hct : M ∣ L.C) (hcj : M ∣ L.D) {p : Int × Int} (hp : H M p) :
    H M (L.apply p) := by
  unfold H at hp ⊢
  unfold ScaledLorentz.apply
  obtain ⟨hp1, hp2⟩ := hp
  have hA1 : M ∣ L.A * p.1 := dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr hp1) L.A
  have hB2 : M ∣ L.B * p.2 := dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr hp2) L.B
  have hB1 : M ∣ L.B * p.1 := dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr hp1) L.B
  have hA2 : M ∣ L.A * p.2 := dvd_mul_of_dvd_right (Int.dvd_iff_emod_eq_zero.mpr hp2) L.A
  constructor
  · rw [← Int.dvd_iff_emod_eq_zero]
    exact Int.dvd_add (Int.dvd_add hA1 hB2) hct
  · rw [← Int.dvd_iff_emod_eq_zero]
    exact Int.dvd_add (Int.dvd_add hB1 hA2) hcj

/-- **Characterisation.** An affine scaled map preserves `H M` if and only if
    `M` divides its translation part; the linear part is no obstruction. -/
theorem hMap_iff_dvd_cd {M : Int} {L : ScaledLorentz} :
    (∀ p, H M p → H M (L.apply p)) ↔ M ∣ L.C ∧ M ∣ L.D := by
  constructor
  · intro h
    have h0 : H M (L.apply (0, 0)) := h (0, 0) (by unfold H; simp)
    have heq : L.apply (0, 0) = (L.C, L.D) := by
      unfold ScaledLorentz.apply; simp
    rw [heq] at h0
    unfold H at h0
    exact ⟨Int.dvd_iff_emod_eq_zero.mpr h0.1, Int.dvd_iff_emod_eq_zero.mpr h0.2⟩
  · intro h p hp
    exact H_apply_of_dvd_cd h.1 h.2 hp

/-- Any modulus dividing every translation part is a common refining domain. -/
theorem commonRefinement_of_dvd_cd {w : List ScaledLorentz} {M : Int} (hM : 0 < M)
    (h : ∀ L ∈ w, M ∣ L.C ∧ M ∣ L.D) : CommonRefinement w M := by
  refine ⟨hM, fun L hL => ⟨?_, ?_⟩⟩
  · intro p hp
    exact H_apply_of_dvd_cd (h L hL).1 (h L hL).2 hp
  · intro p q
    exact Q_scaled L p q

/-- The product of the denominators of a word. -/
def denProd : List ScaledLorentz → Int
  | [] => 1
  | L :: rest => L.N * denProd rest

theorem denProd_pos (w : List ScaledLorentz) : 0 < denProd w := by
  induction w with
  | nil => simp [denProd]
  | cons L rest ih => simp only [denProd]; exact Int.mul_pos L.hN ih

/-- **Theorem 5.2, strengthened.** For a *linear* word (zero translation part),
    every target resolution can be refined: for any `M₀ > 0`,
    `M₀ · ∏_{L∈w} L.N` is a common refining domain. Hence arbitrarily fine
    common sublattices exist. The product is a canonical choice, not the
    maximal refinement — `commonRefinement_linear_arbitrary` shows every
    positive modulus works, so the finest common domain is unbounded. -/
theorem commonRefinement_fine {w : List ScaledLorentz}
    (hlin : ∀ L ∈ w, L.C = 0 ∧ L.D = 0)
    {M₀ : Int} (hM₀ : 0 < M₀) :
    CommonRefinement w (M₀ * denProd w) := by
  have hdp := denProd_pos w
  refine ⟨Int.mul_pos hM₀ hdp, fun L hL => ⟨?_, ?_⟩⟩
  · intro p hp
    refine H_apply_of_dvd_cd ?_ ?_ hp
    · rw [(hlin L hL).1]; exact Int.dvd_zero _
    · rw [(hlin L hL).2]; exact Int.dvd_zero _
  · intro p q
    exact Q_scaled L p q

/-- For a linear word, *every* positive modulus is a common refining domain. -/
theorem commonRefinement_linear_arbitrary {w : List ScaledLorentz}
    (hlin : ∀ L ∈ w, L.C = 0 ∧ L.D = 0)
    {M : Int} (hM : 0 < M) : CommonRefinement w M := by
  refine ⟨hM, fun L hL => ⟨?_, ?_⟩⟩
  · intro p hp
    refine H_apply_of_dvd_cd ?_ ?_ hp
    · rw [(hlin L hL).1]; exact Int.dvd_zero _
    · rw [(hlin L hL).2]; exact Int.dvd_zero _
  · intro p q
    exact Q_scaled L p q

end CausalMohawkBridge.Lorentz

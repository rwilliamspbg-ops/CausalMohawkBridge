namespace CausalMohawkBridge.CausalLattice

/-- Lifted event on the lattice. -/
structure Event where
  t : Int
  j : Int
  deriving DecidableEq, Repr

/-- Null coordinates without division (u = t + j, v = t - j). -/
def u (e : Event) : Int := e.t + e.j
def v (e : Event) : Int := e.t - e.j

/-- Parity sector: t + j even (null coordinates are integral halves). -/
def OnParity (e : Event) : Prop := (u e) % 2 = 0

def stepPlus  (e : Event) : Event := ⟨e.t + 1, e.j + 1⟩
def stepMinus (e : Event) : Event := ⟨e.t + 1, e.j - 1⟩

theorem commuting_diamond (e : Event) :
    stepPlus (stepMinus e) = stepMinus (stepPlus e) := by
  cases e with
  | mk t j =>
    simp only [stepPlus, stepMinus, Event.mk.injEq]
    first | exact ⟨trivial, by omega⟩ | exact ⟨rfl, by omega⟩ | omega

theorem stepPlus_parity (e : Event) : OnParity e → OnParity (stepPlus e) := by
  simp only [OnParity, u, stepPlus]; omega

theorem stepMinus_parity (e : Event) : OnParity e → OnParity (stepMinus e) := by
  simp only [OnParity, u, stepMinus]; omega

/-- One generator step. -/
inductive Step : Event → Event → Prop
  | plus  (e : Event) : Step e (stepPlus e)
  | minus (e : Event) : Step e (stepMinus e)

/-- Reflexive-transitive closure (causal reachability by generator paths). -/
inductive Reach : Event → Event → Prop
  | refl (e : Event) : Reach e e
  | tail {a b c : Event} : Reach a b → Step b c → Reach a c

theorem Reach.trans {a b c : Event} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ s ih => exact Reach.tail ih s

/-- Null-coordinate (non-negative increment) reachability. -/
def NullReachable (e₁ e₂ : Event) : Prop :=
  ∃ a b : Nat, e₂.t = e₁.t + a + b ∧ e₂.j = e₁.j + a - b

theorem reach_to_null {e₁ e₂ : Event} (h : Reach e₁ e₂) : NullReachable e₁ e₂ := by
  induction h with
  | refl => exact ⟨0, 0, by simp, by simp⟩
  | tail _ s ih =>
    obtain ⟨a, b, ht, hj⟩ := ih
    cases s with
    | plus => exact ⟨a + 1, b, by simp [stepPlus]; omega, by simp [stepPlus]; omega⟩
    | minus => exact ⟨a, b + 1, by simp [stepMinus]; omega, by simp [stepMinus]; omega⟩

theorem reach_plus_iter (e : Event) (a : Nat) :
    Reach e ⟨e.t + a, e.j + a⟩ := by
  induction a with
  | zero => simpa using Reach.refl e
  | succ n ih =>
    have := Reach.tail ih (Step.plus ⟨e.t + n, e.j + n⟩)
    simpa [stepPlus, Int.add_assoc] using this

theorem reach_minus_iter (e : Event) (b : Nat) :
    Reach e ⟨e.t + b, e.j - b⟩ := by
  induction b with
  | zero => simpa using Reach.refl e
  | succ n ih =>
    have := Reach.tail ih (Step.minus ⟨e.t + n, e.j - n⟩)
    simp only [stepMinus] at this
    have h : (⟨e.t + ↑n + 1, e.j - ↑n - 1⟩ : Event) = ⟨e.t + ↑(n+1), e.j - ↑(n+1)⟩ := by
      simp only [Event.mk.injEq]; omega
    rw [h] at this; exact this

/-- Converse: any null-coordinate-ordered pair is joined by a generator path. -/
theorem null_to_reach {e₁ e₂ : Event} (h : NullReachable e₁ e₂) : Reach e₁ e₂ := by
  obtain ⟨a, b, ht, hj⟩ := h
  have h1 := reach_plus_iter e₁ a
  have h2 := reach_minus_iter ⟨e₁.t + a, e₁.j + a⟩ b
  have h3 := h1.trans h2
  have : e₂ = ⟨e₁.t + a + b, e₁.j + a - b⟩ := by
    cases e₂; simp only [Event.mk.injEq] at *; omega
  rw [this]; exact h3

/-- Theorem 3.1-style reachability: generator paths = null-coordinate order. -/
theorem reach_iff_null (e₁ e₂ : Event) : Reach e₁ e₂ ↔ NullReachable e₁ e₂ :=
  ⟨reach_to_null, null_to_reach⟩

theorem Reach.parity {e₁ e₂ : Event} (h : Reach e₁ e₂) : OnParity e₁ → OnParity e₂ := by
  induction h with
  | refl => exact id
  | tail _ s ih =>
    intro p
    cases s with
    | plus => exact stepPlus_parity _ (ih p)
    | minus => exact stepMinus_parity _ (ih p)

end CausalMohawkBridge.CausalLattice

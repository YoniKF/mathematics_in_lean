import data.real.basic

section
variables {x y : ℝ}

example (h : y > x^2) : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }

example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h

example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    intro h, left, exact h },
  rw abs_of_neg h,
  intro h, right, exact h
end

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ abs x :=
begin
  cases le_or_gt 0 x,
  { rw abs_of_nonneg h },
  rw abs_of_neg h,
  linarith
end

theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x :=
begin
  cases le_or_gt 0 x,
  { rw abs_of_nonneg h,
    linarith },
  rw abs_of_neg h
end

theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=
begin
  cases le_or_gt 0 (x + y),
  { rw abs_of_nonneg h,
    exact add_le_add (le_abs_self x) (le_abs_self y) },
  rw abs_of_neg h,
  rw neg_add,
  exact add_le_add (neg_le_abs_self x) (neg_le_abs_self y)
end

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with,
  { rw abs_of_nonneg h,
    split,
    { exact or.inl },
    intro h',
    cases h'; linarith },
  rw abs_of_neg h,
  split,
  { exact or.inr },
  intro h',
  cases h'; linarith
end

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
begin
  cases le_or_gt 0 x,
  { rw abs_of_nonneg h,
    split,
    { intro h',
      split; linarith},
    exact and.right },
  rw abs_of_neg h,
  split,
  { intro h',
    split; linarith },
  rintro h', linarith
end

end my_abs
end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, exact xgt
end

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right
end

example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
by { rcases h with ⟨x, y, rfl | rfl⟩; linarith [sq_nonneg x, sq_nonneg y] }

example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  have h' : (x - 1) * (x + 1) = 0, by linarith,
  cases eq_zero_or_eq_zero_of_mul_eq_zero h',
  { left, linarith },
  right, linarith
end

example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
begin
  have h'  : x^2 - y^2 = 0, by { rw h, apply sub_self },
  have h'' : (x - y) * (x + y) = 0, by { rw ← h', ring },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h''' h''',
  { left, apply eq_of_sub_eq_zero h'''},
  right, apply eq_neg_of_add_eq_zero_left h''',
end

section
variables {R : Type*} [comm_ring R] [is_domain R]
variables (x y : R)

example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  have h₀ : x^2 - 1 = 0, by { rw h, apply sub_self },
  have h₁ : (x - 1) * (x + 1) = 0, by { rw ← h₀, ring },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h₁ with h₂ h₂,
  { left, apply eq_of_sub_eq_zero h₂},
  right, apply eq_neg_of_add_eq_zero_left h₂,
end

example (h : x^2 = y^2) : x = y ∨ x = -y :=
begin
  have h₀ : x^2 - y^2 = 0, by { rw h, apply sub_self },
  have h₁ : (x - y) * (x + y) = 0, by { rw ← h₀, ring },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h₁ with h₂ h₂,
  { left, apply eq_of_sub_eq_zero h₂},
  right, apply eq_neg_of_add_eq_zero_left h₂,
end

end

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end

section
open_locale classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction
end

example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
begin
  split,
  { intro h,
    by_cases hp : P,
    { right, exact h hp },
    left, exact hp },
  rintros (hnp | hq ) _,
  { contradiction },
  exact hq
end

end

import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    apply add_le_add
    repeat apply le_abs_self
  · rw [abs_of_neg h]
    rw [neg_add]
    apply add_le_add
    repeat apply neg_le_abs_self

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    constructor
    · exact Or.inl
    · intro h
      rcases h with h | h
      repeat linarith
  · rw [abs_of_neg hy]
    constructor
    · exact Or.inr
    · intro h
      rcases h with h | h
      repeat linarith

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    constructor
    · intro
      constructor
      · linarith
      · assumption
    · exact And.right
  · rw [abs_of_neg hx]
    constructor
    · intro
      constructor <;> linarith
    · intro
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  · left
    linarith
  · right
    linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  · left
    linarith
  · right
    linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := calc
    _ = x^2 - 1 := by ring
    _ = 0 := sub_eq_zero_of_eq h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  · left
    exact eq_of_sub_eq_zero h'
  · right
    apply eq_of_sub_eq_zero
    rw [sub_neg_eq_add]
    assumption

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := calc
    _ = x^2 - y^2 := by ring
    _ = 0 := by rw [h, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  · left
    exact eq_of_sub_eq_zero h'
  · right
    apply eq_of_sub_eq_zero
    rw [sub_neg_eq_add]
    assumption

end

section
variable {R : Type*} [Ring R] [IsDomain R]
variable (x : R)

-- Same as the first example in the previous section above but without commutativity
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by
    rw [sub_mul, mul_add, one_mul, mul_one, ←pow_two,
        add_sub_assoc, sub_add_cancel_left, ←sub_eq_add_neg]
    exact sub_eq_zero_of_eq h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  · left
    exact eq_of_sub_eq_zero h'
  · right
    apply eq_of_sub_eq_zero
    rw [sub_neg_eq_add]
    assumption

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left
      assumption
  · intro h
    rcases h with h' | h'
    · intro h''
      contradiction
    · intro h''
      assumption

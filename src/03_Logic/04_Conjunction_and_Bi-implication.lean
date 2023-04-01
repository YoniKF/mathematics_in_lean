import data.real.basic
import data.nat.prime

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { assumption },
  intro h,
  apply h₁,
  rw h
end

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
⟨h₀, λ h, h₁ (by rw h)⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  have h : x ≠ y,
  { contrapose! h₁,
    rw h₁ },
  exact ⟨h₀, h⟩
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  cases h with h₀ h₁,
  contrapose! h₁,
  exact le_antisymm h₀ h₁
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩ h',
  exact h₁ (le_antisymm h₀ h')
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
λ ⟨h₀, h₁⟩ h', h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h',
  apply h.right,
  exact le_antisymm h.left h'
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
begin
  cases h with h₀ h₁,
  split,
  { assumption },
  contrapose! h₁,
  apply nat.dvd_antisymm,
  repeat { assumption }
end

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬ n ∣ m := ⟨h.left, λ h', h.right (nat.dvd_antisymm h.left h')⟩

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
⟨5/2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
begin
  rintros ⟨z, xltz, zlty⟩,
  exact lt_trans xltz zlty
end

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
λ ⟨z, xltz, zlty⟩, lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
begin
  use 5 / 2,
  split; norm_num
end

example : ∃ m n : ℕ,
  4 < m ∧ m < n ∧ n < 10 ∧ nat.prime m ∧ nat.prime n :=
begin
  use [5, 7],
  norm_num
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩,
  use [h₀, λ h', h₁ (le_antisymm h₀ h')]
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin
  split,
  { contrapose!,
    rintro rfl,
    reflexivity },
  contrapose!,
  exact le_antisymm h
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
⟨λ h₀ h₁, h₀ (by rw h₁), λ h₀ h₁, h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
begin
  split,
  { rintro ⟨h, h'⟩,
    split,
    { assumption },
    contrapose! h',
    rw h' },
  rintro ⟨h, h'⟩,
  split,
  { assumption },
  contrapose! h',
  exact le_antisymm h h'
end

theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { have hx : 0 ≤ x^2 := pow_two_nonneg _,
    have hy : 0 ≤ y^2 := pow_two_nonneg _,
    linarith },
  exact pow_eq_zero h'
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
begin
  split,
  { intro h,
    split,
    { exact aux h },
    rw add_comm at h,
    exact aux h },
  { rintro ⟨rfl, rfl⟩,
    ring }
end

section

example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith
end

example : 3 ∣ nat.gcd 6 15 :=
begin
  rw nat.dvd_gcd_iff,
  split; norm_num
end

end

theorem not_monotone_iff {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw monotone, push_neg }

example : ¬ monotone (λ x : ℝ, -x) :=
begin
  rw not_monotone_iff,
  use [0, 1],
  norm_num
end

section
variables {α : Type*} [partial_order α]
variables a b : α

example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
  { rintro ⟨h, h'⟩,
    split,
    assumption,
    contrapose! h',
    rw h' },
  rintro ⟨h, h'⟩,
  split,
  assumption,
  contrapose! h',
  exact le_antisymm h h'
end

end

section
variables {α : Type*} [preorder α]
variables a b c : α

example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  rintro ⟨h, h'⟩,
  apply h',
  exact h
end

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  rintro ⟨h₀, h₁⟩ ⟨h₂, _⟩,
  split,
  exact le_trans h₀ h₂,
  contrapose! h₁,
  exact le_trans h₂ h₁
end

end

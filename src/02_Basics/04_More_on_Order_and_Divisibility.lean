import data.real.basic

section
variables a b c d : ℝ

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

example : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    { apply min_le_right },
    apply min_le_left },
  { show min b a ≤ min a b,
    apply le_min,
    { apply min_le_right },
    apply min_le_left }
end

example : min a b = min b a :=
begin
  have h : ∀ x y, min x y ≤ min y x,
  { intros x y,
    apply le_min,
    apply min_le_right,
    apply min_le_left },
  apply le_antisymm, apply h, apply h
end

example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left }
end

example : max a b = max b a :=
begin
  have h : ∀ x y : ℝ, max x y ≤ max y x,
  {
    intros x y,
    apply max_le,
    apply le_max_right,
    apply le_max_left
  },
  apply le_antisymm,
  repeat { apply h }
end

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm,
  { show min (min a b) c ≤ min a (min b c),
    apply le_min,
    { show min (min a b) c ≤ a,
      apply (le_trans : min (min a b) c ≤ min a b → min a b ≤ a → _ ≤ _),
      repeat { apply min_le_left } },
    { show min (min a b) c ≤ min b c,
      apply le_min,
      { show min (min a b) c ≤ b,
        apply (le_trans : min (min a b) c ≤ min a b → min a b ≤ b → _ ≤ _),
        apply min_le_left, apply min_le_right },
      show min (min a b) c ≤ c, by apply min_le_right } },
  { show min a (min b c) ≤ min (min a b) c,
    apply le_min,
    { show min a (min b c) ≤ min a b,
      apply le_min,
      show min a (min b c) ≤ a, by apply min_le_left,
      { show min a (min b c) ≤ b,
        apply (le_trans : min a (min b c) ≤ min b c → min b c ≤ b → _ ≤ _),
        apply min_le_right, apply min_le_left } },
    { show min a (min b c) ≤ c,
      apply (le_trans : min a (min b c) ≤ min b c → min b c ≤ c → _ ≤ _),
      repeat { apply min_le_right } } },
end

lemma aux : min a b + c ≤ min (a + c) (b + c) :=
begin
  apply le_min,
  apply add_le_add_right, apply min_le_left,
  apply add_le_add_right, apply min_le_right,
end

example : min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
  apply aux,
  rw ← sub_add_cancel (min (a + c) (b + c)) c,
  apply add_le_add_right,
  have h : min a b = min (a + c - c) (b + c - c),
    by rw [add_sub_cancel a c, add_sub_cancel b c],
  rw h,
  apply aux (a + c) (b + c) (-c),
end

#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)

example : abs a - abs b ≤ abs (a - b) :=
begin
  rw ← add_sub_cancel (abs (a - b)) (abs b), apply add_le_add_right,
  have h : abs a = abs (a - b + b), by rw sub_add_cancel, rw h,
  apply abs_add,
end

end

section
variables w x y z : ℕ

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end

example : x ∣ x^2 :=
by apply dvd_mul_right

example (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  repeat { apply dvd_add },
  { show x ∣ y * (x * z),
    apply dvd_mul_of_dvd_right,
    apply dvd_mul_right },
  show x ∣ x^2, by apply dvd_mul_right,
  { show x ∣ w^2,
    apply dvd_mul_of_dvd_left,
    exact h }
end

end

section
variables m n : ℕ
open nat

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n  : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n  : lcm 0 n = 0)

example : gcd m n = gcd n m :=
begin
  have h : ∀ x y, gcd x y ∣ gcd y x, {
    intros x y,
    apply dvd_gcd,
    apply gcd_dvd_right,
    apply gcd_dvd_left,
  },
  apply dvd_antisymm,
  repeat { apply h }
end

end

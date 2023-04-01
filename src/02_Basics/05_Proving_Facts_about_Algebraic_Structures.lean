import topology.metric_space.basic

section
variables {α : Type*} [partial_order α]
variables x y z : α

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬ x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
lt_iff_le_and_ne

end

section
variables {α : Type*} [lattice α]
variables x y z : α

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right: y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm,
  repeat {
    apply le_inf,
    apply inf_le_right,
    apply inf_le_left }
end

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm,
  { show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z),
    apply le_inf,
    { show (x ⊓ y) ⊓ z ≤ x, calc
        (x ⊓ y) ⊓ z ≤ x ⊓ y : inf_le_left
        ...         ≤ x     : inf_le_left },
    { show (x ⊓ y) ⊓ z ≤ y ⊓ z,
      apply le_inf,
      { show (x ⊓ y) ⊓ z ≤ y, calc
          (x ⊓ y) ⊓ z ≤ x ⊓ y : inf_le_left
          ...         ≤ y     : inf_le_right },
      show (x ⊓ y) ⊓ z ≤ z, from inf_le_right } },
  { show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z,
    apply le_inf,
    { show x ⊓ (y ⊓ z) ≤ x ⊓ y,
      apply le_inf,
      show x ⊓ (y ⊓ z) ≤ x, from inf_le_left,
      { show x ⊓ (y ⊓ z) ≤ y, calc
          x ⊓ (y ⊓ z) ≤ y ⊓ z : inf_le_right
          ...         ≤ y     : inf_le_left }
    },
    { show x ⊓ (y ⊓ z) ≤ z, calc
        x ⊓ (y ⊓ z) ≤ y ⊓ z : inf_le_right
        ...         ≤ z     : inf_le_right } }
end

example : x ⊔ y = y ⊔ x :=
begin
  apply le_antisymm,
  repeat {
    apply sup_le,
    apply le_sup_right,
    apply le_sup_left }
end

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
begin
  apply le_antisymm,
  { show (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z),
    apply sup_le,
    { show x ⊔ y ≤ x ⊔ (y ⊔ z),
      apply sup_le,
      { show x ≤ x ⊔ (y ⊔ z), by apply le_sup_left},
      { show y ≤ x ⊔ (y ⊔ z), calc
          y   ≤ y ⊔ z       : le_sup_left
          ... ≤ x ⊔ (y ⊔ z) : le_sup_right } },
    { show z ≤ x ⊔ (y ⊔ z), calc
        z   ≤ y ⊔ z       : le_sup_right
        ... ≤ x ⊔ (y ⊔ z) : le_sup_right } },
  { show x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z,
    apply sup_le,
    { show x ≤ (x ⊔ y) ⊔ z, calc
        x   ≤ x ⊔ y       : le_sup_left
        ... ≤ (x ⊔ y) ⊔ z : le_sup_left },
    { show y ⊔ z ≤ (x ⊔ y) ⊔ z,
      apply sup_le,
      { show y ≤ (x ⊔ y) ⊔ z, calc
          y   ≤ x ⊔ y       : le_sup_right
          ... ≤ (x ⊔ y) ⊔ z : le_sup_left },
      {show z ≤ (x ⊔ y) ⊔ z, by apply le_sup_right } } }
end

theorem absorb1 : x ⊓ (x ⊔ y) = x :=
begin
  apply le_antisymm,
  apply inf_le_left,
  apply le_inf,
  apply le_refl,
  apply le_sup_left
end

theorem absorb2 : x ⊔ (x ⊓ y) = x :=
begin
  apply le_antisymm,
  { show x ⊔ (x ⊓ y) ≤ x,
    apply sup_le,
    apply le_refl,
    apply inf_le_left },
  show x ≤ x ⊔ x ⊓ y, apply le_sup_left
end

end

section
variables {α : Type*} [distrib_lattice α]
variables x y z : α

#check (inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
#check (inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
#check (sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

end

section
variables {α : Type*} [lattice α]
variables a b c : α

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
begin
  rw h,
  rw (inf_comm : _ ⊓ a = _), rw absorb1,
  rw (inf_comm : (a ⊔ b) ⊓ _ = _),
  rw h,
  rw ← sup_assoc,
  rw (inf_comm : _ ⊓ a = _), rw absorb2,
  rw inf_comm
end

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
begin
  rw h,
  rw (sup_comm : _ ⊔ a = _), rw absorb2,
  rw (sup_comm : (a ⊓ b) ⊔ _ = _),
  rw h,
  rw ← inf_assoc,
  rw (sup_comm : _ ⊔ a = _), rw absorb1,
  rw sup_comm
end

end

section
variables {R : Type*} [ordered_ring R]
variables a b c : R

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

lemma zero_le_sub_of_le : a ≤ b → 0 ≤ b - a :=
begin
  intro h,
  rw ← sub_self a,
  repeat { rw [sub_eq_add_neg, add_comm _ (-a)] },
  apply add_le_add_left h,
end

lemma le_of_zero_le_sub : 0 ≤ b - a → a ≤ b :=
begin
  intro h,
  rw ← add_zero a,
  rw ← sub_add_cancel b a,
  rw add_comm (b - a),
  apply add_le_add_left h,
end

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c :=
begin
  apply le_of_zero_le_sub (a * c) (b * c),
  rw ← sub_mul,
  apply mul_nonneg,
  exact zero_le_sub_of_le _ _ h,
  exact h'
end

end

section
variables {X : Type*} [metric_space X]
variables x y z : X

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)


#check (nonneg_of_mul_nonneg_left : 0 ≤ (2 : ℝ) * dist x y → 0 < (2 : ℝ) → 0 ≤ dist x y)
#check (nonneg_of_mul_nonneg_left : 0 ≤ (2 : ℝ) * _ → 0 < (2 : ℝ) → 0 ≤ dist x y)
#check (nonneg_of_mul_nonneg_left : _ → 0 < (2 : ℝ) → 0 ≤ dist x y)

#check @nonneg_of_mul_nonneg_left _ _ 2 (dist x y)
#check nonneg_of_mul_nonneg_left

example (x y : X) : 0 ≤ dist x y :=
begin
  apply (nonneg_of_mul_nonneg_left : 0 ≤ 2 * dist x y → 0 < (2 : ℝ) → 0 ≤ dist x y),
  { show 0 ≤ 2 * dist x y, calc
      0   = dist x x            : by rw (dist_self x)
      ... ≤ dist x y + dist y x : dist_triangle x y x
      ... = dist x y + dist x y : by rw dist_comm y x
      ... = 2 * dist x y        : by rw ← two_mul },
  exact two_pos
end

end

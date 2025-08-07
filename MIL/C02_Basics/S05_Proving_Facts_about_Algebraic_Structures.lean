import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat exact le_inf inf_le_right inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · trans x ⊓ y
      repeat exact inf_le_left
    · apply le_inf
      · trans x ⊓ y
        · exact inf_le_left
        · exact inf_le_right
      · apply inf_le_right
  · apply le_inf
    · apply le_inf
      · apply inf_le_left
      · trans y ⊓ z
        · exact inf_le_right
        · exact inf_le_left
    · trans y ⊓ z
      repeat exact inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat exact sup_le le_sup_right le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact le_sup_left
      · trans y ⊔ z
        · exact le_sup_left
        · exact le_sup_right
    · trans y ⊔ z
      repeat exact le_sup_right
  · apply sup_le
    · trans x ⊔ y
      repeat exact le_sup_left
    · apply sup_le
      · trans x ⊔ y
        · exact le_sup_right
        · exact le_sup_left
      · exact le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · exact inf_le_left
  · exact le_inf (le_refl _) le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le (le_refl _) inf_le_left
  · exact le_sup_left
end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  have h' : ∀ x y z : α, (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z := by
    intro x y z
    repeat rw [inf_comm _ z]
    exact h z x y
  rw [h, inf_comm (a ⊔ b), absorb1, h', ← sup_assoc, absorb2]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  have h' : ∀ x y z : α, x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z) := by
    intro x y z
    repeat rw [sup_comm _ z]
    exact h z x y
  rw [h, sup_comm (a ⊓ b), absorb2, h', ← inf_assoc, absorb1]
end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem aux1 (h : a ≤ b) : 0 ≤ b - a := calc
  0 = -a + a  := by symm; rw [add_comm]; exact add_neg_cancel a
  _ ≤ -a + b  := by apply add_le_add_left h
  _ = b - a   := by rw [sub_eq_add_neg, add_comm]

theorem aux2 (h : 0 ≤ b - a) : a ≤ b := calc
  a = a + 0 := by symm; exact add_zero a
  _ ≤ a + (b - a) := by apply add_le_add_left h
  _ = b := by rw [← add_sub_assoc, add_comm]; exact add_sub_cancel_right b a

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  apply aux2
  rw [← sub_mul]
  exact mul_nonneg (aux1 _ _ h) h'
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y * 2 := by
    rw [mul_two, ← dist_self x]
    nth_rw 2 [dist_comm x y]
    apply dist_triangle
  apply nonneg_of_mul_nonneg_left h
  norm_num
end

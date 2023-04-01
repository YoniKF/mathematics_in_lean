import data.set.lattice
import data.set.function
import analysis.special_functions.log.basic

section

variables {α β : Type*}
variable  f : α → β
variables s t : set α
variables u v : set β
open function
open set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, use [x, xs] },
    right, use [x, xt] },
  rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
  { use [x, or.inl xs] },
  use [x, or.inr xt]
end

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
begin
  split,
  { intro h,
    intros x xs,
    apply h,
    use [x, xs] },
  { intro h,
    rintros y ⟨x, xs, rfl⟩,
    apply h,
    exact xs }
end

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros x ⟨y, ys, fyeqfx⟩,
  rwa ← h fyeqfx
end

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, h, rfl⟩,
  exact h,
end

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
begin
  rintros y memu,
  rcases h y with ⟨x, rfl⟩,
  use [x, memu]
end

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
sorry

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (xs | fxu),
  { left,
    use [x, xs] },
  { right,
    exact fxu }
end

variables {I : Type*} (A : I → set α) (B : I → set β)

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example (i : I) (injf : injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }

end

section
open set real

example : inj_on log { x | x > 0 } :=
begin
  intros x xpos y ypos,
  intro e,   -- log x = log y
  calc
    x   = exp (log x) : by rw exp_log xpos
    ... = exp (log y) : by rw e
    ... = y           : by rw exp_log ypos
end

example : range exp = { y | y > 0 } :=
begin
  ext y, split,
  { rintros ⟨x, rfl⟩,
    apply exp_pos },
  intro ypos,
  use log y,
  rw exp_log ypos
end

example : inj_on sqrt { x | x ≥ 0 } :=
begin
  intros x xnn y ynn e,
  calc
    x   = (sqrt x)^2 : by rw sq_sqrt xnn
    ... = (sqrt y)^2 : by rw e
    ... = y          : by rw sq_sqrt ynn
end

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
begin
    intros x xnn y ynn e,
    dsimp at e,
  calc
    x   = sqrt (x^2) : by rw sqrt_sq xnn
    ... = sqrt (y^2) : by rw e
    ... = y          : by rw sqrt_sq ynn
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
begin
  ext y, split,
  { rintro ⟨x, xnn, rfl⟩,
    apply sqrt_nonneg },
  { intro ynn,
    use [y^2, sq_nonneg y, sqrt_sq ynn] }
end

example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
begin
  ext y, split,
  { rintro ⟨x, rfl⟩,
    exact sq_nonneg x },
  { intro ynn,
    use [sqrt y, sq_sqrt ynn] }
end

end

section
variables {α β : Type*} [inhabited α]

#check (default : α)

variables (P : α → Prop) (h : ∃ x, P x)

#check classical.some h

example : P (classical.some h) := classical.some_spec h

noncomputable theory
open_locale classical

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y then classical.some h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end

variable  f : α → β
open function

example : injective f ↔ left_inverse (inverse f) f  :=
begin
  split,
  { intros finj x,
    apply finj,
    apply inverse_spec,
    use x },
  { intros linv x y feq,
    rw ←linv x,
    rw ←linv y,
    rw feq }
end

example : surjective f ↔ right_inverse (inverse f) f :=
begin
  split,
  { intros fsur y,
    apply inverse_spec,
    apply fsur },
  { intros rinv y,
    use inverse f y,
    apply rinv }
end

end

section
variable {α : Type*}
open function

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with ⟨j, h⟩,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
    { exact h₁ },
  have h₃ : j ∉ S,
    { rw ← h, exact h₁ },
  contradiction
end

end

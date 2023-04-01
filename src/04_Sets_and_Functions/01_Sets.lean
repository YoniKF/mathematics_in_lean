import data.set.lattice
import data.nat.parity
import tactic

section
variable {α : Type*}
variables (s t u : set α)

open set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xs, xu⟩,
  exact ⟨h x xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩
end

theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by exact λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  right,
  show x ∈ s ∩ u,
  exact ⟨xs, xu⟩
end

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left, exact ⟨xs, xt⟩ },
  right, exact ⟨xs, xu⟩
end

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x (⟨xs, xt⟩ | ⟨xs, xu⟩),
  exact ⟨xs, or.inl xt⟩,
  exact ⟨xs, or.inr xu⟩
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs }, dsimp,
  intro xtu, -- x ∈ t ∨ x ∈ u
  cases xtu with xt xu,
  { show false, from xnt xt },
  show false, from xnu xu
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

example : s \ (t ∪ u) ⊆ s \ t \ u :=
begin
  rintros x ⟨xs, xntu⟩,
  use xs,
  { contrapose! xntu with xt,
    left,
    exact xt },
  { contrapose! xntu with xu,
    right,
    exact xu }
end

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
set.ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

example : s ∩ t = t ∩ s :=
begin
  apply subset.antisymm,
  { rintros x ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros x ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
subset.antisymm (λ x ⟨xs, xt⟩, ⟨xt, xs⟩) (λ x ⟨xt, xs⟩, ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s :=
begin
  ext,
  split,
  exact (λ ⟨xs, _⟩, xs),
  intro xs,
  split,
  exact xs,
  left,
  exact xs
end

example : s ∪ (s ∩ t) = s :=
begin
  ext, split,
  { rintros (xs | ⟨xs, _⟩);
    exact xs },
  { intro xs,
    left,
    exact xs }
end

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext, split,
  { rintros (⟨xs, xnt⟩ | xt),
    { left, exact xs },
    { right, exact xt } },
  { rintros (xs | xt),
    { by_cases h : x ∈ t,
      { right, exact h },
      { left, exact ⟨xs, h⟩ } },
  { right, exact xt } }
end

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext, split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { use xs,
      rintro ⟨_, xt⟩,
      exact xnt xt },
    { split,
      { right,
        exact xt },
      { rintro ⟨xs, _⟩,
        exact xns xs } } },
  { rintros ⟨(xs | xt), xnst⟩,
    { left,
      use xs,
      contrapose! xnst with xt,
      use [xs, xt] },
    { right,
      use xt,
      contrapose! xnst with xs,
      use [xs, xt] } }
end


def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em
end

example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

example (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
begin
  intro n,
  simp,
  intro h,
  intro htwolt,
  cases nat.prime.eq_two_or_odd h with heqtwo hodd,
  { exfalso,
    exact (ne_of_lt htwolt).symm heqtwo },
  { intro heven,
    have := nat.even_iff.mp heven,
    rw hodd at this,
    apply one_ne_zero this }
end

#print prime
#print nat.prime

example (n : ℕ) : prime n ↔ nat.prime n := nat.prime_iff.symm

example (n : ℕ) (h : prime n) : nat.prime n :=
by { rw nat.prime_iff, exact h }

example (n : ℕ) (h : prime n) : nat.prime n :=
by rwa nat.prime_iff

end
section
variables (s t : set ℕ)

example (h₀ : ∀ x ∈ s, ¬ even x) (h₁ : ∀ x ∈ s, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x xs },
  apply h₁ x xs
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ s, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, xs, prime_x]
end

section
variable (ssubt : s ⊆ t)

include ssubt

example (h₀ : ∀ x ∈ t, ¬ even x) (h₁ : ∀ x ∈ t, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀, apply ssubt, exact xs },
  { apply h₁, apply ssubt, exact xs }
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ t, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, ssubt xs, prime_x]
end

end

end

section
variables {α I : Type*}
variables A B : I → set α
variable  s : set α
open set

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  rintros ⟨i, xAi, xs⟩,
  exact ⟨xs, ⟨i, xAi⟩⟩
end

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    intro i,
    exact (h i).2 },
  rintros ⟨h1, h2⟩ i,
  split,
  { exact h1 i },
  exact h2 i
end

open_locale classical

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext,
  simp only [mem_union_eq, mem_Inter],
  split,
  { rintro (xs | h),
    { intro i,
      right,
      exact xs },
    { intro i,
      left,
      exact h i } },
  { intro h,
    by_cases h' : x ∈ s,
    { left,
      exact h' },
    { right,
      intro i,
      cases h i with xAi xs,
      { exact xAi },
      { contradiction } } }
end

def primes : set ℕ := {x | nat.prime x}

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, rw mem_Union₂, refl }

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, simp }

example : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x = 1} :=
begin
  intro x,
  contrapose!,
  simp,
  apply nat.exists_prime_and_dvd
end

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
begin
  apply eq_univ_iff_forall.mpr,
  intro x,
  simp,
  rcases nat.exists_infinite_primes x with ⟨p, xlep, pprime⟩,
  use [p, pprime, xlep]
end

end

section
open set

variables {α : Type*} (s : set (set α))

example : ⋃₀ s = ⋃ t ∈ s, t :=
begin
  ext x,
  rw mem_Union₂,
  refl
end

example : ⋂₀ s = ⋂ t ∈ s, t :=
begin
  ext x,
  rw mem_Inter₂,
  refl
end

end


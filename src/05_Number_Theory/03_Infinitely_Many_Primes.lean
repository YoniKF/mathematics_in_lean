import data.nat.prime
import algebra.big_operators
import tactic

open_locale big_operators

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
begin
  cases m, contradiction,
  cases m, contradiction,
  repeat { apply nat.succ_le_succ },
  apply zero_le
end

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
begin
  by_contradiction h,
  push_neg at h,
  interval_cases m; contradiction
end

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
begin
  by_contradiction h,
  push_neg at h,
  revert m h h0 h1,
  dec_trivial
end

example {m : ℕ} (h : m < 2) : m = 0 ∨ m = 1 :=
by dec_trivial!

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
by omega

theorem exists_prime_factor {n : nat} (h : 2 ≤ n) :
  ∃ p : nat, p.prime ∧ p ∣ n :=
begin
  by_cases np : n.prime,
  { use [n, np, dvd_rfl] },
  induction n using nat.strong_induction_on with n ih,
  dsimp at ih,
  rw nat.prime_def_lt at np,
  push_neg at np,
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩,
  have : m ≠ 0,
  { intro mz,
    rw [mz, zero_dvd_iff] at mdvdn,
    linarith },
  have mgt2 : 2 ≤ m := two_le this mne1,
  by_cases mp : m.prime,
  { use [m, mp, mdvdn] },
  rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩,
  use [p, pp, pdvd.trans mdvdn]
end

#check nat.factorial_pos
#check @nat.dvd_factorial
#check @nat.dvd_sub

theorem primes_infinite : ∀ n, ∃ p > n, nat.prime p :=
begin
  intro n,
  have : 2 ≤ nat.factorial (n + 1) + 1,
    from nat.succ_le_succ (nat.one_le_of_lt (n + 1).factorial_pos),
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩,
  refine ⟨p, _, pp⟩,
  show p > n,
  by_contradiction ple, push_neg at ple,
  have : p ∣ nat.factorial (n + 1),
    by { apply nat.dvd_factorial pp.pos, linarith },
  have : p ∣ 1,
    by {
      rw ←(n + 1).factorial.add_sub_cancel_left 1,
      apply nat.dvd_sub ((n + 1).factorial.le_add_right _); assumption
    },
  show false,
  have : p ≤ 1, from nat.le_of_dvd zero_lt_one this,
  have : 1 < p, from pp.one_lt,
  linarith
end

open finset

section
variables {α : Type*} [decidable_eq α] (r s t : finset α)

example : r ∩ (s ∪ t) ⊆ (r ∩ s) ∪ (r ∩ t) :=
begin
  rw subset_iff,
  intro x,
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter],
  tauto
end

example : r ∩ (s ∪ t) ⊆ (r ∩ s) ∪ (r ∩ t) :=
by { simp [subset_iff], intro x, tauto }

example : (r ∩ s) ∪ (r ∩ t) ⊆ r ∩ (s ∪ t) :=
by { simp [subset_iff], intro x, tauto }

example : (r ∩ s) ∪ (r ∩ t) = r ∩ (s ∪ t) :=
by { ext x, simp, tauto }

end

section
variables {α : Type*} [decidable_eq α] (r s t : finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ (s ∩ t) :=
by { ext, simp, tauto }

example : (r \ s \ t) = r \ (s ∪ t) :=
by { ext, simp, tauto }


end
example (s : finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ (∏ i in s, i) :=
finset.dvd_prod_of_mem _ h

theorem nat.prime.eq_of_dvd_of_prime {p q : ℕ}
    (prime_p : nat.prime p) (prime_q : nat.prime q) (h : p ∣ q) :
  p = q :=
begin
  cases prime_q.eq_one_or_self_of_dvd _ h with pe1 peq,
  { linarith [prime_p.two_le] },
  assumption
end

theorem mem_of_dvd_prod_primes {s : finset ℕ} {p : ℕ} (prime_p : p.prime) :
  (∀ n ∈ s, nat.prime n) →  (p ∣ ∏ n in s, n) → p ∈ s :=
begin
  intros h₀ h₁,
  induction s using finset.induction_on with a s ans ih,
  { simp at h₁,
    linarith [prime_p.two_le] },
  simp [finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁,
  rw mem_insert,
  cases h₁,
  { left, apply prime_p.eq_of_dvd_of_prime h₀.left h₁ },
  right, exact ih h₀.right h₁
end

example (s : finset ℕ) (x : ℕ) : x ∈ s.filter nat.prime ↔ x ∈ s ∧ x.prime :=
mem_filter

theorem primes_infinite' : ∀ (s : finset nat), ∃ p, nat.prime p ∧ p ∉ s :=
begin
  intro s,
  by_contradiction h,
  push_neg at h,
  set s' := s.filter nat.prime with s'_def,
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.prime,
  { intro n,
    simp [s'_def],
    apply h },
  have : 2 ≤ (∏ i in s', i) + 1,
  { apply nat.succ_le_succ,
    apply nat.succ_le_of_lt,
    apply finset.prod_pos,
    intros n h,
    apply nat.prime.pos,
    exact mem_s'.mp h },
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩,
  have : p ∣ (∏ i in s', i),
  { apply finset.dvd_prod_of_mem,
    exact mem_s'.mpr pp },
  have : p ∣ 1,
  { convert nat.dvd_sub' pdvd this, simp },
  show false,
  { linarith [nat.le_of_dvd zero_lt_one this, pp.one_lt] }
end

theorem bounded_of_ex_finset (Q : ℕ → Prop):
  (∃ s : finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n :=
begin
  rintros ⟨s, hs⟩,
  use s.sup id + 1,
  intros k Qk,
  apply nat.lt_succ_of_le,
  show id k ≤ s.sup id,
  apply le_sup (hs k Qk)
end

theorem ex_finset_of_bounded (Q : ℕ → Prop) [decidable_pred Q] :
  (∃ n, ∀ k, Q k → k ≤ n) → (∃ s : finset ℕ, ∀ k, Q k ↔ k ∈ s) :=
begin
  rintros ⟨n, hn⟩,
  use (range (n + 1)).filter Q,
  intro k,
  simp [nat.lt_succ_iff],
  exact hn k
end

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 :=
by { rw [add_comm, nat.add_mul_mod_self_left], norm_num }

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) :
  m % 4 = 3 ∨ n % 4 = 3 :=
begin
  revert h,
  rw [nat.mul_mod],
  have : m % 4 < 4 := nat.mod_lt m (by norm_num),
  interval_cases m % 4 with hm; simp [hm],
  have : n % 4 < 4 := nat.mod_lt n (by norm_num),
  interval_cases n % 4 with hn; simp [hn]; norm_num
end

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n :=
by apply two_le; { intro neq, rw neq at h, norm_num at h }

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) :
  (n / m) ∣ n ∧ n / m < n :=
begin
  split,
  { exact nat.div_dvd_of_dvd h₀ },
  apply nat.div_lt_self,
  { exact (lt_of_lt_of_le zero_lt_two h₁).trans h₂ },
  exact lt_of_lt_of_le one_lt_two h₁
end

theorem exists_prime_factor_mod_4_eq_3 {n : nat} (h : n % 4 = 3) :
  ∃ p : nat, p.prime ∧ p ∣ n ∧ p % 4 = 3 :=
begin
  by_cases np : n.prime,
  { use [n, np, dvd_rfl, h] },
  induction n using nat.strong_induction_on with n ih,
  dsimp at ih,
  rw nat.prime_def_lt at np,
  push_neg at np,
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩,
  have mge2 : 2 ≤ m,
  { apply two_le _ mne1,
    intro mz,
    rw [mz, zero_dvd_iff] at mdvdn, linarith },
  have neq : m * (n / m) = n := nat.mul_div_cancel' mdvdn,
  have : m % 4 = 3 ∨ (n / m) % 4 = 3,
  { apply mod_4_eq_3_or_mod_4_eq_3, rw [neq, h] },
  cases this with h1 h1,
  { by_cases mp : m.prime,
    { use [m, mp, mdvdn, h1] },
    rcases ih m mltn h1 mp with ⟨p, pp, pdvdm, h2⟩,
    use [p, pp, pdvdm.trans mdvdn, h2] },
  { set k := n / m,
    obtain ⟨kdvdn, kltn⟩ := aux mdvdn mge2 mltn,
    by_cases kp : k.prime,
    { use [k, kp, kdvdn, h1] },
    rcases ih k kltn h1 kp with ⟨p, pp, pdvdk, h2⟩,
    use [p, pp, pdvdk.trans kdvdn, h2] },
end

example (m n : ℕ) (s : finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s :=
by rwa mem_erase at h

example (m n : ℕ) (s : finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s :=
by { simp at h, assumption }

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, nat.prime p ∧ p % 4 = 3 :=
begin
  by_contradiction h,
  push_neg at h,
  cases h with n hn,
  have : ∃ s : finset ℕ, ∀ p : ℕ, p.prime ∧ p % 4 = 3 ↔ p ∈ s,
  { apply ex_finset_of_bounded,
    use n,
    contrapose! hn,
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩,
    exact ⟨p, pltn, pp, p4⟩ },
  cases this with s hs,
  have h₀ : 2 ≤ 4 * (∏ i in erase s 3, i) + 3,
  { apply le_add_of_nonneg_of_le,
    { apply nat.zero_le },
    apply nat.le_succ },
  have h₁ : (4 * (∏ i in erase s 3, i) + 3) % 4 = 3,
  { rw [add_comm, nat.add_mul_mod_self_left],
    norm_num },
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩,
  have ps : p ∈ s,
  { apply (hs p).mp,
    use [pp, p4eq] },
  have pne3 : p ≠ 3,
  { rintro rfl,
    have : 3 ∣ ∏ i in s.erase 3, i,
    { have := (nat.dvd_add_iff_left (dvd_refl 3)).mpr pdvd,
      cases nat.prime_three.dvd_mul.mp this,
      { contrapose h,
        norm_num },
      assumption },
    have h := mem_of_dvd_prod_primes nat.prime_three _ this,
    { rw mem_erase at h,
      have := h.left,
      contradiction },
    intros m mmem,
    apply ((hs m).mpr _).left,
    apply (mem_erase.mp mmem).right },
  have : p ∣ 4 * (∏ i in erase s 3, i),
  { apply dvd_mul_of_dvd_right,
    apply dvd_prod_of_mem,
    apply mem_erase.mpr,
    use [pne3, ps] },
  have : p ∣ 3,
  { rw [←nat.add_sub_cancel 3 (4 * (∏ i in erase s 3, i)), add_comm],
    apply nat.dvd_sub,
    { apply nat.le_add_right },
    repeat { assumption } },
  have : p = 3,
  { apply pp.eq_of_dvd_of_prime nat.prime_three,
    assumption },
  contradiction
end



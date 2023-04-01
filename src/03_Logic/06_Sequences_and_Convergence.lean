import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
by { ext u v, ring }

example (a b : ℝ) : abs a = abs (a - b + b) :=
by  { congr, ring }

example {a : ℝ} (h : 1 < a) : a < a * a :=
begin
  convert (mul_lt_mul_right _).2 h,
  { rw [one_mul] },
  exact lt_trans zero_lt_one h
end

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n nge, dsimp,
  simp,
  apply εpos
end

theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ}
  (cs : converges_to s a) (ct : converges_to t b):
converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε εpos, dsimp,
  have ε2pos : 0 < ε / 2, from half_pos εpos,
  cases cs (ε / 2) ε2pos with Ns hs,
  cases ct (ε / 2) ε2pos with Nt ht,
  use max Ns Nt,
  intros n nge,
  rw max_le_iff at nge,
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| : by { congr, ring }
    ...                   ≤ |s n - a| + |t n - b|   : by { apply abs_add }
    ...                   < ε / 2 + ε / 2           : by { linarith [hs n nge.1, ht n nge.2] }
    ...                   = ε                       : add_halves ε
end

theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ}
    (c : ℝ) (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext, rw [h, zero_mul] },
    rw [h, zero_mul] },
  have acpos : 0 < abs c,
    from abs_pos.mpr h,
  intros ε εpos, dsimp,
  have εacpos : 0 < ε / |c|, from div_pos εpos acpos,
  cases cs _ εacpos with N hs,
  use N,
  intros n nge,
  calc
    |c * s n - c * a| = |c| * |s n - a| : by { rw [←mul_sub, abs_mul] }
    ...               < |c| * ε / |c|   : by { rw ← mul_div,
                                               apply (mul_lt_mul_left acpos).mpr,
                                               exact hs n nge}
    ...               = ε               : by { rw mul_comm, apply mul_div_cancel, linarith }
end

theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n nge,
  calc
    |s n|     = |s n - a + a|   : by { congr, rw sub_add_cancel }
    ...       ≤ |s n - a| + |a| : abs_add _ _
    ...       < 1 + |a|         : add_lt_add_right (h n nge) _
    ...       = |a| + 1         : add_comm _ _
end

lemma aux {s t : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (λ n, s n * t n) 0 :=
begin
  intros ε εpos, dsimp,
  rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩,
  have Bpos : 0 < B,
    from lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _)),
  have pos₀ : ε / B > 0,
    from div_pos εpos Bpos,
  cases ct _ pos₀ with N₁ h₁,
  use max N₀ N₁,
  intros n nge,
  rw max_le_iff at nge,
  have h₀n := le_of_lt (h₀ _ nge.1),
  have h₁n : |t n| < ε / B, by { rw ← sub_zero (t n), exact h₁ _ nge.2},
  calc
    |s n * t n - 0| = |s n| * |t n| : by { rw sub_zero, rw abs_mul }
    ...             ≤ B * |t n|     : mul_le_mul_of_nonneg_right h₀n (abs_nonneg _)
    ...             < B * (ε / B)   : (mul_lt_mul_left Bpos).mpr h₁n
    ...             = ε             : mul_div_cancel' _ (ne_of_lt Bpos).symm
end

theorem converges_to_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n * t n) (a * b) :=
begin
  have h₁ : converges_to (λ n, s n * (t n - b)) 0,
  { apply aux cs,
    convert converges_to_add ct (converges_to_const (-b)),
    ring },
  convert (converges_to_add h₁ (converges_to_mul_const b cs)),
  { ext, ring },
  ring
end

theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b :=
begin
  by_contradiction abne,
  have : abs (a - b) > 0,
  { change 0 < |a - b|,
    rw abs_pos,
    apply sub_ne_zero_of_ne,
    assumption },
  let ε := abs (a - b) / 2,
  have εpos : ε > 0,
  { change abs (a - b) / 2 > 0, linarith },
  cases sa ε εpos with Na hNa,
  cases sb ε εpos with Nb hNb,
  let N := max Na Nb,
  have absa : abs (a - s N) < ε,
  { rw abs_sub_comm, apply hNa, apply le_max_left },
  have absb : abs (s N - b) < ε,
  { apply hNb, apply le_max_right },
  have : abs (a - b) < abs (a - b),
  { calc
      |a - b| = |(a - s N) + (s N - b)| : by { congr, abel }
      ...     ≤ |a - s N| + |s N - b|   : abs_add _ _
      ...     < ε + ε                   : add_lt_add absa absb
      ...     = |a - b|                 : add_halves _ },
  exact lt_irrefl _ this
end

section
variables {α : Type*} [linear_order α]

def converges_to' (s : α → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

end


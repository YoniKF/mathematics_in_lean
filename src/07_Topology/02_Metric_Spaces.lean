import topology.instances.real
import analysis.normed_space.banach_steinhaus

open set filter
open_locale topological_space filter


variables {X : Type*} [metric_space X] (a b c : X)

#check (dist a b : ℝ)

#check (dist_nonneg : 0 ≤ dist a b)

#check (dist_eq_zero : dist a b  = 0 ↔ a = b)

#check (dist_comm a b : dist a b  = dist b a)

#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)


-- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.
#check emetric_space
#check pseudo_metric_space
#check pseudo_emetric_space



example {u : ℕ → X} {a : X} :
  tendsto u at_top (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
metric.tendsto_at_top

example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} :
  continuous f ↔
  ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
metric.continuous_iff



example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) :
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
by continuity


example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) :
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))




example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) :
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
begin
  apply continuous.dist,
  exact hf.comp continuous_fst,
  exact hf.comp continuous_snd
end

example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) :
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
(hf.comp continuous_fst).dist (hf.comp continuous_snd)



example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) :
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
hf.fst'.dist hf.snd'



example {f : ℝ → X} (hf : continuous f) : continuous (λ x : ℝ, f (x^2 + x)) :=
begin
  apply hf.comp,
  apply continuous.add,
  { apply continuous_pow },
  exact continuous_id
end

example {f : ℝ → X} (hf : continuous f) : continuous (λ x : ℝ, f (x^2 + x)) :=
hf.comp ((continuous_pow _).add continuous_id)


example {X Y : Type*} [metric_space X] [metric_space Y] (f : X → Y) (a : X) :
continuous_at f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
metric.continuous_at_iff



variables r : ℝ

example : metric.ball a r = {b | dist b a < r} := rfl

example : metric.closed_ball a r = {b | dist b a ≤ r} := rfl



example (hr : 0 < r) : a ∈ metric.ball a r := metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ metric.closed_ball a r := metric.mem_closed_ball_self hr


example (s : set X) : is_open s ↔ ∀ x ∈ s, ∃ ε > 0, metric.ball x ε ⊆ s :=
metric.is_open_iff



example {s : set X} : is_closed s ↔ is_open sᶜ :=
is_open_compl_iff.symm

example {s : set X} (hs : is_closed s) {u : ℕ → X} (hu : tendsto u at_top (𝓝 a))
  (hus : ∀ n, u n ∈ s) : a ∈ s :=
hs.mem_of_tendsto hu (eventually_of_forall hus)

example {s : set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ metric.ball b ε :=
metric.mem_closure_iff


example {u : ℕ → X} (hu : tendsto u at_top (𝓝 a)) {s : set X} (hs : ∀ n, u n ∈ s) :
  a ∈ closure s :=
begin
  rw metric.mem_closure_iff,
  rw metric.tendsto_at_top at hu,
  intros ε εpos,
  cases hu ε εpos with N hN,
  use [u N, hs N],
  rw dist_comm,
  apply hN,
  exact le_rfl
end



example {x : X} {s : set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, metric.ball x ε ⊆ s :=
metric.nhds_basis_ball.mem_iff

example {x : X} {s : set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, metric.closed_ball x ε ⊆ s :=
metric.nhds_basis_closed_ball.mem_iff




example : is_compact (set.Icc 0 1 : set ℝ) :=
is_compact_Icc

example {s : set X} (hs : is_compact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
  ∃ a ∈ s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 a) :=
hs.tendsto_subseq hu

example {s : set X} (hs : is_compact s) (hs' : s.nonempty)
  {f : X → ℝ} (hfs : continuous_on f s) :
  ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
hs.exists_forall_le hs' hfs

example {s : set X} (hs : is_compact s) (hs' : s.nonempty)
  {f : X → ℝ} (hfs : continuous_on f s) :
  ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
hs.exists_forall_ge hs' hfs

example {s : set X} (hs : is_compact s) : is_closed s :=
hs.is_closed



example {X : Type*} [metric_space X] [compact_space X] : is_compact (univ : set X) :=
compact_univ


#check is_compact.is_closed


example {X : Type*} [metric_space X] {Y : Type*} [metric_space Y] {f : X → Y} :
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
metric.uniform_continuous_iff



example {X : Type*} [metric_space X] [compact_space X] {Y : Type*} [metric_space Y]
  {f : X → Y} (hf : continuous f) : uniform_continuous f :=
begin
  rw metric.uniform_continuous_iff,
  intros ε εpos,
  let φ : X × X → ℝ := λ p, dist (f p.1) (f p.2),
  let K := {p : X × X | ε ≤ φ p},
  have cont_φ : continuous φ := (hf.comp continuous_fst).dist (hf.comp continuous_snd),
  have comp_K : is_compact K := (is_closed_le continuous_const cont_φ).is_compact,
  cases eq_empty_or_nonempty K with hK,
  { use [1, one_pos],
    intros a b _,
    apply lt_of_not_le,
    change (a, b) ∉ K,
    rw hK,
    apply not_mem_empty },
  rcases comp_K.exists_forall_le h continuous_dist.continuous_on with ⟨⟨x₀, x₁⟩, xx_mem, xx_inf⟩,
  use dist x₀ x₁,
  split,
  { apply dist_pos.mpr,
    rintro rfl,
    dsimp [φ] at xx_mem,
    rw dist_self at xx_mem,
    linarith },
  intros a b hlt,
  apply lt_of_not_le,
  change (a, b) ∉ K,
  intro ab_mem,
  have := xx_inf (a, b) ab_mem,
  linarith
end




example (u : ℕ → X) : cauchy_seq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N,  ∀ n ≥ N, dist (u m) (u n) < ε :=
metric.cauchy_seq_iff

example (u : ℕ → X) : cauchy_seq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
metric.cauchy_seq_iff'


example [complete_space X] (u : ℕ → X) (hu : cauchy_seq u) : ∃ x, tendsto u at_top (𝓝 x) :=
cauchy_seq_tendsto_of_complete hu



open_locale big_operators
open finset


lemma cauchy_seq_of_le_geometric_two' {u : ℕ → X} (hu : ∀ (n : ℕ), dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) :
  cauchy_seq u :=
begin
  rw metric.cauchy_seq_iff',
  intros ε ε_pos,
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε,
  { have half_nonneg : (0 : ℝ) ≤ 1 / 2, by norm_num,
    have half_lt_one : 1 / 2 < (1 : ℝ), by norm_num,
    have half_pow_vanishes := tendsto_pow_at_top_nhds_0_of_lt_1 half_nonneg half_lt_one,
    rw metric.tendsto_at_top at half_pow_vanishes,
    cases half_pow_vanishes (ε / 2) (half_pos ε_pos) with N hN,
    use N,
    have := hN N le_rfl,
    rw real.dist_0_eq_abs at this,
    have half_pow_pos : (0 : ℝ) < (1 / 2) ^ N, { apply pow_pos, norm_num },
    rw abs_of_pos half_pow_pos at this,
    rw ← one_div_pow,
    linarith },
  use N,
  intros n hn,
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn,
  calc dist (u (N + k)) (u N) = dist (u (N+0)) (u (N + k)) : by { rw dist_comm, rw add_zero }
  ... ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) : dist_le_range_sum_dist (λ n, u (N + n)) k
  ... ≤ ∑ i in range k, (1/2 : ℝ)^(N+i) : by { apply sum_le_sum,
                                               intros n _,
                                               apply hu }
  ... = 1/2^N*∑ i in range k, (1 / 2) ^ i : by { rw mul_sum,
                                                 congr, ext,
                                                 rw [pow_add, one_div_pow], }
  ... ≤ 1/2^N*2 : by { apply (mul_le_mul_left _).mpr,
                       { apply sum_geometric_two_le },
                       rw ← one_div_pow, apply pow_pos, norm_num }
  ... < ε : hN
end


open metric

example [complete_space X] (f : ℕ → set X) (ho : ∀ n, is_open (f n)) (hd : ∀ n, dense (f n)) : dense (⋂n, f n) :=
begin
  let B : ℕ → ℝ := λ n, (1/2)^n,
  have Bpos : ∀ n, 0 < B n, by simp,
  /- Translate the density assumption into two functions `center` and `radius` associating
  to any n, x, δ, δpos a center and a positive radius such that
  `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
  We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have : ∀ (n : ℕ)  (x : X) (δ > 0), ∃ (y : X) (r > 0), r ≤ B (n+1) ∧ closed_ball y r ⊆ (closed_ball x δ) ∩ f n,
  { intros n x δ δpos,
    rcases metric.mem_closure_iff.mp (hd n x) (δ / 2) (half_pos δpos) with ⟨y, ymem, dxy⟩,
    use y,
    rcases is_open_iff.mp (ho n) y ymem with ⟨ε, εpos, byε⟩,
    let r := min (δ / 2) (min (ε / 2) (B (n + 1))),
    use [r, by { simp [(half_pos δpos), (half_pos εpos)]}, by simp],
    apply set.subset_inter,
    { apply closed_ball_subset_closed_ball',
      rw dist_comm,
      apply le_of_lt,
      calc r + dist x y < r + δ / 2     : by { apply add_lt_add_left, exact dxy }
           ...          ≤ δ / 2 + δ / 2 : by { apply add_le_add_right, simp }
           ...          = δ             : add_halves δ },
    apply subset_trans _ byε,
    apply closed_ball_subset_ball,
    calc r   ≤ ε / 2 : by simp
         ... < ε     : half_lt_self εpos },
  choose! center radius Hpos HB Hball using this,
  intros x,
  rw mem_closure_iff_nhds_basis nhds_basis_closed_ball,
  intros ε εpos,
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
  `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
  `closed_ball (c n) (r n)` is included in the previous ball and in `f n`, and such that
  `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
  limit which belongs to all the `f n`. -/
  let F : ℕ → (X × ℝ) := λn, nat.rec_on n (prod.mk x (min ε (B 0)))
                              (λn p, prod.mk (center n p.1 p.2) (radius n p.1 p.2)),
  let c : ℕ → X := λ n, (F n).1,
  let r : ℕ → ℝ := λ n, (F n).2,
  have rpos : ∀ n, 0 < r n,
  { intro n, induction n with n ih,
    { exact lt_min εpos (Bpos 0) },
    exact Hpos n (c n) (r n) ih },
  have rB : ∀n, r n ≤ B n,
  { intro n, cases n,
    { apply min_le_right },
    exact HB n (c n) (r n) (rpos n) },
  have incl : ∀n, closed_ball (c (n+1)) (r (n+1)) ⊆ (closed_ball (c n) (r n)) ∩ (f n),
  { intro n,
    apply Hball n (c n) (r n) (rpos n) },
  have cdist : ∀ n, dist (c n) (c (n+1)) ≤ B n,
  { intro n,
    rw dist_comm,
    change c (n+1) ∈ closed_ball (c n) (B n),
    apply mem_of_mem_of_subset,
    exact mem_of_mem_inter_left (incl n (mem_closed_ball_self (rpos (n+1)).le)),
    apply closed_ball_subset_closed_ball,
    exact rB n },
  have : cauchy_seq c, from cauchy_seq_of_le_geometric_two' cdist,
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchy_seq_tendsto_of_complete this with ⟨y, ylim⟩,
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y,
  have I : ∀n, ∀ m ≥ n, closed_ball (c m) (r m) ⊆ closed_ball (c n) (r n),
  { intros n m nlem,
    obtain ⟨k, rfl : m = n + k⟩ := le_iff_exists_add.mp nlem,
    induction k with k ih,
    { refl },
    transitivity closed_ball (c (n + k)) (r (n + k)),
    { exact (set.subset_inter_iff.mp (incl (n + k))).left },
    exact ih (n.le_add_right k) },
  have yball : ∀n, y ∈ closed_ball (c n) (r n),
  { intro n,
    apply is_closed_ball.mem_of_tendsto ylim,
    rw eventually_iff_exists_mem,
    use [Ici n, Ici_mem_at_top n],
    intros m mgen, dsimp at mgen,
    apply I n m mgen,
    exact mem_closed_ball_self (rpos m).le },
  split,
  { apply mem_Inter_of_mem,
    intro n,
    have ymem := Hball n (c n) (r n) (rpos n) (yball (n + 1)),
    rw mem_inter_iff at ymem,
    exact ymem.right },
  have rε : r 0 ≤ ε, from min_le_left _ _,
  apply closed_ball_subset_closed_ball rε,
  exact yball 0
end




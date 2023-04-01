import topology.instances.real

open set filter
open_locale topological_space filter

def principal {α : Type*} (s : set α) : filter α :=
{ sets := {t | s ⊆ t},
  univ_sets := subset_univ s,
  sets_of_superset := λ _ _, subset.trans,
  inter_sets := λ _ _, subset_inter }

example : filter ℕ :=
{ sets := {s | ∃ a, ∀ b, a ≤ b → b ∈ s},
  univ_sets := ⟨0, λ _ _, mem_univ _⟩,
  sets_of_superset := by { rintros _ _ ⟨a, h⟩ hsub,
                           use a,
                           intros,
                           apply hsub,
                           apply h,
                           assumption },
  inter_sets := by { rintros _ _ ⟨a, h⟩ ⟨a', h'⟩,
                     use max a a',
                     intros,
                     split,
                     { apply h, transitivity max a a', apply le_max_left, assumption },
                     apply h', transitivity max a a', apply le_max_right, assumption } }

def tendsto₁ {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) :=
∀ V ∈ G, f ⁻¹' V ∈ F

def tendsto₂ {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) :=
map f F ≤ G

lemma aux {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) :
  tendsto₂ f F G ↔ tendsto₁ f F G := iff.rfl

#check (@filter.map_mono : ∀ {α β} {m : α → β}, monotone (map m))
#check (@filter.map_map : ∀ {α β γ} {f : filter α} {m : α → β} {m' : β → γ},
                            map m' (map m f) = map (m' ∘ m) f)

example {X Y Z : Type*} {F : filter X} {G : filter Y} {H : filter Z} {f : X → Y} {g : Y → Z}
  (hf : tendsto₁ f F G) (hg : tendsto₁ g G H) : tendsto₁ (g ∘ f) F H :=
begin
  rw tendsto₁,
  intros,
  rw preimage_comp,
  apply hf,
  apply hg,
  assumption
end

example {X Y Z : Type*} {F : filter X} {G : filter Y} {H : filter Z} {f : X → Y} {g : Y → Z}
  (hf : tendsto₁ f F G) (hg : tendsto₁ g G H) : tendsto₁ (g ∘ f) F H :=
begin
  rw [←aux, tendsto₂] at *,
  rw ←map_map,
  transitivity' map g G,
  apply map_mono hf,
  assumption
end

variables (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap (coe : ℚ → ℝ) (𝓝 x₀)
#check tendsto (f ∘ coe) (comap (coe : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

section
variables {α β γ : Type*} (F : filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)
end

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ᶠ 𝓝 y₀ := nhds_prod_eq

#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
   (𝓝 (x₀, y₀)) ↔
    tendsto (prod.fst ∘ f) at_top (𝓝 x₀) ∧ tendsto (prod.snd ∘ f) at_top (𝓝 y₀) :=
begin
  repeat {rw tendsto},
  rw [nhds_prod_eq, filter.prod],
  nth_rewrite_rhs 0 ←map_map,
  nth_rewrite_rhs 2 ←map_map,
  nth_rewrite_rhs 0 map_le_iff_le_comap,
  nth_rewrite_rhs 1 map_le_iff_le_comap,
  apply le_inf_iff
end

example (x₀ : ℝ) : has_basis (𝓝 x₀) (λ ε : ℝ, 0 < ε) (λ ε, Ioo (x₀ - ε) (x₀ + ε)) :=
nhds_basis_Ioo_pos x₀

example (u : ℕ → ℝ) (x₀ : ℝ) :
  tendsto u at_top (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) :=
begin
  have : at_top.has_basis (λ n : ℕ, true) Ici := at_top_basis,
  rw this.tendsto_iff (nhds_basis_Ioo_pos x₀),
  simp
end

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in at_top, P n) (hQ : ∀ᶠ n in at_top, Q n) :
  ∀ᶠ n in at_top, P n ∧ Q n := hP.and hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in at_top, u n = v n) (x₀ : ℝ) :
  tendsto u at_top (𝓝 x₀) ↔ tendsto v at_top (𝓝 x₀) :=
tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[at_top] v) (x₀ : ℝ) :
  tendsto u at_top (𝓝 x₀) ↔ tendsto v at_top (𝓝 x₀) :=
tendsto_congr' h

#check @eventually_of_forall
#check @eventually.mono
#check @eventually.and

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in at_top, P n) (hQ : ∀ᶠ n in at_top, Q n)
  (hR : ∀ᶠ n in at_top, P n ∧ Q n → R n) :
  ∀ᶠ n in at_top, R n :=
begin
  apply (hP.and (hQ.and hR)).mono,
  rintros n ⟨h, h', h''⟩,
  exact h'' ⟨h, h'⟩
end

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in at_top, P n) (hQ : ∀ᶠ n in at_top, Q n)
  (hR : ∀ᶠ n in at_top, P n ∧ Q n → R n) :
  ∀ᶠ n in at_top, R n :=
begin
  filter_upwards [hP, hQ, hR],
  intros n h h' h'',
  exact h'' ⟨h, h'⟩
end

#check mem_closure_iff_cluster_pt
#check le_principal_iff
#check ne_bot_of_le

example (u : ℕ → ℝ) (M : set ℝ) (x : ℝ)
  (hux : tendsto u at_top (𝓝 x)) (huM : ∀ᶠ n in at_top, u n ∈ M) : x ∈ closure M :=
begin
  rw [mem_closure_iff_cluster_pt, cluster_pt],
  apply ne_bot_of_le ∘ le_inf hux,
  rw le_principal_iff,
  exact huM
end

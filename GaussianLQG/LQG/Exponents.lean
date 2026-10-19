import GaussianLQG.Core.Setup

/-!
# Small-γ behaviour of the exponents (blueprint Lemma `lem:exponents`)

Blueprint Lemma `lem:exponents` (source (1.3)), for an arbitrary `Setup`: assume (S1), i.e.
`|d_γ - 2| ≤ C₀ γ` for `γ ∈ (0, γ₀]`, where `d_γ = γ / ξ_γ`. Then

* there are `γ_e ∈ (0, 2)` and `C₁` such that for `γ ∈ (0, γ_e]`:
  `γ/3 ≤ ξ_γ ≤ γ`, `ξ_γ ≤ 1/10` and `|ξ_γ Q_γ - 1| ≤ C₁ ξ_γ` (`Setup.exists_exponents`);
* `ξ_γ / γ → 1/2` (`Setup.tendsto_xi_div_self`) and `ξ_γ Q_γ → 1` (`Setup.tendsto_xi_mul_Q`)
  as `γ ↓ 0`.

Proof: `ξ_γ / γ = 1 / d_γ` and `ξ_γ Q_γ - 1 = (2 - d_γ + γ²/2) / d_γ`, with `d_γ ∈ [1, 3]` once
`C₀ γ ≤ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace GaussianLQG

namespace Setup

variable (S : Setup)

/-- The quantitative content of (S1) used below: for `γ ∈ (0, γ_e]` (with `γ_e ≤ 1/10`), the
dimension `d_γ = γ / ξ_γ` satisfies `|2 - d_γ| ≤ C γ` and `C γ ≤ 1`, with `C ≥ 1`. -/
theorem exists_dim_bound : ∃ γe C : ℝ, 0 < γe ∧ γe ≤ 1 / 10 ∧ 1 ≤ C ∧
    ∀ γ ∈ Ioc (0 : ℝ) γe, 0 < S.ξ γ ∧ |2 - γ / S.ξ γ| ≤ C * γ ∧ C * γ ≤ 1 := by
  obtain ⟨γ₀, C₀, hγ₀, hS1⟩ := S.S1
  set C : ℝ := max C₀ 0 + 1 with hC
  have hC₀C : C₀ ≤ C := by simp only [hC]; linarith [le_max_left C₀ 0]
  have hC1 : 1 ≤ C := by simp only [hC]; linarith [le_max_right C₀ 0]
  have hCpos : 0 < C := by linarith
  refine ⟨min (min γ₀ (1 / 10)) (1 / C), C, lt_min (lt_min hγ₀ (by norm_num)) (by positivity),
    (min_le_left _ _).trans (min_le_right _ _), hC1, ?_⟩
  rintro γ ⟨hγ0, hγ⟩
  have hγ₀' : γ ≤ γ₀ := hγ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγ10 : γ ≤ 1 / 10 := hγ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγC : γ ≤ 1 / C := hγ.trans (min_le_right _ _)
  refine ⟨S.ξ_pos γ hγ0 (by linarith), ?_, ?_⟩
  · rw [abs_sub_comm]
    exact (hS1 γ ⟨hγ0, hγ₀'⟩).trans (mul_le_mul_of_nonneg_right hC₀C hγ0.le)
  · calc C * γ ≤ C * (1 / C) := mul_le_mul_of_nonneg_left hγC hCpos.le
      _ = 1 := by field_simp

/-- **Blueprint Lemma `lem:exponents`, quantitative part.** There are `γ_e ∈ (0, 2)` and `C₁`
such that for `γ ∈ (0, γ_e]`: `γ/3 ≤ ξ_γ ≤ γ`, `ξ_γ ≤ 1/10` and `|ξ_γ Q_γ - 1| ≤ C₁ ξ_γ`. -/
theorem exists_exponents : ∃ γe C₁ : ℝ, 0 < γe ∧ γe < 2 ∧ ∀ γ ∈ Ioc (0 : ℝ) γe,
    γ / 3 ≤ S.ξ γ ∧ S.ξ γ ≤ γ ∧ S.ξ γ ≤ 1 / 10 ∧
      |S.ξ γ * LQGMetric.Q γ - 1| ≤ C₁ * S.ξ γ := by
  obtain ⟨γe, C, hγe, hγe10, hC1, hbd⟩ := S.exists_dim_bound
  refine ⟨γe, 3 * (C + 1), hγe, by linarith, ?_⟩
  intro γ hγmem
  obtain ⟨hξ, hd, hCγ⟩ := hbd γ hγmem
  have hγ0 : 0 < γ := hγmem.1
  have hγ10 : γ ≤ 1 / 10 := hγmem.2.trans hγe10
  set d : ℝ := γ / S.ξ γ with hd_def
  have hdl := neg_abs_le (2 - d)
  have hdu := le_abs_self (2 - d)
  have hd1 : 1 ≤ d := by linarith
  have hd3 : d ≤ 3 := by linarith
  have hdpos : 0 < d := by linarith
  have hξeq : S.ξ γ = γ / d := by
    rw [hd_def, div_div_cancel₀ hγ0.ne']
  have hξle : S.ξ γ ≤ γ := by rw [hξeq]; exact div_le_self hγ0.le hd1
  have hξge : γ / 3 ≤ S.ξ γ := by
    rw [hξeq]; exact div_le_div_of_nonneg_left hγ0.le hdpos hd3
  refine ⟨hξge, hξle, hξle.trans hγ10, ?_⟩
  have hQ : S.ξ γ * LQGMetric.Q γ - 1 = ((2 - d) + γ ^ 2 / 2) / d := by
    rw [hξeq, LQGMetric.Q]
    field_simp
    ring
  have h1 : |(2 - d) + γ ^ 2 / 2| ≤ |2 - d| + γ ^ 2 / 2 := by
    have := abs_add_le (2 - d) (γ ^ 2 / 2)
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2)] at this
  have h2 : γ ^ 2 ≤ γ := by
    rw [pow_two]
    exact mul_le_of_le_one_right hγ0.le (by linarith)
  -- `|ξQ - 1| ≤ (C γ + γ) / d ≤ (C + 1) γ / d = (C + 1) ξ ≤ 3 (C + 1) ξ`
  have h3 : |S.ξ γ * LQGMetric.Q γ - 1| ≤ (C + 1) * S.ξ γ := by
    rw [hQ, abs_div, abs_of_pos hdpos, hξeq, mul_div_assoc', div_le_div_iff_of_pos_right hdpos]
    nlinarith
  calc |S.ξ γ * LQGMetric.Q γ - 1| ≤ (C + 1) * S.ξ γ := h3
    _ ≤ 3 * (C + 1) * S.ξ γ := by nlinarith

/-- **Blueprint Lemma `lem:exponents`**: `ξ_γ / γ → 1/2` as `γ ↓ 0`. -/
theorem tendsto_xi_div_self : Tendsto (fun γ => S.ξ γ / γ) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  obtain ⟨γe, C, hγe, -, hC1, hbd⟩ := S.exists_dim_bound
  -- `|ξ/γ - 1/2| = |2 - d| / (2 d) ≤ C γ`
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), |S.ξ γ / γ - 1 / 2| ≤ C * γ := by
    filter_upwards [Ioc_mem_nhdsGT hγe] with γ hγmem
    obtain ⟨hξ, hd, hCγ⟩ := hbd γ hγmem
    have hγ0 : 0 < γ := hγmem.1
    set d : ℝ := γ / S.ξ γ with hd_def
    have hdl := neg_abs_le (2 - d)
    have hdu := le_abs_self (2 - d)
    have hd1 : 1 ≤ d := by linarith
    have hdpos : 0 < d := by linarith
    have he : S.ξ γ / γ - 1 / 2 = (2 - d) / (2 * d) := by
      rw [hd_def]
      field_simp
    rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * d), div_le_iff₀ (by positivity)]
    nlinarith
  have hlim : Tendsto (fun γ : ℝ => C * γ) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun γ : ℝ => C * γ) (𝓝 0) (𝓝 (C * 0)) := tendsto_id.const_mul C
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hev.mono fun γ hγ => by rw [Real.norm_eq_abs]; exact hγ) hlim

/-- **Blueprint Lemma `lem:exponents`**: `ξ_γ Q_γ → 1` as `γ ↓ 0`. -/
theorem tendsto_xi_mul_Q : Tendsto (fun γ => S.ξ γ * LQGMetric.Q γ) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨γe, C₁, hγe, -, hbd⟩ := S.exists_exponents
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), |S.ξ γ * LQGMetric.Q γ - 1| ≤ |C₁| * γ := by
    filter_upwards [Ioc_mem_nhdsGT hγe] with γ hγmem
    obtain ⟨-, hξle, -, hQ⟩ := hbd γ hγmem
    have hξ0 : 0 ≤ S.ξ γ := (div_nonneg hγmem.1.le (by norm_num : (0 : ℝ) ≤ 3)).trans
      (hbd γ hγmem).1
    calc |S.ξ γ * LQGMetric.Q γ - 1| ≤ C₁ * S.ξ γ := hQ
      _ ≤ |C₁| * S.ξ γ := mul_le_mul_of_nonneg_right (le_abs_self C₁) hξ0
      _ ≤ |C₁| * γ := mul_le_mul_of_nonneg_left hξle (abs_nonneg C₁)
  have hlim : Tendsto (fun γ : ℝ => |C₁| * γ) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun γ : ℝ => |C₁| * γ) (𝓝 0) (𝓝 (|C₁| * 0)) := tendsto_id.const_mul _
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hev.mono fun γ hγ => by rw [Real.norm_eq_abs]; exact hγ) hlim

/-- **Blueprint Lemma `lem:exponents`** (all parts): the bounds of `exists_exponents` together
with `ξ_γ / γ → 1/2` and `ξ_γ Q_γ → 1` as `γ ↓ 0`. -/
theorem exponents :
    (∃ γe C₁ : ℝ, 0 < γe ∧ γe < 2 ∧ ∀ γ ∈ Ioc (0 : ℝ) γe,
      γ / 3 ≤ S.ξ γ ∧ S.ξ γ ≤ γ ∧ S.ξ γ ≤ 1 / 10 ∧
        |S.ξ γ * LQGMetric.Q γ - 1| ≤ C₁ * S.ξ γ) ∧
    Tendsto (fun γ => S.ξ γ / γ) (𝓝[>] 0) (𝓝 (1 / 2)) ∧
    Tendsto (fun γ => S.ξ γ * LQGMetric.Q γ) (𝓝[>] 0) (𝓝 1) :=
  ⟨S.exists_exponents, S.tendsto_xi_div_self, S.tendsto_xi_mul_Q⟩

end Setup

end GaussianLQG

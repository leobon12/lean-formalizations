import HigherDimLQGMetric.Determ.CardLimit
import LQGMetric.Papers.LM.T1_7V19

/-! Conditional variance bound for a metric law with independent cell observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

theorem determ_var_measure (ν : Measure (ContMetric dim)) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ D ∂ν, D.IsLength) (C : ℝ) (hC1 : 1 < C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd dim, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    (z w : Rd dim) (n : ℕ) (hz : ‖z‖ < n) (hw : ‖w‖ < n)
    (hprod : ∀ j : ℕ, ∀ᵐ θ ∂(volume : Measure (Fin dim → ℝ)),
      ν.map (determY (1 / ((j : ℝ) + 1)) θ
        (determFixedBox (d := dim) (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1))) =
      Measure.pi fun k : determFixedBox (d := dim) (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1) =>
        ν.map (determ_enc (determCube (1 / ((j : ℝ) + 1)) θ k))) :
    ∫ D, ((determF (n + 1) z w D).toReal -
      ∫ D', (determF (n + 1) z w D').toReal ∂ν) ^ 2 ∂ν ≤
      C ^ 4 * ∫ D, ((determF n z w D).toReal - (determF (n + 1) z w D).toReal) *
        (determF (n + 1) z w D).toReal ∂ν := by
  have hC0 : 0 < C := zero_lt_one.trans hC1
  set R : ℝ := (n : ℝ) + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  set εj : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hεjdef
  have hεj : ∀ j, 0 < εj j := fun j => by positivity
  have hεj1 : ∀ j, εj j ≤ 1 := fun j => by
    simp only [hεjdef]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hz1 : ‖z‖ < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hw1 : ‖w‖ < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hmR : ((n + 1 : ℕ) : ℝ) ≤ R := by push_cast; rfl
  set F : ContMetric dim → ℝ := fun d => (determF (n + 1) z w d).toReal with hFdef
  set F₀ : ContMetric dim → ℝ := fun d => (determF n z w d).toReal with hF₀def
  have hFm : Measurable F := (determ_measurableF (n + 1) z w).ennreal_toReal
  have hF₀m : Measurable F₀ := (determ_measurableF n z w).ennreal_toReal
  have hF2 := determ_memLp_F ν hL hC0 hcopy hz1 hw1
  -- the data for each mesh
  have hdata := fun j => determ_es_avg ν hL hC0.le hcopy hmR hz1 hw1 (hεj j) (hprod j) hF2
  choose Φ hΦ hΦF K hK hslice hvar using hdata
  set G : ℕ → ContMetric dim → ℝ≥0∞ := fun j d => ∫⁻ θ, determES (εj j) R F (Φ j) ν θ d ∂(determShiftLaw dim)
  have hGm : ∀ j, Measurable (G j) := fun j =>
    (determ_measurable_ES (εj j) R hFm (hΦ j) ν).lintegral_prod_left'
  have hint : ∀ j, ∀ᵐ d ∂ν, ∀ Γ : ℝ, (∀ᵐ θ ∂(volume : Measure (Fin dim → ℝ)), θ ∈ determUnitShift dim → ∃ b : determFixedBox (d := dim) (εj j) R → ℝ, (∀ k, 0 ≤ b k) ∧
          (∀ (k : determFixedBox (d := dim) (εj j) R) (d'' : ContMetric dim),
            DetermCompat C (εj j) θ (determFixedBox (d := dim) (εj j) R) d d'' k.1 →
            max (F d'' - F d) 0 ^ 2 ≤ b k) ∧ ∑ k, b k ≤ Γ) →
      G j d ≤ ENNReal.ofReal Γ := fun j => by
    have := hK j
    exact determ_int_ES_le ν hL hC0.le hcopy hFm (hΦ j) (K j) (hslice j) (hΦF j) (hprod j)
  -- bounds on `F`, `F₀`
  obtain ⟨B, hB⟩ := determ_F_bdd ν hL hC0 hcopy hz1 hw1
  obtain ⟨B₀, hB₀⟩ := determ_F_bdd ν hL hC0 hcopy hz hw
  set B' := (ENNReal.ofReal B).toReal
  set B₀' := (ENNReal.ofReal B₀).toReal
  have hFB : ∀ᵐ d ∂ν, 0 ≤ F d ∧ F d ≤ B' := by
    filter_upwards [hB] with d hd
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono ENNReal.ofReal_ne_top hd.1⟩
  have hF₀B : ∀ᵐ d ∂ν, F d ≤ F₀ d ∧ F₀ d ≤ B₀' := by
    filter_upwards [hB₀, hL] with d hd hdl
    exact ⟨ENNReal.toReal_mono hd.2 (determ_chainInf_succ_le hdl n z w),
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hd.1⟩
  -- domination
  set Kc : ℝ := 2 * R + 2 * Real.sqrt dim + 2
  have hKc0 : 0 ≤ Kc := by dsimp [Kc]; positivity
  set Dc : ℝ := (C ^ 2 - 1) * B' * (C ^ 2 * (B' + 1) + Kc ^ dim)
  have hGD : ∀ j, G j ≤ᵐ[ν] fun _ => ENNReal.ofReal Dc := by
    intro j
    filter_upwards [hint j, hL, hFB] with d hd hdl hdB
    refine (hd _ (determ_perD₂ hdl hC1.le hz hw (hεj j))).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : 0 ≤ C ^ 2 - 1 := by nlinarith
    have he3 : εj j ^ (dim + 1) ≤ 1 := pow_le_one₀ (hεj j).le (hεj1 j)
    have hcard := determ_eps_card_le (d := dim) (hεj j) (hεj1 j) hR0
    have hcard' : εj j * Kc ^ dim ≤ Kc ^ dim := by
      nlinarith [pow_nonneg hKc0 dim, hεj1 j]
    have hb1 : 0 ≤ (C ^ 2 - 1) * F d := mul_nonneg hc hdB.1
    have hb2 : C ^ 2 * (F d + εj j ^ (dim + 1)) + εj j ^ (dim + 1) * (determFixedBox (d := dim) (εj j) R).card ≤
        C ^ 2 * (B' + 1) + Kc ^ dim := by
      have : C ^ 2 * (F d + εj j ^ (dim + 1)) ≤ C ^ 2 * (B' + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hdB.2]) (sq_nonneg C)
      linarith
    have hb3 : 0 ≤ C ^ 2 * (F d + εj j ^ (dim + 1)) + εj j ^ (dim + 1) * (determFixedBox (d := dim) (εj j) R).card := by
      have : 0 ≤ εj j ^ (dim + 1) := by positivity
      positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hdB.2 hc) hb2 hb3
      (mul_nonneg hc (hdB.1.trans hdB.2))
  -- the pointwise limit
  have hε0 : Tendsto εj atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hε3 : Tendsto (fun j => εj j ^ (dim + 1)) atTop (𝓝 0) := by
    simpa using hε0.pow (dim + 1)
  have hcard0 : Tendsto (fun j => εj j ^ (dim + 1) * ((determFixedBox (d := dim) (εj j) R).card : ℝ)) atTop (𝓝 0) := by
    have hup : Tendsto (fun j => εj j * Kc ^ dim) atTop (𝓝 0) := by
      simpa using hε0.mul_const (Kc ^ dim)
    exact squeeze_zero (fun j => by have := hεj j; positivity)
      (fun j => determ_eps_card_le (d := dim) (hεj j) (hεj1 j) hR0) hup
  have hH : ∀ᵐ d ∂ν, limsup (fun j => G j d) atTop ≤
      ENNReal.ofReal (C ^ 4 * ((F₀ d - F d) * F d)) := by
    filter_upwards [ae_all_iff.2 hint, hL] with d hd hdl
    have hκ : ∀ i : ℕ, limsup (fun j => G j d) atTop ≤
        ENNReal.ofReal (C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d)) := by
      intro i
      obtain ⟨ε₀, hε₀, hP⟩ := determ_perD hdl hC1.le hz hw (κ := 1 / ((i : ℝ) + 1)) (by positivity)
      set Γ : ℕ → ℝ := fun j => C ^ 2 * (F₀ d - F d + εj j ^ (dim + 1) + 1 / ((i : ℝ) + 1)) *
        (C ^ 2 * (F d + εj j ^ (dim + 1)) + εj j ^ (dim + 1) * (determFixedBox (d := dim) (εj j) R).card) with hΓdef
      have hΓ : Tendsto Γ atTop
          (𝓝 (C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d))) := by
        have h1 := ((tendsto_const_nhds (x := F₀ d - F d)).add hε3).add
          (tendsto_const_nhds (x := 1 / ((i : ℝ) + 1)))
        have h2 := (tendsto_const_nhds (x := F d)).add hε3
        have := (h1.const_mul (C ^ 2)).mul ((h2.const_mul (C ^ 2)).add hcard0)
        rw [show C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d) =
          C ^ 2 * (F₀ d - F d + 0 + 1 / ((i : ℝ) + 1)) * (C ^ 2 * (F d + 0) + 0) by ring]
        exact this
      have hev : ∀ᶠ j in atTop, G j d ≤ ENNReal.ofReal (Γ j) := by
        have hεe : ∀ᶠ j in atTop, εj j < ε₀ := (tendsto_order.1 hε0).2 ε₀ hε₀
        filter_upwards [hεe] with j hj
        exact hd j _ (hP (εj j) (hεj j) hj)
      calc limsup (fun j => G j d) atTop ≤ limsup (fun j => ENNReal.ofReal (Γ j)) atTop :=
            limsup_le_limsup hev (by isBoundedDefault) (by isBoundedDefault)
        _ = ENNReal.ofReal (C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d)) :=
            ((ENNReal.continuous_ofReal.tendsto _).comp hΓ).limsup_eq
    have hlim : Tendsto (fun i : ℕ =>
        ENNReal.ofReal (C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d))) atTop
        (𝓝 (ENNReal.ofReal (C ^ 4 * ((F₀ d - F d) * F d)))) := by
      have h1 := (tendsto_const_nhds (x := F₀ d - F d)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h2 := (ENNReal.continuous_ofReal.tendsto _).comp
        ((h1.const_mul (C ^ 2)).mul_const (C ^ 2 * F d))
      have e : C ^ 2 * (F₀ d - F d + 0) * (C ^ 2 * F d) = C ^ 4 * ((F₀ d - F d) * F d) := by ring
      rw [e] at h2
      exact h2
    exact ge_of_tendsto' hlim hκ
  -- reverse Fatou and the real form
  have hDfin : ∫⁻ _, ENNReal.ofReal Dc ∂ν ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hmain := LQGMetric.LM.t17v_fatou hGm hDfin hGD hvar hH
  have hbd : ∀ᵐ d ∂ν, 0 ≤ C ^ 4 * ((F₀ d - F d) * F d) ∧
      C ^ 4 * ((F₀ d - F d) * F d) ≤ C ^ 4 * (B₀' * B') := by
    filter_upwards [hFB, hF₀B] with d h1 h2
    have hC4 : 0 ≤ C ^ 4 := by positivity
    refine ⟨mul_nonneg hC4 (mul_nonneg (by linarith) h1.1), mul_le_mul_of_nonneg_left ?_ hC4⟩
    exact mul_le_mul (by linarith) h1.2 h1.1 (by linarith)
  have hI : Integrable (fun d => C ^ 4 * ((F₀ d - F d) * F d)) ν := by
    refine Integrable.of_bound ((measurable_const.mul ((hF₀m.sub hFm).mul hFm)).aestronglyMeasurable)
      (C ^ 4 * (B₀' * B')) ?_
    filter_upwards [hbd] with d hd
    rw [Real.norm_eq_abs, abs_of_nonneg hd.1]
    exact hd.2
  have hnn : 0 ≤ᵐ[ν] fun d => C ^ 4 * ((F₀ d - F d) * F d) := hbd.mono fun d hd => hd.1
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn,
    ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hnn), integral_const_mul] at hmain
  exact hmain


end HigherDimLQGMetric

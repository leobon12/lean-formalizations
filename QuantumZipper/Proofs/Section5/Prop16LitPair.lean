import QuantumZipper.Proofs.Section5.Prop16LitChart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: comparison of area pairings through the chart

`LitChart.pair_close` (deterministic): if the area measure `ν` of the field read through the
chart `ψ` is the pull-back of the area measure `μ` of the straight zoom (`ψ_* ν = μ|_{ψ(U)}`,
conformal covariance, Duplantier–Sheffield arXiv:0808.1560 Prop. 2.1), then for a test function
`f` supported in `B(0,R)` and scales `a` (straight) and `b` (through the chart),

  `|∫ f(z/b) dν(z) − ∫ f(w/a) dμ(w)| ≤ ε · ν(K)`,

provided that, on the region where one of the two integrands is nonzero, `z/b` and `ψ(z)/a` are
`τ`-close (`τ` a modulus of uniform continuity of `f` at level `ε`) and `z ∈ K`. The geometric
input is supplied by `LitChart.scale_bounds` and the first-order expansion of `ψ` at `0`.
Own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open Filter Set Metric MeasureTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace LitChart

/-- **Pairing comparison through the chart.** -/
theorem pair_close {μ ν : Measure ℂ} {ψ : ℂ → ℂ} {f : ℂ → ℝ} {U S K : Set ℂ}
    {a b R τ ε Mf : ℝ} (ha : 0 < a) (hb : 0 < b) (hf : Continuous f)
    (hfM : ∀ u, |f u| ≤ Mf) (hfR : ∀ u, R ≤ ‖u‖ → f u = 0)
    (hfτ : ∀ u v, ‖u - v‖ < τ → |f u - f v| ≤ ε) (hε : 0 ≤ ε)
    (hψ : Measurable ψ) (hmap : ν.map ψ = μ.restrict S)
    (hνU : ∀ᵐ z ∂ν, z ∈ U) (hμH : ∀ᵐ w ∂μ, w ∈ H) (hS : ball 0 (R * a) ∩ H ⊆ S)
    (hK : MeasurableSet K) (hKν : ν K < ⊤)
    (hgeom : ∀ z ∈ U, (‖z / b‖ < R ∨ ‖ψ z / a‖ < R) → ‖z / b - ψ z / a‖ < τ ∧ z ∈ K) :
    |∫ z, f (z / b) ∂ν - ∫ w, f (w / a) ∂μ| ≤ ε * (ν K).toReal := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hfa : Continuous fun w : ℂ => f (w / a) := hf.comp (continuous_id.div_const _)
  have hfb : Continuous fun w : ℂ => f (w / b) := hf.comp (continuous_id.div_const _)
  -- nonvanishing forces the point into the ball
  have hnz : ∀ (u : ℂ) (c : ℝ), 0 < c → f (u / c) ≠ 0 → ‖u / c‖ < R := by
    intro u c _ h
    by_contra hle
    exact h (hfR _ (not_lt.1 hle))
  -- step 1: move the straight pairing to `ν`
  have h1 : ∫ w, f (w / a) ∂μ = ∫ z, f (ψ z / a) ∂ν := by
    have e1 : ∫ w, f (w / a) ∂μ = ∫ w in S, f (w / a) ∂μ := by
      refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
      filter_upwards [hμH] with w hwH hwS
      by_contra hne
      have hlt := hnz w a ha hne
      apply hwS
      refine hS ⟨?_, hwH⟩
      rw [mem_ball, dist_zero_right]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, div_lt_iff₀ ha] at hlt
      linarith
    rw [e1, ← hmap, integral_map hψ.aemeasurable hfa.aestronglyMeasurable]
  rw [h1]
  -- step 2: integrability, dominated by `Mf · 1_K`
  have hdomK : Integrable (K.indicator fun _ => Mf) ν :=
    (integrable_indicator_iff hK).2 (integrableOn_const (hs := hKν.ne))
  have hI1 : Integrable (fun z => f (z / b)) ν := by
    refine Integrable.mono' hdomK hfb.aestronglyMeasurable ?_
    filter_upwards [hνU] with z hz
    by_cases h0 : f (z / b) = 0
    · rw [h0, norm_zero]
      by_cases hzK : z ∈ K
      · rw [indicator_of_mem hzK]; exact (abs_nonneg _).trans (hfM 0)
      · rw [indicator_of_notMem hzK]
    · have hzK := (hgeom z hz (Or.inl (hnz z b hb h0))).2
      rw [indicator_of_mem hzK, Real.norm_eq_abs]; exact hfM _
  have hI2 : Integrable (fun z => f (ψ z / a)) ν := by
    refine Integrable.mono' hdomK (hfa.measurable.comp hψ).aestronglyMeasurable ?_
    filter_upwards [hνU] with z hz
    by_cases h0 : f (ψ z / a) = 0
    · rw [h0, norm_zero]
      by_cases hzK : z ∈ K
      · rw [indicator_of_mem hzK]; exact (abs_nonneg _).trans (hfM 0)
      · rw [indicator_of_notMem hzK]
    · have hzK := (hgeom z hz (Or.inr (hnz (ψ z) a ha h0))).2
      rw [indicator_of_mem hzK, Real.norm_eq_abs]; exact hfM _
  -- step 3: the pointwise bound
  rw [← integral_sub hI1 hI2]
  have hdom : Integrable (K.indicator fun _ => ε) ν :=
    (integrable_indicator_iff hK).2 (integrableOn_const (hs := hKν.ne))
  have hbd : ∀ᵐ z ∂ν, ‖f (z / b) - f (ψ z / a)‖ ≤ K.indicator (fun _ => ε) z := by
    filter_upwards [hνU] with z hz
    by_cases h0 : f (z / b) = 0 ∧ f (ψ z / a) = 0
    · rw [h0.1, h0.2, sub_zero, norm_zero]
      by_cases hzK : z ∈ K
      · rw [indicator_of_mem hzK]; exact hε
      · rw [indicator_of_notMem hzK]
    · have hor : ‖z / b‖ < R ∨ ‖ψ z / a‖ < R := by
        rcases not_and_or.1 h0 with h | h
        · exact Or.inl (hnz z b hb h)
        · exact Or.inr (hnz (ψ z) a ha h)
      obtain ⟨hτ, hzK⟩ := hgeom z hz hor
      rw [indicator_of_mem hzK, Real.norm_eq_abs]
      exact hfτ _ _ hτ
  have := norm_integral_le_of_norm_le hdom hbd
  rw [integral_indicator hK, setIntegral_const, smul_eq_mul, Real.norm_eq_abs] at this
  rw [measureReal_def] at this
  linarith

end LitChart

end QuantumZipper

import QuantumZipper.Proofs.Section5.Prop16LitPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the pointwise comparison at small scale

`LitChart.pointwise_close` (deterministic): fix a chart `ψ` (strict complex derivative `κ > 0`
at `0`, `ψ 0 = 0`, real on a real segment around `0`, injective on `ℍ`, mapping `ℍ` into `ℍ`)
and a continuous compactly supported test function `f` vanishing off `B(0, R_f)`. For every
`ε₀ > 0` there is `δ > 0` (with `R = 4 R_f`)
such that for all measures `μ` (straight area measure, carried by `ℍ`) and `ν` (area measure
read through the chart, carried by `B(0,r₁) ∩ ℍ`) related by conformal covariance
`ψ_* ν = μ|_{ψ(B(0,r₁) ∩ ℍ)}`, if the (1.8)-scale `a` of `μ` lies in `(0, δ)`, then the scale `b`
of `ν` is positive and

  `|∫ f(z/b) dν(z) − ∫ f(w/a) dμ(w)| ≤ ε₀ · μ(B(0, R a) ∩ ℍ)`.

With the rescaling rule `μ_can = (·/a)_* μ`, the right side is `ε₀ · μ_can(B(0,R) ∩ ℍ)`: the
chart only changes the canonical area pairings by a small multiple of the canonical mass of a
fixed ball, because to first order at `0` it is the dilation by `κ`, which (1.8) absorbs.
Own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open Filter Set Metric MeasureTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace LitChart

/-- **Pointwise comparison of canonical pairings at small scale.** -/
theorem pointwise_close {ψ : ℂ → ℂ} {κ r r₁ : ℝ} (hκ : 0 < κ)
    (hψ : HasStrictDerivAt ψ (κ : ℂ) 0) (hψ0 : ψ 0 = 0) (hr : 0 < r)
    (hreal : ∀ t : ℝ, |t| < r → (ψ t).im = 0) (hψm : Measurable ψ) (hinj : InjOn ψ H)
    (hψH : ∀ z ∈ H, ψ z ∈ H) (hr₁ : 0 < r₁) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) {Rf : ℝ} (hRf1 : 1 ≤ Rf) (hfR : ∀ u : ℂ, Rf ≤ ‖u‖ → f u = 0)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ δ > 0, ∀ μ ν : Measure ℂ,
      ν.map ψ = μ.restrict (ψ '' (ball 0 r₁ ∩ H)) → (∀ᵐ z ∂ν, z ∈ ball 0 r₁ ∩ H) →
      (∀ᵐ w ∂μ, w ∈ H) → 0 < scaleOf μ → scaleOf μ < δ →
      μ (ball 0 (4 * Rf * scaleOf μ) ∩ H) < ⊤ →
      0 < scaleOf ν ∧ |∫ z, f (z / scaleOf ν) ∂ν - ∫ w, f (w / scaleOf μ) ∂μ| ≤
        ε₀ * (μ (ball 0 (4 * Rf * scaleOf μ) ∩ H)).toReal := by
  have hRf0 : 0 < Rf := by linarith
  obtain ⟨Mf, hMf⟩ := hf.bounded_above_of_compact_support hfs
  have hfM : ∀ u, |f u| ≤ Mf := fun u => by simpa [Real.norm_eq_abs] using hMf u
  obtain ⟨τ, hτ, hτf⟩ := Metric.uniformContinuous_iff.1
    (hfs.uniformContinuous_of_continuous hf) ε₀ hε₀
  have hfτ : ∀ u v : ℂ, ‖u - v‖ < τ → |f u - f v| ≤ ε₀ := fun u v h => by
    have := hτf (show dist u v < τ by rwa [dist_eq_norm])
    rw [Real.dist_eq] at this; exact this.le
  -- precision `ε`
  set ε := min (1 / 3) (τ / (16 * Rf)) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε3 : ε ≤ 1 / 3 := min_le_left _ _
  have hετ : 16 * Rf * ε ≤ τ := by
    have := min_le_right (1 / 3 : ℝ) (τ / (16 * Rf))
    rw [← hεdef] at this
    rw [le_div_iff₀ (by positivity)] at this; linarith
  -- chart radii
  obtain ⟨δl, hδl, hlin⟩ := strict_bound hψ (show 0 < ε * κ by positivity)
  obtain ⟨δi, hδi, himg⟩ := image_subset hκ hψ hψ0 hr hreal hε
  obtain ⟨δs, hδs, hsub⟩ := subset_image hκ hψ hψ0 hr hreal hε
  set ρ₁ := min (min δi δs) (min r₁ δl) with hρ₁
  have hρ₁0 : 0 < ρ₁ := lt_min (lt_min hδi hδs) (lt_min hr₁ hδl)
  have hρi : ρ₁ ≤ δi := (min_le_left _ _).trans (min_le_left _ _)
  have hρs : ρ₁ ≤ δs := (min_le_left _ _).trans (min_le_right _ _)
  have hρr : ρ₁ ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hρl : ρ₁ ≤ δl := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨κ * ρ₁ / (4 * Rf + 4), by positivity, ?_⟩
  intro μ ν hmap hνU hμH ha0 haδ hfin
  set a := scaleOf μ with ha
  set U := ball (0 : ℂ) r₁ ∩ H with hU
  set S := ψ '' U with hS
  set c₁ := (1 - ε) * κ with hc₁
  set c₂ := (1 + ε) * κ with hc₂
  have hc₁0 : 0 < c₁ := by rw [hc₁]; have : 0 < 1 - ε := by linarith
                           positivity
  have hc₁₂ : c₁ ≤ c₂ := by rw [hc₁, hc₂]; linarith [mul_nonneg hε.le hκ.le]
  have hc₁κ : 2 * κ / 3 ≤ c₁ := by
    rw [hc₁]; linarith [mul_le_mul_of_nonneg_right hε3 hκ.le]
  have hc₂c₁ : c₂ ≤ 2 * c₁ := by
    rw [hc₂, hc₁]; linarith [mul_le_mul_of_nonneg_right hε3 hκ.le]
  have hmeasB : ∀ t : ℝ, MeasurableSet (ball (0 : ℂ) t ∩ H) := fun t =>
    measurableSet_ball.inter (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  -- key sizes
  have ha_small : 3 * Rf * a / κ < ρ₁ := by
    rw [div_lt_iff₀ hκ]
    have h1 : a < κ * ρ₁ / (4 * Rf + 4) := haδ
    rw [lt_div_iff₀ (by positivity)] at h1
    linarith [mul_pos ha0 hRf0]
  -- `hlow`, `hup`
  have hlow : ∀ s, 0 < s → s ≤ ρ₁ → μ (ball 0 (c₁ * s) ∩ H) ≤ ν (ball 0 s ∩ H) := by
    intro s hs hsρ
    have hsubS : ball 0 (c₁ * s) ∩ H ⊆ S := (hsub s hs (hsρ.trans hρs)).trans
      (image_mono (inter_subset_inter_left _ (ball_subset_ball (hsρ.trans hρr))))
    calc μ (ball 0 (c₁ * s) ∩ H) = μ.restrict S (ball 0 (c₁ * s) ∩ H) := by
          rw [Measure.restrict_apply (hmeasB _), inter_eq_left.2 hsubS]
      _ = ν (ψ ⁻¹' (ball 0 (c₁ * s) ∩ H)) := by rw [← hmap, Measure.map_apply hψm (hmeasB _)]
      _ ≤ ν (ball 0 s ∩ H) := by
          refine measure_mono_ae ?_
          filter_upwards [hνU] with z hz hzpre
          obtain ⟨z', hz', hψz'⟩ := hsub s hs (hsρ.trans hρs) hzpre
          have : z' = z := hinj hz'.2 hz.2 hψz'
          rw [← this]; exact hz'
  have hup : ∀ s, 0 < s → s ≤ ρ₁ → ν (ball 0 s ∩ H) ≤ μ (ball 0 (c₂ * s) ∩ H) := by
    intro s hs hsρ
    calc ν (ball 0 s ∩ H) ≤ ν (ψ ⁻¹' (ball 0 (c₂ * s) ∩ H)) :=
          measure_mono fun z hz => himg s hs (hsρ.trans hρi) ⟨z, hz, rfl⟩
      _ = μ.restrict S (ball 0 (c₂ * s) ∩ H) := by
          rw [← hmap, Measure.map_apply hψm (hmeasB _)]
      _ ≤ μ (ball 0 (c₂ * s) ∩ H) := Measure.restrict_apply_le _ _
  -- the scales
  have hac₁ : a < c₁ * ρ₁ := by
    have : a < κ * ρ₁ / 4 := by
      have h1 : κ * ρ₁ / (4 * Rf + 4) ≤ κ * ρ₁ / 4 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      linarith
    linarith [mul_le_mul_of_nonneg_right hc₁κ hρ₁0.le, mul_pos hκ hρ₁0]
  obtain ⟨hb1, hb2⟩ := scale_bounds hc₁0 hc₁₂ hlow hup ha0 hac₁
  set b := scaleOf ν with hb
  have hb0 : 0 < b := lt_of_lt_of_le (div_pos ha0 (hc₁0.trans_le hc₁₂)) hb1
  -- consequences: `a ≤ c₂ b`, `c₁ b ≤ a`
  have hab1 : a ≤ c₂ * b := by
    rw [div_le_iff₀ (hc₁0.trans_le hc₁₂)] at hb1; linarith
  have hab2 : c₁ * b ≤ a := by
    rw [le_div_iff₀ hc₁0] at hb2; linarith
  have hbκ : κ * b ≤ 3 * a / 2 := by
    have : 2 * κ / 3 * b ≤ c₁ * b := mul_le_mul_of_nonneg_right hc₁κ hb0.le
    linarith
  have hb_small : 2 * Rf * b < ρ₁ := by
    have h1 : 2 * Rf * b ≤ 3 * Rf * a / κ := by
      rw [le_div_iff₀ hκ]
      linarith [mul_le_mul_of_nonneg_left hbκ (show (0 : ℝ) ≤ 2 * Rf by positivity)]
    linarith
  -- `hS` for `pair_close`
  set s₁ := Rf * a / c₁ with hs₁
  have hs₁0 : 0 < s₁ := by positivity
  have hs₁ρ : s₁ ≤ ρ₁ := by
    have h1 : s₁ ≤ 3 * Rf * a / (2 * κ) := by
      rw [hs₁, div_le_div_iff₀ hc₁0 (by positivity)]
      linarith [mul_le_mul_of_nonneg_left hc₁κ (show (0 : ℝ) ≤ Rf * a by positivity)]
    have h2 : 3 * Rf * a / (2 * κ) ≤ 3 * Rf * a / κ :=
      div_le_div_of_nonneg_left (by positivity) hκ (by linarith)
    linarith
  have hc₁s₁ : c₁ * s₁ = Rf * a := by rw [hs₁]; field_simp
  have hSin : ball 0 (Rf * a) ∩ H ⊆ S := by
    rw [← hc₁s₁]
    exact (hsub s₁ hs₁0 (hs₁ρ.trans hρs)).trans
      (image_mono (inter_subset_inter_left _ (ball_subset_ball (hs₁ρ.trans hρr))))
  -- the geometric input
  set K := ball (0 : ℂ) (2 * Rf * b) ∩ H with hK
  have hgeom : ∀ z ∈ U, (‖z / b‖ < Rf ∨ ‖ψ z / a‖ < Rf) →
      ‖z / b - ψ z / a‖ < τ ∧ z ∈ K := by
    intro z hz hor
    have hzH : z ∈ H := hz.2
    have hzs : ‖z‖ < 2 * Rf * b := by
      rcases hor with h | h
      · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hb0.le, div_lt_iff₀ hb0] at h
        linarith [mul_pos hRf0 hb0]
      · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha0.le, div_lt_iff₀ ha0] at h
        have hmem : ψ z ∈ ball 0 (c₁ * s₁) ∩ H := by
          refine ⟨?_, hψH z hzH⟩
          rw [mem_ball, dist_zero_right, hc₁s₁]; linarith
        obtain ⟨z', hz', hψz'⟩ := hsub s₁ hs₁0 (hs₁ρ.trans hρs) hmem
        have hzz : z' = z := hinj hz'.2 hzH hψz'
        rw [← hzz]
        have h1 : ‖z'‖ < s₁ := by simpa [mem_ball, dist_zero_right] using hz'.1
        have h2 : s₁ ≤ 2 * Rf * b := by
          rw [hs₁, div_le_iff₀ hc₁0]
          have h3 : a ≤ 2 * c₁ * b := by
            linarith [mul_le_mul_of_nonneg_right hc₂c₁ hb0.le]
          calc Rf * a ≤ Rf * (2 * c₁ * b) := mul_le_mul_of_nonneg_left h3 hRf0.le
            _ = 2 * Rf * b * c₁ := by ring
        linarith
    refine ⟨?_, ⟨by rwa [mem_ball, dist_zero_right], hzH⟩⟩
    -- the estimate
    have hzl : ‖z‖ < δl := by linarith
    have hl := hlin z 0 hzl (by simpa using hδl)
    simp only [hψ0, sub_zero] at hl
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
    have hid : z / b - ψ z / a =
        (((a - κ * b : ℝ) : ℂ) * z + (b : ℂ) * ((κ : ℂ) * z - ψ z)) / ((a : ℂ) * b) := by
      field_simp; push_cast; ring
    have hdiff : |a - κ * b| ≤ 2 * ε * a := by
      rw [abs_le]; constructor
      · have h1 : (1 - ε) * (κ * b) ≤ a := by
          have := hab2; rw [hc₁] at this; linarith
        linarith [mul_le_mul_of_nonneg_left hbκ hε.le]
      · have h1 : a ≤ (1 + ε) * (κ * b) := by
          have := hab1; rw [hc₂] at this; linarith
        linarith [mul_le_mul_of_nonneg_left hbκ hε.le]
    have hnum : ‖((a - κ * b : ℝ) : ℂ) * z + (b : ℂ) * ((κ : ℂ) * z - ψ z)‖ ≤
        2 * ε * a * ‖z‖ + b * (ε * κ * ‖z‖) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left hl hb0.le
    rw [hid, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ha0.le, Real.norm_of_nonneg hb0.le, div_lt_iff₀ (by positivity)]
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    -- `2εa‖z‖ + bεκ‖z‖ < τ a b`
    have e1 : 2 * ε * a * ‖z‖ ≤ 2 * ε * a * (2 * Rf * b) :=
      mul_le_mul_of_nonneg_left hzs.le (by positivity)
    have e2 : b * (ε * κ * ‖z‖) ≤ ε * (κ * b) * (2 * Rf * b) := by
      have : b * (ε * κ * ‖z‖) = ε * (κ * b) * ‖z‖ := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hzs.le (by positivity)
    have e3 : ε * (κ * b) * (2 * Rf * b) ≤ ε * (3 * a / 2) * (2 * Rf * b) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hbκ hε.le
    have e4 : 2 * ε * a * (2 * Rf * b) + ε * (3 * a / 2) * (2 * Rf * b) =
        7 * Rf * ε * (a * b) := by ring
    have e5 : 7 * Rf * ε * (a * b) < τ * (a * b) := by
      have hab : 0 < a * b := mul_pos ha0 hb0
      have : 7 * Rf * ε < τ := by linarith [mul_pos hRf0 hε]
      exact mul_lt_mul_of_pos_right this hab
    linarith
  -- the mass of `K`
  have hKμ : ν K ≤ μ (ball 0 (4 * Rf * a) ∩ H) := by
    refine (hup (2 * Rf * b) (by positivity) hb_small.le).trans (measure_mono ?_)
    refine inter_subset_inter_left _ (ball_subset_ball ?_)
    have h4 : c₂ * b ≤ 2 * a := by
      linarith [mul_le_mul_of_nonneg_right hc₂c₁ hb0.le]
    linarith [mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ 2 * Rf by positivity)]
  have hKfin : ν K < ⊤ := hKμ.trans_lt hfin
  refine ⟨hb0, ?_⟩
  have key := pair_close ha0 hb0 hf hfM hfR hfτ hε₀.le hψm hmap hνU hμH hSin (hmeasB _) hKfin hgeom
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hε₀.le)
  exact ENNReal.toReal_mono hfin.ne hKμ

end LitChart

end QuantumZipper

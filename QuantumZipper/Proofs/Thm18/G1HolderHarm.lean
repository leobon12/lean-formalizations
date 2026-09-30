import QuantumZipper.Common.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-HOLDER step 2: boundary Lipschitz bound for a harmonic function vanishing on a segment

`im_le_mul_im_of_tendsto_zero`: if `g` is holomorphic on the half-disc `ℍ ∩ B(0, ρ)`,
`Im g ≤ M` there, and `Im g(z) → 0` as `z → t` for every real `|t| < ρ`, then
`Im g(z) ≤ K Im z` on `ℍ ∩ B̄(0, ρ/4)`.

**Own elementary argument** (standard harmonic-majorant argument, cf. Garnett–Marshall,
*Harmonic Measure*, Ch. I, maximum principle and harmonic measure of boundary arcs).
Instead of the harmonic measure of the arc of a half-disc we use the explicit rational
majorant on the rectangle `R = {|Re w| < a, 0 < Im w < a}`, `a = ρ/3`:
`Φ(w) = a/(a − w) − a/(w + a) + w/a`, whose imaginary part
`h(w) = a Im w/|a − w|² + a Im w/|w + a|² + Im w/a` is `≥ 0` on `ℍ`, `≥ 1` on the top and
the vertical sides of `R`, and `≤ (33/a) Im w` for `|Re w| ≤ 3a/4`.
By compactness of `[−a, a]`, `Im g < δ` on `{|Re w| ≤ a, 0 < Im w < ε₀}`; the maximum
modulus principle (mathlib `Complex.norm_le_of_forall_mem_frontier_norm_le`) applied to
`exp(−i (g − M' Φ))` on `{ε < Im w < a, |Re w| < a}` gives `Im g ≤ M' h + δ`, and `δ → 0`.
No positivity of `Im g` is needed.
-/

namespace QuantumZipper.Thm18Asm.G1RC

open Complex Metric Set Filter Topology

/-- The rational harmonic majorant on the rectangle `{|Re w| < a, 0 < Im w < a}`. -/
noncomputable def g1hPhi (a : ℝ) (w : ℂ) : ℂ :=
  (a : ℂ) / ((a : ℂ) - w) - (a : ℂ) / (w + (a : ℂ)) + ((a⁻¹ : ℝ) : ℂ) * w

/-- Imaginary part of `g1hPhi`. -/
noncomputable def g1hH (a : ℝ) (w : ℂ) : ℝ :=
  a * w.im / normSq ((a : ℂ) - w) + a * w.im / normSq (w + (a : ℂ)) + a⁻¹ * w.im

lemma g1hPhi_im (a : ℝ) (w : ℂ) : (g1hPhi a w).im = g1hH a w := by
  simp only [g1hPhi, g1hH, add_im, sub_im, div_im, ofReal_re, ofReal_im, im_ofReal_mul, sub_re,
    add_re]
  ring

lemma g1hH_nonneg {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 ≤ w.im) : 0 ≤ g1hH a w := by
  unfold g1hH
  have h1 : 0 ≤ a * w.im := mul_nonneg ha.le hw
  have h2 : 0 ≤ a⁻¹ * w.im := mul_nonneg (inv_nonneg.2 ha.le) hw
  have h3 := div_nonneg h1 (normSq_nonneg ((a : ℂ) - w))
  have h4 := div_nonneg h1 (normSq_nonneg (w + (a : ℂ)))
  linarith

lemma g1hH_one_le {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 < w.im) (h2 : w.im ≤ a)
    (hside : w.im = a ∨ |w.re| = a) : 1 ≤ g1hH a w := by
  unfold g1hH
  have h1 : 0 ≤ a * w.im := mul_nonneg ha.le hw.le
  have h3 := div_nonneg h1 (normSq_nonneg ((a : ℂ) - w))
  have h4 := div_nonneg h1 (normSq_nonneg (w + (a : ℂ)))
  have h5 : 0 ≤ a⁻¹ * w.im := mul_nonneg (inv_nonneg.2 ha.le) hw.le
  have key : ∀ N : ℝ, N = w.im ^ 2 → 1 ≤ a * w.im / N := by
    intro N hN
    subst hN
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rcases hside with h | h
  · have : a⁻¹ * w.im = 1 := by rw [h]; exact inv_mul_cancel₀ ha.ne'
    linarith
  · rcases abs_eq ha.le |>.1 h with h' | h'
    · have := key (normSq ((a : ℂ) - w)) (by simp [normSq_apply, h']; ring)
      linarith
    · have := key (normSq (w + (a : ℂ))) (by simp [normSq_apply, h']; ring)
      linarith

lemma g1hH_le {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) (hre : |z.re| ≤ 3 * a / 4) :
    g1hH a z ≤ 33 / a * z.im := by
  unfold g1hH
  have hre' := abs_le.1 hre
  have h1 : 0 ≤ a * z.im := mul_nonneg ha.le hz.le
  have hN1 : a ^ 2 / 16 ≤ normSq ((a : ℂ) - z) := by
    simp only [normSq_apply, sub_re, ofReal_re, sub_im, ofReal_im]
    nlinarith [mul_self_nonneg z.im]
  have hN2 : a ^ 2 / 16 ≤ normSq (z + (a : ℂ)) := by
    simp only [normSq_apply, add_re, ofReal_re, add_im, ofReal_im]
    nlinarith [mul_self_nonneg z.im]
  have hpos : 0 < a ^ 2 / 16 := by positivity
  have e1 := div_le_div_of_nonneg_left h1 hpos hN1
  have e2 := div_le_div_of_nonneg_left h1 hpos hN2
  have e3 : a * z.im / (a ^ 2 / 16) = 16 / a * z.im := by field_simp
  have e4 : 33 / a * z.im = 16 / a * z.im + 16 / a * z.im + a⁻¹ * z.im := by
    field_simp; ring
  rw [e4]
  linarith

/-- Uniform smallness of `Im g` near the segment `[-b, b]`, by compactness. -/
lemma g1h_unif_small {g : ℂ → ℂ} {ρ b δ : ℝ} (hbρ : b < ρ)
    (hbd : ∀ t : ℝ, |t| < ρ → Tendsto (fun z => (g z).im) (𝓝[H] (t : ℂ)) (𝓝 0))
    (hδ : 0 < δ) :
    ∃ ε₀ > 0, ∀ w : ℂ, 0 < w.im → |w.re| ≤ b → w.im < ε₀ → (g w).im < δ := by
  set S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc (-b) b with hSdef
  have hS : IsCompact S := isCompact_Icc.image continuous_ofReal
  have key : {w : ℂ | w ∈ H → (g w).im < δ} ∈ 𝓝ˢ S := by
    rw [mem_nhdsSet_iff_forall]
    rintro _ ⟨t, ht, rfl⟩
    have htρ : |t| < ρ := (abs_le.2 ht).trans_lt hbρ
    exact mem_nhdsWithin_iff_eventually.1 (hbd t htρ (Iio_mem_nhds hδ))
  obtain ⟨U, hUo, hSU, hUs⟩ := mem_nhdsSet_iff_exists.1 key
  obtain ⟨ε₀, hε₀, hth⟩ := hS.exists_thickening_subset_open hUo hSU
  refine ⟨ε₀, hε₀, fun w hw hre him => ?_⟩
  have hwth : w ∈ thickening ε₀ S := by
    rw [mem_thickening_iff]
    refine ⟨(w.re : ℂ), ⟨w.re, abs_le.1 hre, rfl⟩, ?_⟩
    rw [dist_of_re_eq (by simp), Real.dist_eq]
    simp only [ofReal_im, sub_zero, abs_of_pos hw]
    exact him
  exact hUs (hth hwth) hw

/-- **Boundary Lipschitz bound** (own elementary argument; see the module docstring). -/
theorem im_le_mul_im_of_tendsto_zero {g : ℂ → ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ g (H ∩ Metric.ball (0 : ℂ) ρ))
    (hM : ∀ z ∈ H ∩ Metric.ball (0 : ℂ) ρ, (g z).im ≤ M)
    (hbd : ∀ t : ℝ, |t| < ρ → Filter.Tendsto (fun z => (g z).im) (nhdsWithin (t : ℂ) H)
      (nhds 0)) :
    ∃ K : ℝ, ∀ z ∈ H, ‖z‖ ≤ ρ / 4 → (g z).im ≤ K * z.im := by
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set a := ρ / 3 with ha_def
  have ha : 0 < a := by positivity
  have hball : ∀ w : ℂ, 0 < w.im → w.im ≤ a → |w.re| ≤ a → w ∈ H ∩ ball (0 : ℂ) ρ := by
    intro w hw h1 h2
    refine ⟨hw, ?_⟩
    rw [mem_ball_zero_iff]
    calc ‖w‖ ≤ |w.re| + |w.im| := norm_le_abs_re_add_abs_im w
      _ < ρ := by rw [abs_of_pos hw]; linarith
  have hmain : ∀ z : ℂ, 0 < z.im → |z.re| < a → z.im < a → (g z).im ≤ M' * g1hH a z := by
    intro z hz hre him
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨ε₀, hε₀, hsmall⟩ := g1h_unif_small (b := a) (by linarith) hbd hδ
    set ε := min ε₀ z.im / 2 with hε_def
    have hmin : 0 < min ε₀ z.im := lt_min hε₀ hz
    have hε : 0 < ε := by positivity
    have hεε₀ : ε < ε₀ := by have := min_le_left ε₀ z.im; linarith
    have hεz : ε < z.im := by have := min_le_right ε₀ z.im; linarith
    set U : Set ℂ := {w | ε < w.im ∧ w.im < a ∧ |w.re| < a} with hU_def
    have hUo : IsOpen U :=
      (isOpen_lt continuous_const continuous_im).inter
        ((isOpen_lt continuous_im continuous_const).inter
          (isOpen_lt (continuous_abs.comp continuous_re) continuous_const))
    have hUcl : closure U ⊆ {w | ε ≤ w.im ∧ w.im ≤ a ∧ |w.re| ≤ a} :=
      closure_minimal (fun w hw => ⟨hw.1.le, hw.2.1.le, hw.2.2.le⟩)
        ((isClosed_le continuous_const continuous_im).inter
          ((isClosed_le continuous_im continuous_const).inter
            (isClosed_le (continuous_abs.comp continuous_re) continuous_const)))
    have hclH : ∀ w ∈ closure U, w ∈ H ∩ ball (0 : ℂ) ρ := fun w hw =>
      let h := hUcl hw; hball w (hε.trans_le h.1) h.2.1 h.2.2
    have hΦd : DifferentiableOn ℂ (g1hPhi a) (closure U) := by
      intro w hw
      have hwim : 0 < w.im := hε.trans_le (hUcl hw).1
      have n1 : (a : ℂ) - w ≠ 0 := by
        intro h0; have := congrArg im h0; simp at this; linarith
      have n2 : w + (a : ℂ) ≠ 0 := by
        intro h0; have := congrArg im h0; simp at this; linarith
      refine DifferentiableAt.differentiableWithinAt ?_
      unfold g1hPhi
      exact ((differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id)
        n1 |>.sub ((differentiableAt_const _).div (differentiableAt_id.add
          (differentiableAt_const _)) n2)).add ((differentiableAt_const _).mul differentiableAt_id)
    have hgd : DifferentiableOn ℂ g (closure U) := hd.mono hclH
    set F : ℂ → ℂ := fun w => Complex.exp (-I * (g w - (M' : ℂ) * g1hPhi a w)) with hF_def
    have hFd : DifferentiableOn ℂ F (closure U) :=
      ((hgd.sub (hΦd.const_mul (M' : ℂ))).const_mul (-I)).cexp
    have hFn : ∀ w, ‖F w‖ = Real.exp ((g w).im - M' * g1hH a w) := by
      intro w
      simp only [hF_def, norm_exp, ← g1hPhi_im]
      congr 1
      simp [mul_re, mul_im, sub_re, sub_im]
    have hfr : ∀ w ∈ frontier U, ‖F w‖ ≤ Real.exp δ := by
      intro w hw
      rw [hFn, Real.exp_le_exp]
      have hwcl := hUcl (frontier_subset_closure hw)
      have hwU : w ∉ U := by rw [hUo.frontier_eq] at hw; exact hw.2
      obtain ⟨h1, h2, h3⟩ := hwcl
      have hwim : 0 < w.im := hε.trans_le h1
      have hH0 : 0 ≤ M' * g1hH a w := mul_nonneg hM'0 (g1hH_nonneg ha hwim.le)
      by_cases hb : w.im = ε
      · have := hsmall w hwim h3 (by rw [hb]; exact hεε₀)
        linarith
      · have hside : w.im = a ∨ |w.re| = a := by
          by_contra hc
          push Not at hc
          exact hwU ⟨lt_of_le_of_ne h1 (Ne.symm hb), lt_of_le_of_ne h2 hc.1,
            lt_of_le_of_ne h3 hc.2⟩
        have h1' : 1 ≤ g1hH a w := g1hH_one_le ha hwim h2 hside
        have hgM := hM w (hball w hwim h2 h3)
        have : M' * 1 ≤ M' * g1hH a w := mul_le_mul_of_nonneg_left h1' hM'0
        have := le_max_left M 0
        linarith
    have hzU : z ∈ U := ⟨hεz, him, hre⟩
    have hbdd : Bornology.IsBounded U :=
      isBounded_ball.subset fun w hw => (hball w (hε.trans hw.1) hw.2.1.le hw.2.2.le).2
    have := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hFd.diffContOnCl hfr
      (subset_closure hzU)
    rw [hFn, Real.exp_le_exp] at this
    linarith
  refine ⟨M' * (33 / a), fun z hz hzn => ?_⟩
  have hz' : 0 < z.im := hz
  have hre : |z.re| ≤ ρ / 4 := (abs_re_le_norm z).trans hzn
  have him : z.im ≤ ρ / 4 := (le_abs_self _).trans ((abs_im_le_norm z).trans hzn)
  have h1 := hmain z hz' (by linarith) (by linarith)
  have h2 : g1hH a z ≤ 33 / a * z.im := g1hH_le ha hz' (by rw [ha_def]; linarith)
  calc (g z).im ≤ M' * g1hH a z := h1
    _ ≤ M' * (33 / a * z.im) := mul_le_mul_of_nonneg_left h2 hM'0
    _ = M' * (33 / a) * z.im := by ring

end QuantumZipper.Thm18Asm.G1RC

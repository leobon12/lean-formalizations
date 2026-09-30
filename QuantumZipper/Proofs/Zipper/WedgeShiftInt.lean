import QuantumZipper.Proofs.Zipper.WedgeShiftRaw
import QuantumZipper.Proofs.LQG.WedgeInfGrowth

/-!
# WEDGE-SHIFT (4): integrability of the radial pieces on every folded circle

The sub-node `F1.WedgeCircleIntStmt`: a.s., on every folded circle `fc(w, ρ)` (also those through
`0`), the semicircle averages `radAvgReg X ‖·‖` of the free field and the radial process
`A(−log‖·‖)` are integrable.

Both are `f(−log‖u‖)` for a continuous `f` of at most linear growth at `+∞` (the law of large
numbers for Brownian motion, `BMLLN.ae_tendsto_div_atTop`, applied to the radial Brownian motion
of the free field `WedgeTK.radialBMpos` and to the forward Brownian motion of the wedge process),
and `log‖·‖` is integrable on folded circles (`CoordReg.integrable_log_norm_foldedCircle`).

Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace QuantumZipper
namespace F1

theorem fc_ae_norm_le' (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ x ∂(foldedCircle w r), ‖x‖ ≤ ‖w‖ + r := by
  unfold foldedCircle
  rw [ae_map_iff measurable_foldH.aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)]
  filter_upwards [CircleMV.ae_circleUnif w r] with x hx
  rw [CircleFubini.norm_foldH']
  calc ‖x‖ = ‖w + (x - w)‖ := by ring_nf
    _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
    _ = ‖w‖ + r := by rw [hx, abs_of_nonneg hr]

/-- A continuous `f` with `|f τ| ≤ K + M |τ|` for `τ ≥ −log(‖w‖ + ρ)` gives an integrable
`f(−log‖·‖)` on `fc(w, ρ)`. -/
theorem integrable_fc_comp_neglog {f : ℝ → ℝ} (hf : Continuous f) (w : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    {K M : ℝ} (hbd : ∀ τ, -Real.log (‖w‖ + ρ) ≤ τ → |f τ| ≤ K + M * |τ|) :
    Integrable (fun u => f (-Real.log ‖u‖)) (foldedCircle w ρ) := by
  have hm : Measurable fun u : ℂ => f (-Real.log ‖u‖) :=
    hf.measurable.comp (Real.measurable_log.comp measurable_norm).neg
  have hdom : Integrable (fun u : ℂ => K + M * |Real.log ‖u‖|) (foldedCircle w ρ) :=
    (integrable_const K).add ((CoordReg.integrable_log_norm_foldedCircle w ρ).abs.const_mul M)
  refine hdom.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero_fc w hρ, fc_ae_norm_le' w hρ.le] with u hu hle
  have hlog : Real.log ‖u‖ ≤ Real.log (‖w‖ + ρ) :=
    Real.log_le_log (norm_pos_iff.2 hu) hle
  rw [Real.norm_eq_abs]
  have := hbd (-Real.log ‖u‖) (by linarith)
  rwa [abs_neg] at this

/-- From linear growth on `[0, ∞)` and continuity to a bound on `[a, ∞)`. -/
theorem exists_bound_ge {f : ℝ → ℝ} (hf : Continuous f) {K M : ℝ}
    (h : ∀ s, 0 ≤ s → |f s| ≤ K + M * s) (hM : 0 ≤ M) (a : ℝ) :
    ∃ K' : ℝ, ∀ τ, a ≤ τ → |f τ| ≤ K' + M * |τ| := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := 0)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max K C, fun τ hτ => ?_⟩
  rcases le_or_gt 0 τ with h0 | h0
  · rw [abs_of_nonneg h0]
    linarith [h τ h0, le_max_left K C]
  · have := hC τ ⟨hτ, h0.le⟩
    rw [Real.norm_eq_abs] at this
    have : 0 ≤ M * |τ| := mul_nonneg hM (abs_nonneg _)
    linarith [le_max_right K C]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Linear growth of the semicircle averages of the free field in log-scale. -/
theorem ae_growth_radAvgReg {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∃ K M : ℝ, 0 ≤ M ∧ ∀ s, 0 ≤ s →
      |radAvgReg (X ω) (Real.exp (-s))| ≤ K + M * s := by
  have hB := WedgeTK.isBrownianReal_radialBMpos hX
  filter_upwards [BMLLN.ae_tendsto_div_atTop hB, hB.cont] with ω hlim hc
  obtain ⟨K, hK⟩ := WedgeInf.exists_abs_le_of_tendsto_div hc hlim one_pos
  refine ⟨√2 * K + |radAvgReg (X ω) 1|, √2, by positivity, fun s hs => ?_⟩
  have h := hK s.toNNReal
  simp only [WedgeTK.radialBMpos, WedgeTK.radialProc, Real.coe_toNNReal _ hs, one_mul,
    abs_mul, abs_inv] at h
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [abs_of_pos h2] at h
  have h3 : |radAvgReg (X ω) (Real.exp (-s)) - radAvgReg (X ω) 1| ≤ √2 * (s + K) := by
    rw [inv_mul_le_iff₀ h2] at h
    linarith
  have h4 := abs_sub_abs_le_abs_sub (radAvgReg (X ω) (Real.exp (-s))) (radAvgReg (X ω) 1)
  nlinarith

omit [IsProbabilityMeasure P] in
/-- Linear growth of the forward wedge radial process. -/
theorem ae_growth_wedge {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsWedgeProcess α Q A P) :
    ∀ᵐ ω ∂P, ∃ K M : ℝ, 0 ≤ M ∧ ∀ s, 0 ≤ s → |A s ω| ≤ K + M * s := by
  obtain ⟨B, B', hB, -, -, hAB⟩ := hA
  filter_upwards [BMLLN.ae_tendsto_div_atTop hB, hB.cont] with ω hlim hc
  obtain ⟨K, hK⟩ := WedgeInf.exists_abs_le_of_tendsto_div hc hlim one_pos
  refine ⟨√2 * K, √2 + |α - Q|, by positivity, fun s hs => ?_⟩
  have h := hK s.toNNReal
  rw [Real.coe_toNNReal _ hs, one_mul] at h
  rw [hAB ω s]
  simp only [wedgePath, hs, ite_true]
  have h2 : (0 : ℝ) ≤ √2 := by positivity
  calc |√2 * B s.toNNReal ω + (α - Q) * s|
      ≤ |√2 * B s.toNNReal ω| + |(α - Q) * s| := abs_add_le _ _
    _ = √2 * |B s.toNNReal ω| + |α - Q| * s := by
        rw [abs_mul, abs_mul, abs_of_nonneg h2, abs_of_nonneg hs]
    _ ≤ √2 * (s + K) + |α - Q| * s := by gcongr
    _ = √2 * K + (√2 + |α - Q|) * s := by ring

/-- **The integrability sub-node holds.** -/
theorem wedgeCircleIntStmt_holds (γ α : ℝ) : WedgeCircleIntStmt γ α := by
  intro Ω' _ P' _ X A hX hA hI
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [hG.ae_good, ae_growth_radAvgReg hX, ae_growth_wedge hA,
    WedgeCan4.ae_continuous_wedgeProcess hA] with ω hg hr hw hc w ρ hρ
  obtain ⟨K₁, M₁, hM₁, h₁⟩ := hr
  obtain ⟨K₂, M₂, hM₂, h₂⟩ := hw
  constructor
  · -- `radAvgReg x ‖u‖ = f (−log‖u‖)` with `f τ = F(0, e^{−τ})`
    have hfc : Continuous fun τ : ℝ => G ω ((0 : ℂ), Real.exp (-τ)) :=
      hg.1.1.comp_continuous (continuous_const.prodMk (Real.continuous_exp.comp continuous_neg))
        fun τ => ⟨WedgeMeasCoord.zero_mem_Hbar_wm, Real.exp_pos _⟩
    have hfe : ∀ τ : ℝ, G ω ((0 : ℂ), Real.exp (-τ)) = radAvgReg (X ω) (Real.exp (-τ)) :=
      fun τ => (hg.radAvgReg_eq (Real.exp_pos _)).symm
    obtain ⟨K', hK'⟩ := exists_bound_ge hfc (fun s hs => by rw [hfe]; exact h₁ s hs) hM₁
      (-Real.log (‖w‖ + ρ))
    refine (integrable_fc_comp_neglog hfc w hρ hK').congr ?_
    filter_upwards [ae_ne_zero_fc w hρ] with u hu
    rw [hfe, neg_neg, Real.exp_log (norm_pos_iff.2 hu)]
  · obtain ⟨K', hK'⟩ := exists_bound_ge hc h₂ hM₂ (-Real.log (‖w‖ + ρ))
    exact integrable_fc_comp_neglog hc w hρ hK'

/-- **Field-level B4(c) from RC3 of the wedge field on all folded circles.** -/
theorem wedgeAddConstLawStmt_of_rc3All
    (hRC : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeRC3AllStmt γ α) :
    WedgeAddConstLawStmt :=
  wedgeAddConstLawStmt_of_rc3 hRC fun γ α _ _ _ => wedgeCircleIntStmt_holds γ α

end F1
end QuantumZipper

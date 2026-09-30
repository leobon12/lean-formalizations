import QuantumZipper.Proofs.Zipper.ScaleGeomInBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SCALEGEOM-IN, part 2: scale consistency and `ScaleGeomFixInputsStmt` (F2 step (4), D45)

The scale-consistency half of input (2) of `F2.ScaleGeomFixInputsStmt`: a.s., for all `t ≥ 0`,
`G1.ScaleConsistentAt (h⁰ + X) Q a` at the images of folded circles under `f_t⁻¹` of the rescaled
driver `W(a²·)/a`. Route (the one already used for the wedge field in
`WedgeUnzip.wedgeContinuum_of_x` and `WedgeUnzip.unscaledB3dStmt_of_core`):

* `WedgeUnzip.scaleConsistent_of_continuum` (proved): scale consistency at those images follows
  from regularity and the continuum limit of the smoothed pairings against
  `ν = (f_{a²t}⁻¹)_* fc(a d, a r)` (Brownian scaling of the Loewner flow, `RS.fwdMapInv_scale`);
* `continuum_add_Lf` (deterministic, here): the continuum limit survives adding a log
  singularity `Lf α = α(−log‖·‖)`: the smoothed pairing of `Lf α` is `α(−∫ log max(ρ, ‖u‖) dν)`,
  which converges to `α(−∫ log‖u‖ dν)` with rate `3Cρ^{1/3}` because `ν` is a `1/3`-Frostman
  probability measure carried by a bounded part of `ℍ` (`RegCont.νT_facts`,
  `RegCont.integral_log_max_sub_le`);
* `h⁰ + X = (X + α₀(−log‖·‖)) + Lf(−√κ)` (`F2.h0rev_add_eq`), and the continuum limit for
  `X + α₀(−log‖·‖)` at all times is the existing named node `WedgeUnzip.XContinuumStmt`
  (`WedgeUnzipCore.lean:76`).

Main results: `scaleGeomRegAeStmt_of` (input (2) from `YExactAllStmt` and `XContinuumStmt`),
`scaleGeomFixInputsStmt_of` (all of `ScaleGeomFixInputsStmt` from `YGoodAllStmt`,
`YExactAllStmt`, `XContinuumStmt`) and `scaleGeomAeStmt'_of_nodes`.

Sources: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (pp. 60–62);
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, §3.1 (circle-average smoothing).
Own bookkeeping (dominated/Frostman convergence of the log term; no new mathematics).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- `h⁰ + x = (x + α₀(−log‖·‖)) + Lf(−√κ)`. -/
theorem sgin_h0rev_add_eq_logSing_Lf (κ : ℝ) (x : FieldSample) :
    ofFun (h0rev κ) + x = (x + logSingField κ) + ofFun (LogSingGood.Lf (-Real.sqrt κ)) := by
  rw [h0rev_add_eq]
  congr 1
  unfold gammaLog
  congr 1
  funext z
  simp only [LogSingGood.Lf]
  ring

/-- **The continuum limit survives adding a log singularity** (deterministic). -/
theorem continuum_add_Lf {x₀ : FieldSample} {F₀ : ℂ × ℝ → ℝ} (hF₀ : IsRegularWith x₀ F₀)
    (α : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) (c : ℂ)
    {r : ℝ} (hr : 0 < r)
    (hint : ∀ ρ : ℝ, 0 < ρ → Integrable (fun u => evalReg x₀ (foldedCircle u ρ))
      ((foldedCircle c r).map (fwdMapInv W T)))
    (hL : ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg x₀ (foldedCircle u ρ)
      ∂((foldedCircle c r).map (fwdMapInv W T))) (𝓝[>] 0) (𝓝 L)) :
    (∀ ρ : ℝ, 0 < ρ → Integrable
      (fun u => evalReg (x₀ + ofFun (LogSingGood.Lf α)) (foldedCircle u ρ))
      ((foldedCircle c r).map (fwdMapInv W T))) ∧
    ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg (x₀ + ofFun (LogSingGood.Lf α)) (foldedCircle u ρ)
      ∂((foldedCircle c r).map (fwdMapInv W T))) (𝓝[>] 0) (𝓝 L) := by
  set ν := (foldedCircle c r).map (fwdMapInv W T) with hν
  obtain ⟨C, B, _hC, _hB, hfacts⟩ := RegCont.νT_facts hW hW0 T c hr
  obtain ⟨hP, hFr, hae⟩ := hfacts T ⟨hT, le_rfl⟩
  have : IsProbabilityMeasure ν := hP
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hνK : ν (Metric.closedBall (0 : ℂ) B ∩ Hbar)ᶜ = 0 := by
    have h1 : ∀ᵐ z ∂ν, z ∈ Metric.closedBall (0 : ℂ) B ∩ Hbar :=
      hae.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, WedgeUnzip.mem_Hbar_of_mem_H hz.1⟩
    exact ae_iff.1 h1
  have hlogi : ∀ ρ : ℝ, 0 < ρ → Integrable (fun u : ℂ => Real.log (max ρ ‖u‖)) ν :=
    fun ρ hρ => FrostmanReg.integrable_of_continuousOn_frostman hK inter_subset_right hνK
      (Continuous.log (continuous_const.max continuous_norm) fun _ =>
        (hρ.trans_le (le_max_left _ _)).ne').continuousOn
  have hev : ∀ ρ : ℝ, 0 < ρ →
      (fun u => evalReg (x₀ + ofFun (LogSingGood.Lf α)) (foldedCircle u ρ)) =ᵐ[ν]
        fun u => evalReg x₀ (foldedCircle u ρ) + α * -Real.log (max ρ ‖u‖) := fun ρ hρ =>
    hae.mono fun u hu => LogSingGood.evalReg_add_Lf_fc hF₀ α (WedgeUnzip.mem_Hbar_of_mem_H hu.1) hρ
  have hsum : ∀ ρ : ℝ, 0 < ρ → Integrable
      (fun u => evalReg x₀ (foldedCircle u ρ) + α * -Real.log (max ρ ‖u‖)) ν :=
    fun ρ hρ => (hint ρ hρ).add ((hlogi ρ hρ).neg.const_mul α)
  refine ⟨fun ρ hρ => (hsum ρ hρ).congr (hev ρ hρ).symm, ?_⟩
  obtain ⟨L, hL⟩ := hL
  have hν0 : ∀ᵐ z ∂ν, z ≠ 0 := hae.mono fun z hz h => by subst h; simp [H] at hz
  have hlog : Tendsto (fun ρ => ∫ u, Real.log (max ρ ‖u‖) ∂ν) (𝓝[>] 0)
      (𝓝 (∫ u, Real.log ‖u‖ ∂ν)) := by
    have h3 : Tendsto (fun ρ : ℝ => 3 * C * ρ ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const 0 (1 / 3 : ℝ)
        (Or.inr (by norm_num))).tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rw [Real.zero_rpow (by norm_num)] at h
      simpa using h.const_mul (3 * C)
    refine tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero' (Eventually.of_forall fun ρ => norm_nonneg _) ?_ h3)
    filter_upwards [Ioc_mem_nhdsGT one_pos] with ρ hρ
    rw [Real.norm_eq_abs]
    exact (RegCont.integral_log_max_sub_le hFr hν0 (hae.mono fun z hz => hz.2) hρ.1 hρ.2).2
  refine ⟨L + α * -∫ u, Real.log ‖u‖ ∂ν, (hL.add (hlog.neg.const_mul α)).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  have hi2 : Integrable (fun u : ℂ => α * -Real.log (max ρ ‖u‖)) ν :=
    (hlogi ρ hρ).neg.const_mul α
  rw [integral_congr_ae (hev ρ hρ), integral_add (hint ρ hρ) hi2, integral_const_mul,
    integral_neg]

/-- **Input (2) of `ScaleGeomFixInputsStmt`** from `WedgeUnzip.YExactAllStmt` (RC3 half) and
`WedgeUnzip.XContinuumStmt` (scale-consistency half). -/
theorem scaleGeomRegAeStmt_of (hYE : WedgeUnzip.YExactAllStmt)
    (hXC : WedgeUnzip.XContinuumStmt) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {a : ℝ} (ha : 0 < a) : ScaleGeomRegAeStmt κ a P B X := by
  filter_upwards [ae_rc3_of_yExact hYE hκ hκ4 hB hX hind, hXC κ hκ hκ4 P B X hB hX hind,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hrc hco hc h0 t ht
  have hW : Continuous (drive κ B ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have hta : 0 ≤ a ^ 2 * t := mul_nonneg (sq_nonneg a) ht
  obtain ⟨⟨F₀, hF₀⟩, hco⟩ := hco
  refine ⟨fun d r hr => ?_, hrc (a ^ 2 * t) hta⟩
  rw [sgin_h0rev_add_eq_logSing_Lf]
  obtain ⟨hint, hL⟩ := hco (a ^ 2 * t) hta ((a : ℂ) * d) (a * r) (mul_pos ha hr)
  obtain ⟨hint', hL'⟩ := continuum_add_Lf hF₀ (-Real.sqrt κ) hW hW0 hta _ (mul_pos ha hr) hint hL
  exact WedgeUnzip.scaleConsistent_of_continuum ⟨_, LogSingGood.regular_add_Lf hF₀ _⟩ _ hW hW0
    ha ht d hr hint' hL'

end F2
end QuantumZipper

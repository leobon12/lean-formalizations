import QuantumZipper.Proofs.Thm18.G3Za1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (a), layer 2: `ofFun f + W` at pulled-back circles through the log singularity

For a free field `W`, a local conformal map `Φ` at `0` with `Φ 0 = 0` (`PullData`), and a profile
`f = a (−log ‖·‖) + h` near `0` (`h` continuous), almost surely

  `evalReg (ofFun f + W) (Φ_* fc(c, s)) = ∫ f d(Φ_* fc(c, s)) + W (Φ_* fc(c, s))`

for every folded circle `fc(c, s)` in the pull-back disc, including circles through `0`
(`ae_evalReg_ofFun_add_pullCircle`); hence the coordinate change of `ofFun f + W` through `Φ`
at `fc(c, s)` is that of `W` plus `∫ f ∘ Φ d fc(c, s)` (`ae_coordChange_ofFun_add_pullCircle`).

Inputs: the regularization of `W` at pulled-back circles converges (the Borel–Cantelli argument
of `G3Cv.ae_evalReg_pullCircle`, kept in `Tendsto` form: `ae_tendsto_avgReg_pullCircle`);
continuity of the dyadic circle averages of `W` (`FrostmanReg.ae_circleAvg_tendsto_frostman`);
the deterministic layer `G3Za.evalReg_ofFun_add_logSing`; `log ‖Φ‖` is integrable on circles by
the bi-Lipschitz bound. Own elementary argument (Sheffield arXiv:1012.4797, p. 70, treats the
zoom of `h + γ(−log|· − x|)` through a conformal map without comment).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

open G3Cv SmoothConv CircleFubini CoordChange

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- **Regularization at pulled-back circles, `Tendsto` form.** -/
theorem ae_tendsto_avgReg_pullCircle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : Ω → FieldSample} (hW : IsFreeGFFModConstH W P)
    (hD : PullData Φ b r₀ ρ r₁ m M) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcr : ‖c - b‖ + r ≤ ρ) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (W ω) k z ∂pullCircle Φ c r) atTop
      (𝓝 (W ω (pullCircle Φ c r))) := by
  set μ := pullCircle Φ c r with hμ
  have hadm : IsAdmissibleH μ := hD.isAdmissibleH_pullCircle hr hcr
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hD.conf.meas.aemeasurable).2 inferInstance
  obtain ⟨K, hK, hKH, hKc⟩ := hadm.2.1
  have h1 : ∀ᵐ ω ∂P, ∀ k, ∫ z, avgReg (W ω) k z ∂μ =
      W ω (μ.bind fun w => foldedCircle w (radius k)) :=
    ae_all_iff.2 fun k => Regularization.ae_integral_avgReg_eq hW k μ hK hKH hKc
  set D : ℕ → Ω → ℝ := fun k ω => W ω (μ.bind fun w => foldedCircle w (radius k)) - W ω μ
  have hadmk : ∀ k, IsAdmissibleH (μ.bind fun w => foldedCircle w (radius k)) := fun k =>
    hD.isAdmissibleH_pullCircle_bind hr hcr (radius_pos k)
  have hmass : ∀ k, (μ.bind fun w => foldedCircle w (radius k)) univ = μ univ := fun k =>
    bind_circle_univ μ
  have hmom := fun k => integral_sq_pair_eq hW (hadmk k) hadm (hmass k)
  have hm := hD.bl.1
  have hvar : ∀ k, ∫ ω, D k ω ^ 2 ∂P ≤ 16 / (m * r) * (1 / 2 : ℝ) ^ k := by
    intro k
    rw [(hmom k).2]
    refine (le_abs_self _).trans ((abs_kernelCov2_bind_le hadm (radius_pos k) (hadmk k)
      (fun x hx => integral_Lr_pullCircle_bounds hD hr hcr (radius_pos k) hx)).trans
      (le_of_eq ?_))
    unfold radius; field_simp
  have hsum : Summable fun k => ∫ ω, D k ω ^ 2 ∂P := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => sq_nonneg _) hvar ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h2 := ae_tendsto_zero_of_summable_sq
    (fun k => ((hW.measurable_coord _).sub (hW.measurable_coord _)).aemeasurable)
    (fun k => (hmom k).1) hsum
  filter_upwards [h1, h2] with ω h1 h2
  simp only [h1]
  have := h2.add_const (W ω μ)
  rw [zero_add] at this
  refine this.congr fun k => ?_
  show D k ω + W ω μ = _
  simp only [D]; ring

/-- `log ‖Φ‖` is integrable on folded circles in the bi-Lipschitz disc. -/
theorem integrable_log_norm_comp_fc (hD : PullData Φ 0 r₀ ρ r₁ m M) (hΦ0 : Φ 0 = 0)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hcr : ‖c‖ + r ≤ ρ) :
    Integrable (fun u => Real.log ‖Φ u‖) (foldedCircle c r) := by
  have hnull := foldedCircle_compl_null (b := 0) hr (by simpa using hcr)
  have hae := ae_mem_of_compl_null_g3cv hnull
  have hmeas : Measurable fun u => Real.log ‖Φ u‖ :=
    Real.measurable_log.comp (measurable_norm.comp hD.conf.meas)
  refine ((CoordReg.integrable_log_norm_foldedCircle c r).abs.add
    (integrable_const (|Real.log m| + |Real.log M|))).mono' hmeas.aestronglyMeasurable
    (hae.mono fun u hu => ?_)
  have hu0 : u ∈ closedBall ((0 : ℝ) : ℂ) ρ := hu.1
  have h00 : ((0 : ℝ) : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ := mem_closedBall_self hD.hρ.le
  have hb := hD.bl.2.2 u hu0 _ h00
  simp only [Complex.ofReal_zero, sub_zero, hΦ0] at hb
  have h := abs_log_sub_le_g3cv hD.bl.1 hD.bl.2.1 (norm_nonneg u) (norm_nonneg _) hb.1 hb.2
  rw [Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (Real.log ‖Φ u‖) (Real.log ‖u‖)
  simp only [Pi.add_apply]
  linarith

/-- **`ofFun f + W` at a pulled-back circle** (a.s.), circles through the singularity included. -/
theorem ae_evalReg_ofFun_add_pullCircle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : Ω → FieldSample} (hW : IsFreeGFFModConstH W P)
    (hD : PullData Φ 0 r₀ ρ r₁ m M) (hΦ0 : Φ 0 = 0) {a ρf : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = a * -Real.log ‖u‖ + h u)
    (hh : Continuous h) (hMρ : M * ρ < ρf) {c : ℂ} {r : ℝ} (hr : 0 < r) (hcr : ‖c‖ + r ≤ ρ) :
    ∀ᵐ ω ∂P, evalReg (ofFun f + W ω) (pullCircle Φ c r) =
      (∫ u, f u ∂pullCircle Φ c r) + W ω (pullCircle Φ c r) := by
  have hcr' : ‖c - ((0 : ℝ) : ℂ)‖ + r ≤ ρ := by simpa using hcr
  have : IsProbabilityMeasure (pullCircle Φ c r) :=
    (Measure.isProbabilityMeasure_map_iff hD.conf.meas.aemeasurable).2 inferInstance
  have hnull := foldedCircle_compl_null (b := 0) hr hcr'
  have hae := ae_mem_of_compl_null_g3cv hnull
  have h00 : ((0 : ℝ) : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ := mem_closedBall_self hD.hρ.le
  have hbl : ∀ u ∈ closedBall ((0 : ℝ) : ℂ) ρ, m * ‖u‖ ≤ ‖Φ u‖ ∧ ‖Φ u‖ ≤ M * ‖u‖ := by
    intro u hu
    have hb := hD.bl.2.2 u hu _ h00
    simpa [hΦ0] using hb
  have hreg : ∀ᵐ ω ∂P, RegCont.RegAvgGood (W ω) :=
    ae_all_iff.2 fun k => FrostmanReg.ae_circleAvg_tendsto_frostman hW k
  have hf' : ∀ u ∈ closedBall ((0 : ℝ) : ℂ) ρf ∩ Hbar,
      f u = a * -Real.log ‖u - ((0 : ℝ) : ℂ)‖ + h u := by
    intro u hu; simpa using hf u (by simpa using hu)
  -- support, atoms and log-integrability of the pulled-back circle
  have hν : ∀ᵐ w ∂pullCircle Φ c r, w ∈ closedBall ((0 : ℝ) : ℂ) (M * ρ) ∩ Hbar := by
    refine (ae_map_iff (p := fun w => w ∈ closedBall ((0 : ℝ) : ℂ) (M * ρ) ∩ Hbar)
      hD.conf.meas.aemeasurable
      (by exact (isClosed_closedBall.inter isClosed_Hbar).measurableSet)).2 ?_
    filter_upwards [hae] with u hu
    refine ⟨?_, hD.up u hu⟩
    have h1 := (hbl u hu.1).2
    have h2 : ‖u‖ ≤ ρ := by simpa using hu.1
    rw [mem_closedBall, Complex.ofReal_zero, dist_zero_right]
    nlinarith [hD.bl.2.1]
  have hνp : ∀ᵐ w ∂pullCircle Φ c r, w ≠ ((0 : ℝ) : ℂ) := by
    refine (ae_map_iff (p := fun w => w ≠ ((0 : ℝ) : ℂ)) hD.conf.meas.aemeasurable
      (by exact (measurableSet_singleton _).compl)).2 ?_
    filter_upwards [hae, F1.ae_ne_zero_fc c hr] with u hu hu0 h0
    have h1 := (hbl u hu.1).1
    rw [Complex.ofReal_zero] at h0
    rw [h0, norm_zero] at h1
    have : 0 < m * ‖u‖ := mul_pos hD.bl.1 (norm_pos_iff.2 hu0)
    linarith
  have hlog : Integrable (fun w : ℂ => Real.log ‖w - ((0 : ℝ) : ℂ)‖) (pullCircle Φ c r) := by
    rw [pullCircle, integrable_map_measure (measurable_log_norm_sub 0).aestronglyMeasurable
      hD.conf.meas.aemeasurable]
    have := integrable_log_norm_comp_fc hD hΦ0 hr hcr
    refine this.congr (ae_of_all _ fun u => ?_)
    simp
  filter_upwards [hreg, ae_tendsto_avgReg_pullCircle hW hD hr hcr'] with ω hreg hA
  exact evalReg_ofFun_add_logSing hreg hf' hh hMρ hν hνp hlog hA

/-- **Coordinate change of `ofFun f + W` at a circle** (a.s.): that of `W` plus `∫ f ∘ Φ`. -/
theorem ae_coordChange_ofFun_add_pullCircle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : Ω → FieldSample} (hW : IsFreeGFFModConstH W P)
    (hD : PullData Φ 0 r₀ ρ r₁ m M) (hΦ0 : Φ 0 = 0) {a ρf : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = a * -Real.log ‖u‖ + h u)
    (hh : Continuous h) (hfm : Measurable f) (hMρ : M * ρ < ρf) (Q : ℝ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hcr : ‖c‖ + r ≤ ρ) :
    ∀ᵐ ω ∂P, coordChange (ofFun f + W ω) Φ Q (foldedCircle c r) =
      coordChange (W ω) Φ Q (foldedCircle c r) + ∫ u, f (Φ u) ∂foldedCircle c r := by
  have hcr' : ‖c - ((0 : ℝ) : ℂ)‖ + r ≤ ρ := by simpa using hcr
  filter_upwards [ae_evalReg_ofFun_add_pullCircle hW hD hΦ0 hf hh hMρ hr hcr,
    ae_evalReg_pullCircle hW hD hr hcr'] with ω h1 h2
  simp only [coordChange]
  have e1 : evalReg (ofFun f + W ω) ((foldedCircle c r).map Φ) =
      (∫ u, f u ∂pullCircle Φ c r) + W ω (pullCircle Φ c r) := h1
  have e2 : evalReg (W ω) ((foldedCircle c r).map Φ) = W ω (pullCircle Φ c r) := h2
  rw [e1, e2]
  have e3 : ∫ u, f u ∂pullCircle Φ c r = ∫ u, f (Φ u) ∂foldedCircle c r := by
    rw [pullCircle]
    exact integral_map hD.conf.meas.aemeasurable hfm.aestronglyMeasurable
  rw [e3]; ring

end G3Za
end QuantumZipper

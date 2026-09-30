import QuantumZipper.Proofs.Thm18.G1RegLogDeriv
import QuantumZipper.Proofs.LQG.VagueUniqueOn
import QuantumZipper.Proofs.LQG.WedgeGood

/-!
# G1-REG, part 2: goodness and positive scale of the pulled-back field from the wedge law

Clauses (iii) (`IsLQGGood γ x`) and (iv) (`0 < scaleParam γ x`) of `G1.ChoiceRegular`, for the
pulled-back field `x = coordChange y ψ Q`, follow from the wedge law of its canonical
description `canonical γ x` (part (a) of `G1SideCore`), deterministically per sample:

* `G1.scaleParam_pos_of_canonical`: if `canonical γ x` has unit area on `B₁(0) ∩ ℍ`, then
  `scaleParam γ x > 0` (if it were `0`, `canonical γ x = rescale x Q 0` has constant circle
  averages, so its area approximations tend to `0` and its area measure is `0`);
* `G1.isLQGGood_of_canonical`: if `x` is a regular sample whose folded-circle values are its
  regularized ones (clause (ii)), `scaleParam γ x > 0` and `canonical γ x` is good, then `x` is
  good (`x` and `rescale (canonical γ x) Q s⁻¹` have the same circle coordinates; M4-T3).

Own elementary arguments (bookkeeping on the conformal covariance under dilations, Sheffield
§1.6, (1.8), and M4-T3 `IsLQGGood.rescale`).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1

/-- `rescale x Q 0` has constant folded-circle values `evalReg x (δ₀)`. -/
theorem rescale_zero_apply (x : FieldSample) (Q : ℝ) (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    rescale x Q 0 μ = evalReg x (Measure.dirac 0) := by
  unfold rescale coordChange
  have h1 : (fun z : ℂ => ((0 : ℝ) : ℂ) * z) = fun _ => (0 : ℂ) := by funext z; simp
  have h2 : ∀ z : ℂ, deriv (fun w : ℂ => ((0 : ℝ) : ℂ) * w) z = 0 := fun z => by simp
  simp only [h2, norm_zero, Real.log_zero, integral_zero, mul_zero, add_zero]
  rw [h1, Measure.map_const, measure_univ, one_smul]

/-- The area measure of `rescale x Q 0` vanishes (`γ > 0`). -/
theorem qAreaMeasure_rescale_zero {γ : ℝ} (hγ : 0 < γ) (x : FieldSample) (Q : ℝ) :
    qAreaMeasure γ (rescale x Q 0) = 0 := by
  set K := evalReg x (Measure.dirac 0)
  have havg : ∀ k z, avgReg (rescale x Q 0) k z = K := fun k z => by
    unfold avgReg
    simp_rw [rescale_zero_apply]
    exact tendsto_const_nhds.limUnder_eq
  set a : ℕ → ℝ := fun k => radius k ^ (γ ^ 2 / 2) * Real.exp (γ * K) with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have happ : ∀ k, areaApprox γ (rescale x Q 0) k = ENNReal.ofReal (a k) • volume.restrict H := by
    intro k
    unfold areaApprox
    simp_rw [havg]
    exact withDensity_const _
  have hlim : Tendsto a atTop (𝓝 0) := by
    have hr : Tendsto radius atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hp : 0 < γ ^ 2 / 2 := by positivity
    have := (hr.rpow_const (Or.inr hp.le)).mul_const (Real.exp (γ * K))
    rwa [Real.zero_rpow hp.ne', zero_mul] at this
  refine qAreaMeasure_eq ⟨by simp, fun _ _ _ => by simp, fun f _ _ _ => ?_⟩
  simp only [integral_zero_measure, happ, integral_smul_measure]
  have e : ∀ k, (ENNReal.ofReal (a k)).toReal • ∫ z, f z ∂volume.restrict H =
      a k * ∫ z, f z ∂volume.restrict H := fun k => by
    rw [ENNReal.toReal_ofReal (ha0 k), smul_eq_mul]
  simp_rw [e]
  simpa using hlim.mul_const (∫ z, f z ∂volume.restrict H)

/-- **Clause (iv) from the unit area of the canonical description.** -/
theorem scaleParam_pos_of_canonical {γ : ℝ} (hγ : 0 < γ) {x : FieldSample}
    (h1 : qAreaMeasure γ (canonical γ x) (ball 0 1 ∩ H) = 1) : 0 < scaleParam γ x := by
  have hnn : 0 ≤ scaleParam γ x := Real.sInf_nonneg fun a ha => ha.1.le
  refine lt_of_le_of_ne hnn fun h0 => ?_
  have hc : canonical γ x = rescale x (Qc γ) 0 := by rw [canonical, ← h0]
  rw [hc, qAreaMeasure_rescale_zero hγ] at h1
  simp at h1

/-- Folded-circle values of `rescale (rescale x Q s) Q s⁻¹` for a regular `x`: the regularized
values of `x`. -/
theorem rescale_rescale_inv_fc {x : FieldSample} (hx : IsRegularSample x) (Q : ℝ) {s : ℝ}
    (hs : 0 < s) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    rescale (rescale x Q s) Q s⁻¹ (foldedCircle d r) = evalReg x (foldedCircle d r) := by
  obtain ⟨F, hF⟩ := hx
  have hsi : 0 < s⁻¹ := inv_pos.2 hs
  rw [RegClosure.rescale_fc_eq (hF.rescale' Q hs) Q hsi d hr,
    ← WedgeTK.fc_foldH_eq d r, hF.evalReg_fc_of_mem (CircleFubini.foldH_mem_Hbar' d) hr]
  have e1 : (s : ℂ) * foldH ((s⁻¹ : ℝ) * d) = foldH d := by
    rw [← RegClosure.foldH_mul_pos _ hs]
    congr 1
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  rw [e1, show s * (s⁻¹ * r) = r by field_simp, Real.log_inv]
  ring

/-- **Clause (iii) from the goodness of the canonical description.** -/
theorem isLQGGood_of_canonical {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsRegularSample x)
    (hexact : ∀ d ∈ Hbar, ∀ r > 0, evalReg x (foldedCircle d r) = x (foldedCircle d r))
    (hs : 0 < scaleParam γ x) (hc : IsLQGGood γ (canonical γ x)) : IsLQGGood γ x := by
  have hg := hc.rescale hγ (inv_pos.2 hs)
  refine (WedgeGood.isLQGGood_congr_coords (γ := γ) ?_).1 hg
  funext i
  simp only [Factorization.coords]
  set d := (Factorization.dyadicIndex i).1
  set r := radius (Factorization.dyadicIndex i).2
  have hr : 0 < r := radius_pos _
  rw [canonical, rescale_rescale_inv_fc hx _ hs d hr, ← WedgeTK.fc_foldH_eq d r,
    hexact _ (CircleFubini.foldH_mem_Hbar' d) r hr]

end G1
end Thm18Asm
end QuantumZipper

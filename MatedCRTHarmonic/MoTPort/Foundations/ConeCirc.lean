/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.Foundations.Cone
import LQGMetric.Field.CircleAvgCont
import LQGMetric.Field.CircleAvgRate

/-!
# The circle-average process of a cone field

DMS Def 4.10 (L2198): the average of the cone field on `∂B(0, e^{-s})` is the radial process.
Deterministic form here: for any field `y` whose circle average at radius `r` about `0` exists
(as the limit of LM's mollified averages), and any continuous `A` making the radial function
locally integrable,
`circleAvg (coneField y A Q) r 0 = circleAvg y r 0 + Q(−log r) + A(−log r)`
(`circleAvg_coneField`), hence at `r = e^{-t}`: `Q t + A t` plus the circle average of `y`
(`circleAvg_coneField_exp`). For `y` the lateral part of a whole-plane GFF the latter vanishes a.s.

Proof: adapted from LM `CircleAvg.tendsto_mollAvg_ofCont` (LQGMetric/Field/CircleAvgCont.lean):
near the circle `|z| = r` the radial function agrees with the continuous function
`z ↦ F(−log max(|z|, r/2))`, and the mollifier at scale `2^{-n} ≤ r/2` only sees that region
(locality of `ofFunC`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace MatedCRTHarmonic.MoTPort

open LQGMetric

namespace ConeCirc

lemma ofFunC_apply' {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (φ : TestC) :
    ofFunC f φ = ∫ x, φ x * f x := by
  rw [ofFunC, Distribution.ofFun_apply (hf.locallyIntegrableOn _)]
  rfl

/-- locality: the pairing with the mollifier `ψ_{n,x}` only sees `f` on `B(x, 2^{-n})` -/
lemma ofFunC_bumpTest_eq {f g : ℂ → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) {x : ℂ} {δ : ℝ} (hfg : ∀ y, dist y x < δ → f y = g y)
    {n : ℕ} (hn : (2 : ℝ)⁻¹ ^ n ≤ δ) :
    ofFunC f (bumpTest n x) = ofFunC g (bumpTest n x) := by
  rw [ofFunC_apply' hf, ofFunC_apply' hg]
  congr 1
  funext y
  by_cases hy : dist y x < δ
  · rw [hfg y hy]
  · rw [CircleAvg.bumpTest_eq_zero_of_le n (le_trans hn (not_lt.mp hy))]; simp

/-- the mollified circle averages of a radial function `F(−log|·|)` (`F` continuous, the function
locally integrable) converge to `F(−log r)` -/
theorem tendsto_mollAvg_radial {F : ℝ → ℝ} (hF : Continuous F) {f : ℂ → ℝ}
    (hf : LocallyIntegrable f volume) (hfF : ∀ z, f z = F (-Real.log ‖z‖)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => CircleAvg.mollAvg (ofFunC f) n 0 r) atTop (𝓝 (F (-Real.log r))) := by
  have hr2 : 0 < r / 2 := half_pos hr
  have hmax : ∀ z : ℂ, 0 < max ‖z‖ (r / 2) := fun z => lt_max_of_lt_right hr2
  let g : C(ℂ, ℝ) := ⟨fun z => F (-Real.log (max ‖z‖ (r / 2))),
    hF.comp ((Real.continuousOn_log.comp_continuous (continuous_norm.max continuous_const)
      fun z => (hmax z).ne').neg)⟩
  have hev : ∀ᶠ n : ℕ in atTop, (2 : ℝ)⁻¹ ^ n ≤ r / 2 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (Iic_mem_nhds hr2)
  have hlim : Tendsto (fun n => CircleAvg.mollAvg (ofCont g) n 0 r) atTop
      (𝓝 (F (-Real.log r))) := by
    have h := CircleAvg.tendsto_mollAvg_ofCont g r 0
    have hc : Real.circleAverage (⇑g) 0 r = F (-Real.log r) := by
      apply Real.circleAverage_const_on_circle
      intro x hx
      rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hx
      show F (-Real.log (max ‖x‖ (r / 2))) = _
      rw [hx, max_eq_left (by linarith)]
    rwa [hc] at h
  refine hlim.congr' ?_
  filter_upwards [hev] with n hn
  unfold CircleAvg.mollAvg
  apply Real.circleAverage_congr_sphere
  intro x hx
  rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hx
  refine (ofFunC_bumpTest_eq g.continuous.locallyIntegrable hf (δ := r / 2) (fun y hy => ?_) hn)
  have hy' : r / 2 < ‖y‖ := by
    have := norm_sub_norm_le x y
    rw [← dist_eq_norm, dist_comm] at this
    linarith
  show F (-Real.log (max ‖y‖ (r / 2))) = f y
  rw [hfF y, max_eq_left hy'.le]

/-- **circle averages of the cone field** (DMS Def 4.10): the circle average of
`coneField y A Q` at radius `r` is that of `y` plus the radial value `Q(−log r) + A(−log r)` -/
theorem circleAvg_coneField {y : Field} {A : ℝ → ℝ} {Q : ℝ} (hA : Continuous A)
    (hloc : LocallyIntegrable (fun z : ℂ => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖)) volume)
    {r : ℝ} (hr : 0 < r) {a : ℝ}
    (hy : Tendsto (fun n => CircleAvg.mollAvg y n 0 r) atTop (𝓝 a)) :
    circleAvg (coneField y A Q) r 0 = a + (Q * (-Real.log r) + A (-Real.log r)) := by
  apply CircleAvg.circleAvg_eq_of_tendsto
  have hsplit : ∀ n, CircleAvg.mollAvg (coneField y A Q) n 0 r =
      CircleAvg.mollAvg y n 0 r + CircleAvg.mollAvg
        (ofFunC fun z : ℂ => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖)) n 0 r := by
    intro n
    simp only [CircleAvg.mollAvg_eq, coneField, ContinuousLinearMap.add_apply]
  simp_rw [hsplit]
  exact hy.add (tendsto_mollAvg_radial (F := fun t => Q * t + A t)
    ((continuous_const.mul continuous_id).add hA) hloc (fun z => rfl) hr)

/-- at radius `e^{-t}`: the circle average of the cone field is `Q t + A_t` plus that of `y` -/
theorem circleAvg_coneField_exp {y : Field} {A : ℝ → ℝ} {Q : ℝ} (hA : Continuous A)
    (hloc : LocallyIntegrable (fun z : ℂ => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖)) volume)
    (t : ℝ) {a : ℝ}
    (hy : Tendsto (fun n => CircleAvg.mollAvg y n 0 (Real.exp (-t))) atTop (𝓝 a)) :
    circleAvg (coneField y A Q) (Real.exp (-t)) 0 = a + (Q * t + A t) := by
  rw [circleAvg_coneField hA hloc (Real.exp_pos _) hy, Real.log_exp, neg_neg]

end ConeCirc

end MatedCRTHarmonic.MoTPort

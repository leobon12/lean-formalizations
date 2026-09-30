import QuantumZipper.Proofs.Thm18.G3Za2
import QuantumZipper.Proofs.Thm18.G3Cv2Trans
import QuantumZipper.Proofs.LQG.PalmNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (b), layer 3: translating the Palm field to the zoom point

Under the Palm law the field is `PalmNorm.normAt S (ofFun f₀ + V)` with `V` free and `f₀` singular like
`γ(−log |· − x|)` at the Palm point `x ∈ ℝ` (`G3WedgePalmIdStmt`); the zoom reads it through
`translate · x` (`zoomFieldVia`), a second regularization. Almost surely, near `0`,

  `translate (PalmNorm.normAt S (ofFun f₀ + V)) x`  agrees with
  `addConst (ofFun (f₀(· + x)) + rawTranslate V x) (−(ofFun f₀ + V)(S))`

at every dyadic folded circle (`ae_agreeNear_translate_palm`), circles whose translate passes
through the singularity included. So the zoom of the Palm field is the zoom of a translated
free field plus the profile `f₀(· + x)`, which has its `γ(−log ‖·‖)` singularity at `0`,
normalized by a raw value at `S`: the input of `G3Za.exists_g0Setup_palm`. Constants are
handled through `evalReg_addConst_ofFun_add_logSing`. Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

open G3Cv

theorem integrable_fc_logSing {a p ρ : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (p : ℂ) ρ ∩ Hbar, f u = a * -Real.log ‖u - p‖ + h u)
    (hh : Continuous h) {c : ℂ} {s : ℝ} (hs : 0 < s) (hcs : ‖c - p‖ + s ≤ ρ) :
    Integrable f (foldedCircle c s) := by
  have hnull := foldedCircle_compl_null (b := p) hs hcs
  have hae := ae_mem_of_compl_null_g3cv hnull
  refine (((integrable_log_norm_sub_fc c s p).neg.const_mul a).add
    (K3.integrable_of_continuousOn_closedBall_Hbar hh.continuousOn hnull)).congr ?_
  filter_upwards [hae] with u hu
  exact (hf u hu).symm

/-- Adding a constant commutes with the dyadic circle averages near the singularity. -/
theorem avgReg_addConst_ofFun_add {x : FieldSample} {a p ρ : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (p : ℂ) ρ ∩ Hbar, f u = a * -Real.log ‖u - p‖ + h u)
    (hh : Continuous h) (c : ℝ) {k : ℕ} {w : ℂ} (hw : ‖w - p‖ + radius k < ρ) :
    avgReg (addConst (ofFun f + x) c) k w = avgReg (ofFun (fun u => f u + c) + x) k w := by
  unfold avgReg
  apply D3Plus.limUnder_congr_eventually
  have hd := RegClosure.tendsto_dyadicRoundC w
  have hev : ∀ᶠ n in atTop, ‖dyadicRoundC n w - p‖ + radius k ≤ ρ := by
    have : Tendsto (fun n => ‖dyadicRoundC n w - p‖ + radius k) atTop
        (𝓝 (‖w - p‖ + radius k)) := ((hd.sub_const _).norm).add_const _
    exact (this.eventually (gt_mem_nhds hw)).mono fun n hn => hn.le
  filter_upwards [hev] with n hn
  have hi := integrable_fc_logSing hf hh (radius_pos k) hn
  simp only [addConst, Pi.add_apply, ofFun, measure_univ, ENNReal.toReal_one, mul_one]
  rw [integral_add hi (integrable_const c), integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  ring

/-- **Regularized evaluation of `addConst (ofFun f + x) c`** near the singularity. -/
theorem evalReg_addConst_ofFun_add_logSing {x : FieldSample} (hx : RegCont.RegAvgGood x)
    {a p ρ ρ₁ : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (p : ℂ) ρ ∩ Hbar, f u = a * -Real.log ‖u - p‖ + h u)
    (hh : Continuous h) (hρ₁ : ρ₁ < ρ) (c : ℝ) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ w ∂ν, w ∈ closedBall (p : ℂ) ρ₁ ∩ Hbar) (hνp : ∀ᵐ w ∂ν, w ≠ (p : ℂ))
    (hlog : Integrable (fun w : ℂ => Real.log ‖w - (p : ℂ)‖) ν) {A : ℝ}
    (hA : Tendsto (fun k => ∫ w, avgReg x k w ∂ν) atTop (𝓝 A)) :
    evalReg (addConst (ofFun f + x) c) ν = ∫ w, f w ∂ν + c + A := by
  have hf' : ∀ u ∈ closedBall (p : ℂ) ρ ∩ Hbar,
      (fun u => f u + c) u = a * -Real.log ‖u - p‖ + (fun u => h u + c) u := by
    intro u hu; simp only [hf u hu]; ring
  have h2 := evalReg_ofFun_add_logSing hx hf' (hh.add continuous_const) hρ₁ hν hνp hlog hA
  have hcongr : evalReg (addConst (ofFun f + x) c) ν = evalReg (ofFun (fun u => f u + c) + x) ν := by
    unfold evalReg
    apply D3Plus.limUnder_congr_eventually
    have hk : ∀ᶠ k in atTop, radius k < ρ - ρ₁ :=
      (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
        (gt_mem_nhds (by linarith))
    filter_upwards [hk] with k hk
    refine integral_congr_ae (hν.mono fun w hw => ?_)
    have hwp : ‖w - p‖ ≤ ρ₁ := by
      have := hw.1; rwa [mem_closedBall, dist_eq_norm] at this
    exact avgReg_addConst_ofFun_add hf hh c (by linarith)
  have hnull : ν (closedBall (p : ℂ) ρ₁ ∩ Hbar)ᶜ = 0 := ae_iff.1 hν
  have hfi : Integrable f ν := by
    refine ((hlog.neg.const_mul a).add
      (K3.integrable_of_continuousOn_closedBall_Hbar hh.continuousOn hnull)).congr ?_
    filter_upwards [hν] with u hu
    exact (hf u ⟨closedBall_subset_closedBall hρ₁.le hu.1, hu.2⟩).symm
  rw [hcongr, h2, integral_add hfi (integrable_const c), integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul]

/-- **The translated Palm field near `0`** (a.s., at every dyadic circle). -/
theorem ae_agreeNear_translate_palm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {V : Ω → FieldSample} (hV : IsFreeGFFModConstH V P)
    {a x ρf ρ₁ : ℝ} {f₀ h₀ : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (x : ℂ) ρf ∩ Hbar, f₀ u = a * -Real.log ‖u - x‖ + h₀ u)
    (hh : Continuous h₀) (hfm : Measurable f₀) (hρ₁ : ρ₁ < ρf) (S : Measure ℂ) :
    ∀ᵐ ω ∂P, D3Plus.AgreeNear (translate (PalmNorm.normAt S (ofFun f₀ + V ω)) (x : ℂ))
      (addConst (ofFun (fun u => f₀ (u + x)) + rawTranslate (V ω) x)
        (-((ofFun f₀ + V ω) S))) ρ₁ := by
  have hc : ∀ n : ℕ, (Set.range (dyadicRoundC n)).Countable := fun n => by
    have hsub : Set.range (dyadicRoundC n) ⊆
        Set.range (fun p : ℤ × ℤ =>
          (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
      rintro _ ⟨z, rfl⟩
      exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
    exact (Set.countable_range _).mono hsub
  have hreg : ∀ᵐ ω ∂P, RegCont.RegAvgGood (V ω) :=
    ae_all_iff.2 fun k => FrostmanReg.ae_circleAvg_tendsto_frostman hV k
  have hall : ∀ᵐ ω ∂P, ∀ n k, ∀ d ∈ Set.range (dyadicRoundC n),
      Tendsto (fun j => ∫ w, avgReg (V ω) j w ∂foldedCircle (d + x) (radius k)) atTop
        (𝓝 (V ω (foldedCircle (d + x) (radius k)))) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    rw [ae_ball_iff (hc n)]
    intro d _
    have h := ae_tendsto_avgReg_pullCircle hV (pullData_id (d + x) (radius k) (radius_pos k))
      (c := d + x) (radius_pos k) (by simp)
    simpa [pullCircle, Measure.map_id] using h
  filter_upwards [hreg, hall] with ω hreg hω n k z hz
  set d := dyadicRoundC n z
  have hk0 := radius_pos k
  have hdx : ‖(d + x) - x‖ + radius k ≤ ρ₁ := by simp only [add_sub_cancel_right]; linarith
  have hν : ∀ᵐ w ∂foldedCircle (d + x) (radius k), w ∈ closedBall (x : ℂ) ρ₁ ∩ Hbar :=
    ae_mem_of_compl_null_g3cv (foldedCircle_compl_null (b := x) hk0 hdx)
  have hνp : ∀ᵐ w ∂foldedCircle (d + x) (radius k), w ≠ (x : ℂ) := by
    rw [ae_iff]; simpa using FoldBound.fb_fc_singleton (d + x) hk0.ne' (x : ℂ)
  have hmain := evalReg_addConst_ofFun_add_logSing hreg hf hh hρ₁ (-((ofFun f₀ + V ω) S)) hν hνp
    (integrable_log_norm_sub_fc _ _ x) (hω n k d ⟨z, rfl⟩)
  have hmap : (foldedCircle d (radius k)).map (· + (x : ℂ)) = foldedCircle (d + x) (radius k) :=
    IndepParams.fc_map_add_real d (radius k) x
  show evalReg (PalmNorm.normAt S (ofFun f₀ + V ω)) ((foldedCircle d (radius k)).map (· + (x : ℂ))) = _
  rw [hmap]
  simp only [PalmNorm.normAt] at *
  rw [hmain]
  simp only [addConst, Pi.add_apply, ofFun, rawTranslate, measure_univ, ENNReal.toReal_one,
    mul_one, hmap]
  have e : ∫ u, f₀ (u + (x : ℂ)) ∂foldedCircle d (radius k) =
      ∫ u, f₀ u ∂foldedCircle (d + x) (radius k) := by
    rw [← hmap, integral_map (by fun_prop) hfm.aestronglyMeasurable]
  rw [e]
  ring

end G3Za
end QuantumZipper

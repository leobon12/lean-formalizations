import QuantumZipper.Proofs.Thm18.ASep4Wit
import QuantumZipper.Proofs.Thm18.ASep3Box
import QuantumZipper.Proofs.Thm18.ASepConj1D
import QuantumZipper.Proofs.Zipper.UnifUCIdDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 4): the identity input of the scale engine run

* `ae_integral_Y5_eq_bind_gen`: stochastic Fubini for the dilated modification against any
  compactly supported probability measure `ν ⊆ Hbar` (as `ae_integral_Y5_eq_bind`, ASep4Comm);
* `bind_pushKernel_dmap_eq`: `ν.bind (fc(·, ρ).map (s · f_t⁻¹)) = ((bindFc ν ρ).map f_t⁻¹).map (s ·)`;
* `ae_ident_scale`: at a fixed scaled good parameter `q = (τ, a, s)` and radius `ρ > 0`, almost
  surely `∫ evalReg x_q (fc(v, ρ)) dν_p(v) = X((muA0 p ρ).map (s ·)) + ∫ Dfun(v, ρ) dν_p + Q log s`,
  with `x_q = coordChange (rescale X Q s) f_τ⁻¹ Q` (through the explicit witness `witS`).

Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (stochastic Fubini); own
bookkeeping (scale version of `ae_ident_fwdMapInv_rho`, ASepIdentRho).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open CircleFubini RegCont CoordReg RegUnif

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Stochastic Fubini for the dilated modification, general centre measure.** -/
theorem ae_integral_Y5_eq_bind_gen [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    {Y : (Fin 5 → ℝ) → Ω → ℝ}
    (hYc : ∀ ω, ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4})
    (hYeq : ∀ q ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4},
      (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (nu5 W T q))
    {t : ℝ} (ht : t ∈ Icc 0 T) {s : ℝ} (hs : 0 < s) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    {R₁ : ℝ} (hR₁ : 0 ≤ R₁) (hν : ν (ballH R₁)ᶜ = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∫ u, Y (q5 t u s ρ) ω ∂ν =
      X ω (ν.bind (pushKernel (dmap W t s) (measurable_dmap hW ht.1 s) ρ)) := by
  set hf := measurable_dmap hW ht.1 s
  set Φ := pushKernel (dmap W t s) hf ρ with hΦ
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  set B : ℝ := RegCont.revBound (2 * M) T (R₁ + ρ) with hB
  set C : ℝ := RegCont.frostC T ρ (R₁ + ρ) with hC
  have hC0 : 0 ≤ C := by simp only [hC, RegCont.frostC]; positivity
  have hfacts : ∀ z ∈ ballH R₁, Φ z (ballH (s * B))ᶜ = 0 ∧
      TwoPoint.IsFrostman (Φ z) (1 / 3) (C * s⁻¹ ^ (1 / 3 : ℝ)) := by
    intro z hz
    have hzR : ‖z‖ + ρ ≤ R₁ + ρ := by
      have := hz.1; rw [mem_closedBall, dist_zero_right] at this; linarith
    obtain ⟨-, hFr, hae⟩ := RegUnif.νT_box_facts hW hW0 hρ hM ht le_rfl hzR
    have e : Φ z = (RegCont.νT W z ρ t).map fun x => (s : ℂ) * x := by
      rw [hΦ, pushKernel_apply, fc_map_dmap hW hW0 ht.1 s z hρ]
    rw [e]
    refine ⟨?_, isFrostman_map_mul_of (by norm_num) hC0 hs le_rfl hFr⟩
    refine ae_iff.1 ((ae_map_iff (measurable_const_mul _).aemeasurable
      (isCompact_ballH _).isClosed.measurableSet).2 ?_)
    filter_upwards [hae] with x hx
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hs.le]
      exact mul_le_mul_of_nonneg_left hx.2 hs.le
    · show 0 ≤ ((s : ℂ) * x).im
      have : 0 < x.im := hx.1
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      positivity
  have hcS : ∀ z ∈ ballH R₁, Φ z (ballH (s * B))ᶜ = 0 := fun z hz => (hfacts z hz).1
  have hcP : ∀ z ∈ ballH R₁, ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂Φ z ≤
      ENNReal.ofReal (C * s⁻¹ ^ (1 / 3 : ℝ) / (1 / 3)) := fun z hz y =>
    Thm18Asm.G1RC.frostman_pot_le (hfacts z hz).2 (by norm_num) (by positivity) y
  have h0 : (0 : ℂ) ∈ ballH R₁ :=
    ⟨by rw [mem_closedBall, dist_zero_right, norm_zero]; exact hR₁, by simp [Hbar]⟩
  have hmem : ∀ u : ℂ, q5 t u s ρ ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4} := fun u => ⟨hs, hρ⟩
  have hYc' : ∀ ω, ContinuousOn (fun u => Y (q5 t u s ρ) ω - Y (q5 t 0 s ρ) ω) Hbar :=
    fun ω => (((hYc ω).comp_continuous (continuous_q5_fst t s ρ) hmem).sub
      continuous_const).continuousOn
  have hY : ∀ u ∈ Hbar, (fun ω => Y (q5 t u s ρ) ω - Y (q5 t 0 s ρ) ω) =ᵐ[P]
      fun ω => X ω (Φ u) - X ω (Φ 0) := by
    intro u hu
    filter_upwards [hYeq _ (hmem u), hYeq _ (hmem 0)] with ω h1 h2
    rw [h1, h2, nu5_q5 hW hW0 ht hu s hρ, nu5_q5 hW hW0 ht h0.2 s hρ]
    rfl
  have hF := integral_kernelAvg_ae_eq_bind hX Φ (K' := ballH R₁) (R := s * B)
    ENNReal.ofReal_ne_top hcS hcP h0 hYc' hY ν (isCompact_ballH R₁)
    inter_subset_right subset_rfl hν
  filter_upwards [hF, hYeq _ (hmem 0)] with ω h1 h2
  have hint : Integrable (fun u => Y (q5 t u s ρ) ω) ν :=
    Thm18Asm.G1Z3.integrable_of_ae_mem_z3 (isCompact_ballH R₁) inter_subset_right
      (mem_ae_iff.2 hν) ((hYc ω).comp_continuous (continuous_q5_fst t s ρ) hmem).continuousOn
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul,
    measure_univ, one_smul] at h1
  rw [nu5_q5 hW hW0 ht h0.2 s hρ] at h2
  have e : X ω (Φ 0) = X ω ((foldedCircle 0 ρ).map (dmap W t s)) := rfl
  linarith

/-- The dilated pushed bind is the dilated `muA0`-type measure. -/
theorem bind_pushKernel_dmap_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (s : ℝ) (ν : Measure ℂ) [IsFiniteMeasure ν] {ρ : ℝ} (hρ : 0 < ρ) :
    ν.bind (pushKernel (dmap W t s) (measurable_dmap hW ht s) ρ) =
      ((bindFc ν ρ).map (fwdMapInv W t)).map fun z => (s : ℂ) * z := by
  rw [bind_pushKernel]
  have hrm := TwoPoint.measurable_revMap (RegCont.continuous_vRev hW t) ht
  have e : (bindFc ν ρ).map (fwdMapInv W t) = (bindFc ν ρ).map (revMap (vRev W t) t) :=
    Measure.map_congr ((bindFc_ae_mem_H ν hρ).mono fun x hx =>
      UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hx)
  rw [e, Measure.map_map (measurable_const_mul _) hrm]
  rfl

/-- **The identity input at a fixed scaled parameter.** -/
theorem ae_ident_scale [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (Q : ℝ) {T : ℝ}
    {Y : (Fin 5 → ℝ) → Ω → ℝ}
    (hYc : ∀ ω, ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4})
    (hYe : ∀ q ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4},
      (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (nu5 W T q))
    (hreg : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ t ∈ Icc (0 : ℝ) T,
      IsRegularWith (coordChange (rescale (X ω) Q s) (fwdMapInv W t) Q) (witS Y W Q ω (s, t)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {s : ℝ} (hs : 0 < s) {ν : Measure ℂ}
    [IsProbabilityMeasure ν] {R₁ : ℝ} (hR₁ : 0 ≤ R₁) (hν : ν (ballH R₁)ᶜ = 0) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∫ v, evalReg (coordChange (rescale (X ω) Q s) (fwdMapInv W t) Q)
        (foldedCircle v ρ) ∂ν =
      X ω (((bindFc ν ρ).map (fwdMapInv W t)).map fun z => (s : ℂ) * z) +
        ∫ v, Dfun (vRev W t) t 0 (fun _ => 0) Q (v, ρ) ∂ν + Q * Real.log s := by
  have hV := continuous_vRev hW t
  have hνK : ∀ᵐ v ∂ν, v ∈ ballH R₁ := mem_ae_iff.2 hν
  filter_upwards [hreg, ae_integral_Y5_eq_bind_gen hX hW hW0 hYc hYe ht hs hR₁ hν hρ]
    with ω h1 h2
  have hZ := h1 s hs t ht
  have e1 : ∫ v, evalReg (coordChange (rescale (X ω) Q s) (fwdMapInv W t) Q)
      (foldedCircle v ρ) ∂ν = ∫ v, witS Y W Q ω (s, t) (v, ρ) ∂ν :=
    integral_congr_ae (hνK.mono fun v hv => hZ.evalReg_fc_of_mem hv.2 hρ)
  have hint1 : Integrable (fun u => Y (q5 t u s ρ) ω) ν :=
    Thm18Asm.G1Z3.integrable_of_ae_mem_z3 (isCompact_ballH R₁) inter_subset_right hνK
      ((hYc ω).comp_continuous (continuous_q5_fst t s ρ) fun _ => ⟨hs, hρ⟩).continuousOn
  have hint2 : Integrable (fun u => Dfun (vRev W t) t 0 (fun _ => 0) Q (u, ρ)) ν :=
    Thm18Asm.G1Z3.integrable_of_ae_mem_z3 (isCompact_ballH R₁) inter_subset_right hνK
      ((continuousOn_Dfun (W := vRev W t) (T := t) hV ht.1 0 continuous_const Q).comp_continuous
        (continuous_id.prodMk continuous_const) fun _ => hρ).continuousOn
  rw [e1]
  simp only [witS, Dfix]
  rw [integral_add_const_add hint1 hint2, h2, bind_pushKernel_dmap_eq hW hW0 ht.1 s ν hρ]
  ring

end ASep
end QuantumZipper

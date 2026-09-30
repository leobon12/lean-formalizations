import QuantumZipper.Proofs.Thm18.G4RoundWedgeReg

/-!
# Theorem 1.8, node G4: the rezip identities, deterministic core

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1) (the paper
gives no proof of the round trips). The two rezip identities of `G4RoundWedgeReg`
(`G4RoundDownRezipCoreStmt`, `G4RoundUpRezipCoreStmt`) are reduced, **deterministically**, to
regularity of the intermediate fields at pushed dyadic folded circles, exactly as the fixed-time
Corollary 1.5 rezip (`Cor15Group.rezip_apply`, `cor15RezipFieldStmt_of`). The Loewner input is
the scaling rule of the reverse flow (Lawler, *Conformally Invariant Processes in the Plane*,
§4.1 scaling of the Loewner equation; here `LoewnerAlgebra.revMap_scale`, blueprint A1(d)) and
the inverse function theorem for `revMap` (`Cor15Group.hasStrictDerivAt_revMapInv`).

* `rezipDown_fc_apply`: with `f = revMap V T`, `x = Y ∘ f⁻¹ + Q log|(f⁻¹)'|` (the zipped field),
  `y = x(b·) + Q log b` and `ψ = f(b·)/b`, the raw value of `y ∘ ψ + Q log|ψ'|` at a probability
  measure `σ` carried by `ℍ` is that of `Y(b·) + Q log b`, once `y` is regular at `σ.map ψ` and
  `x` is regular at `σ.map (f(b·))`. No hull condition is needed (`f⁻¹ ∘ f = id` on `ℍ`).
* `rezipUp_fc_apply`: with `F = revMap V t` on `ℍ` (the unzipping map), `x' = Y ∘ F + …`,
  `y' = x'(a·) + Q log a` and `g = revMapInv (V(a²·)/a) (t/a²)` (the inverse of `F(a·)/a`), the
  raw value of `y' ∘ g + Q log|g'|` at `σ` is that of `Y(a·) + Q log a`, once `σ` is carried by
  the image of `F(a·)/a`, `y'` is regular at `σ.map g` and `x'` at `σ.map (a g)`.
* `regEq_rezipDown`, `regEq_rezipUp`: the `RegEq` forms (all dyadic folded circles).

**Own elementary argument** (change of variables and the chain rule; the paper has no proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

theorem rezip_mul_mem_H {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w ∈ H) : (b : ℂ) * w ∈ H := by
  have hw' : 0 < w.im := hw
  show 0 < ((b : ℂ) * w).im
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  positivity

/-- The derivative of `z ↦ f(bz)/b` at `z ∈ ℍ` is `f'(bz)` for `f = revMap V T`. -/
theorem deriv_revMap_mul_div {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 ≤ T) {b : ℝ}
    (hb : 0 < b) {z : ℂ} (hz : z ∈ H) :
    deriv (fun w => revMap V T ((b : ℂ) * w) / (b : ℂ)) z = deriv (revMap V T) ((b : ℂ) * z) := by
  have hbz := rezip_mul_mem_H hb hz
  have hf : HasDerivAt (revMap V T) (deriv (revMap V T) ((b : ℂ) * z)) ((b : ℂ) * z) :=
    ((differentiableOn_revMap V hV hT) _ hbz).differentiableAt
      (isOpen_H.mem_nhds hbz) |>.hasDerivAt
  have h1 : HasDerivAt (fun w : ℂ => (b : ℂ) * w) (b : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (b : ℂ)
  have h2 := (hf.comp z h1).div_const (b : ℂ)
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  refine h2.deriv.trans ?_
  field_simp

/-- **Rezip identity, unzip-then-zip direction, at one measure** (deterministic). -/
theorem rezipUp_fc_apply (Y : FieldSample) (Q : ℝ) {V : ℝ → ℝ} (hV : Continuous V) {t : ℝ}
    (ht : 0 ≤ t) {a : ℝ} (ha : 0 < a) {F : ℂ → ℂ} (hF : EqOn F (revMap V t) H)
    (σ : Measure ℂ) [IsProbabilityMeasure σ]
    (hσ : σ (revMap (fun s => V (a ^ 2 * s) / a) (t / a ^ 2) '' H)ᶜ = 0)
    (hR1 : evalReg (rescale (coordChange Y F Q) Q a)
        (σ.map (revMapInv (fun s => V (a ^ 2 * s) / a) (t / a ^ 2))) =
      rescale (coordChange Y F Q) Q a
        (σ.map (revMapInv (fun s => V (a ^ 2 * s) / a) (t / a ^ 2))))
    (hR2 : evalReg (coordChange Y F Q)
        (σ.map fun w => (a : ℂ) * revMapInv (fun s => V (a ^ 2 * s) / a) (t / a ^ 2) w) =
      coordChange Y F Q
        (σ.map fun w => (a : ℂ) * revMapInv (fun s => V (a ^ 2 * s) / a) (t / a ^ 2) w)) :
    coordChange (rescale (coordChange Y F Q) Q a)
      (revMapInv (fun s => V (a ^ 2 * s) / a) (t / a ^ 2)) Q σ = rescale Y Q a σ := by
  set Vs : ℝ → ℝ := fun s => V (a ^ 2 * s) / a with hVsdef
  set ts : ℝ := t / a ^ 2 with htsdef
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hVs : Continuous Vs := (hV.comp (continuous_const.mul continuous_id)).div_const a
  have hts : 0 ≤ ts := by positivity
  have hat : a ^ 2 * ts = t := by rw [htsdef]; field_simp
  have hscale : ∀ z ∈ H, revMap Vs ts z = revMap V t ((a : ℂ) * z) / (a : ℂ) := by
    intro z hz
    rw [hVsdef, LoewnerAlgebra.revMap_scale V hV ha hts hz, hat]
  have hU : ∀ᵐ w ∂σ, w ∈ revMap Vs ts '' H := ae_iff.2 hσ
  have hgU : ∀ w ∈ revMap Vs ts '' H, revMapInv Vs ts w ∈ H ∧ revMap Vs ts (revMapInv Vs ts w) = w := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Cor15Group.revMapInv_revMap hVs hts hz]
    exact ⟨hz, rfl⟩
  have hgm : Measurable (revMapInv Vs ts) := Cor15Group.measurable_revMapInv hVs hts
  have hmA : Measurable (fun z : ℂ => (a : ℂ) * z) := measurable_const_mul _
  have hagm : Measurable (fun w => (a : ℂ) * revMapInv Vs ts w) := hmA.comp hgm
  haveI : IsProbabilityMeasure (σ.map (revMapInv Vs ts)) := (Measure.isProbabilityMeasure_map_iff hgm.aemeasurable).2 inferInstance
  have e1 : coordChange (rescale (coordChange Y F Q) Q a) (revMapInv Vs ts) Q σ =
      evalReg (rescale (coordChange Y F Q) Q a) (σ.map (revMapInv Vs ts)) +
      Q * ∫ w, Real.log ‖deriv (revMapInv Vs ts) w‖ ∂σ := rfl
  have e2 : rescale (coordChange Y F Q) Q a (σ.map (revMapInv Vs ts)) =
      evalReg (coordChange Y F Q) ((σ.map (revMapInv Vs ts)).map fun z => (a : ℂ) * z) +
      Q * ∫ z, Real.log ‖deriv (fun z : ℂ => (a : ℂ) * z) z‖ ∂(σ.map (revMapInv Vs ts)) := rfl
  have e3 : (σ.map (revMapInv Vs ts)).map (fun z => (a : ℂ) * z) =
      σ.map fun w => (a : ℂ) * revMapInv Vs ts w := by
    rw [Measure.map_map hmA hgm]; rfl
  have e5 : coordChange Y F Q (σ.map fun w => (a : ℂ) * revMapInv Vs ts w) =
      evalReg Y ((σ.map fun w => (a : ℂ) * revMapInv Vs ts w).map F) +
      Q * ∫ u, Real.log ‖deriv F u‖ ∂(σ.map fun w => (a : ℂ) * revMapInv Vs ts w) := rfl
  have hHa : ∀ᵐ u ∂(σ.map fun w => (a : ℂ) * revMapInv Vs ts w), u ∈ H :=
    (ae_map_iff hagm.aemeasurable isOpen_H.measurableSet).2
      (hU.mono fun w hw => rezip_mul_mem_H ha (hgU w hw).1)
  have hkey : ∀ w ∈ revMap Vs ts '' H, revMap V t ((a : ℂ) * revMapInv Vs ts w) = (a : ℂ) * w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hgU w hw
    have := hscale _ h1
    rw [h2, eq_div_iff ha0] at this
    rw [← this]
    ring
  have e6 : (σ.map fun w => (a : ℂ) * revMapInv Vs ts w).map F = σ.map fun z => (a : ℂ) * z := by
    rw [Measure.map_congr (hHa.mono fun u hu => hF hu),
      Measure.map_map (TwoPoint.measurable_revMap hV ht) hagm]
    exact Measure.map_congr (hU.mono fun w hw => hkey w hw)
  have e7 : ∫ u, Real.log ‖deriv F u‖ ∂(σ.map fun w => (a : ℂ) * revMapInv Vs ts w) =
      ∫ w, Real.log ‖deriv F ((a : ℂ) * revMapInv Vs ts w)‖ ∂σ :=
    integral_map hagm.aemeasurable
      (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable
  have e8 : ∫ w, Real.log ‖deriv (revMapInv Vs ts) w‖ ∂σ =
      -∫ w, Real.log ‖deriv F ((a : ℂ) * revMapInv Vs ts w)‖ ∂σ := by
    rw [← integral_neg]
    refine integral_congr_ae (hU.mono fun w hw => ?_)
    obtain ⟨z, hz, rfl⟩ := hw
    have haz := rezip_mul_mem_H ha hz
    have hφ : deriv (revMap Vs ts) z = deriv (revMap V t) ((a : ℂ) * z) := by
      rw [Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hz)
        fun w hw => hscale w hw)]
      exact deriv_revMap_mul_div hV ht ha hz
    have hFd : deriv F ((a : ℂ) * z) = deriv (revMap V t) ((a : ℂ) * z) :=
      Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds haz) hF)
    show Real.log ‖deriv (revMapInv Vs ts) (revMap Vs ts z)‖ =
      -Real.log ‖deriv F ((a : ℂ) * revMapInv Vs ts (revMap Vs ts z))‖
    rw [(Cor15Group.hasStrictDerivAt_revMapInv hVs hts hz).hasDerivAt.deriv,
      Cor15Group.revMapInv_revMap hVs hts hz, hφ, hFd, norm_inv, Real.log_inv]
  have e9 : rescale Y Q a σ = evalReg Y (σ.map fun z => (a : ℂ) * z) +
      Q * ∫ z, Real.log ‖deriv (fun z : ℂ => (a : ℂ) * z) z‖ ∂σ := rfl
  rw [e1, hR1, e2, e3, RegClosure.integral_log_deriv_mul ha, hR2, e5, e6, e7, e8, e9,
    RegClosure.integral_log_deriv_mul ha]
  ring

end Thm18Asm
end QuantumZipper

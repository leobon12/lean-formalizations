import SupercriticalConformalCovariance.Tangent.Main
import SupercriticalConformalCovariance.ZBConformal.Pullback

/-!
# Lemma 3.3, step 1: the smooth normalization

Paper l. 206–207: "Fix a smooth radial test function `f` of integral one and normalize `h` by
`(h, f) = 0`. Changing between fixed normalizations is harmless by Weyl scaling."

* `subseqLSC_of_mul`: convergence in probability is invariant under multiplying sequence and limit by
  one random factor `κ ∈ (0, ∞)`;
* `isDomainRealization_addConst`: subtracting a random constant from `h` subtracts it from the
  realization of every transformed field `h^{ψ}` (the conformal transport preserves integrals).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric Function
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open LQGMetric (DistC DistOn TestOn TestC restrictTo addFun addConst ofCont IsGFFPlusCont
  IsWholePlaneGFF)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric LSCTendsto)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest confPullbackField
  IsDomainRealization)

/-- **Scaling invariance of the convergence.** -/
theorem subseqLSC_of_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (κ : Ω → ℝ≥0∞)
    (hκ : ∀ᵐ ω ∂P, κ ω ≠ 0 ∧ κ ω ≠ ⊤) {F : ℕ → Ω → ℂ × ℂ → ℝ≥0∞} {L : Ω → ℂ × ℂ → ℝ≥0∞}
    (h : SubseqLSC P (fun n ω q => ((κ ω * F n ω q : ℝ≥0∞) : EReal))
      (fun ω q => ((κ ω * L ω q : ℝ≥0∞) : EReal))) :
    SubseqLSC P (fun n ω q => (F n ω q : EReal)) (fun ω q => (L ω q : EReal)) := by
  intro ns hns
  obtain ⟨ms, hms, hae⟩ := h ns hns
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae, hκ] with ω hω hκω
  have hinv0 : (κ ω)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hκω.2
  have hinvt : (κ ω)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hκω.1
  have hcancel : ∀ x : ℝ≥0∞, (κ ω)⁻¹ * (κ ω * x) = x := fun x => by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hκω.1 hκω.2, one_mul]
  have := lscTendsto_mul_sandwich (F := fun k q => F (ns (ms k)) ω q)
    (G := fun k q => κ ω * F (ns (ms k)) ω q) (G₀ := fun q => κ ω * L ω q) hω hinv0 hinvt
    tendsto_const_nhds tendsto_const_nhds
    (Eventually.of_forall fun k q => by simp only [hcancel]; exact ⟨le_rfl, le_rfl⟩)
  simpa only [hcancel] using this

/-- The conformal transport of test functions preserves integrals. -/
theorem integral_confPushTest {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
    (g : TestOn U) : ∫ y, confPushTest hφ g y = ∫ x, g x := by
  have := SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest hφ g (fun _ => 1)
  simpa using this

/-- **Shifting `h` by a random constant shifts the realizations.** -/
theorem isDomainRealization_addConst (Q : ℝ) {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ V U) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hhm : Measurable h) {hbar : Ω → DistC} {fr : Ω → C(V, ℝ)}
    (hreal : IsDomainRealization V P (fun ω => confPullbackField Q hφ (restrictTo U (h ω))) hbar fr)
    {c : Ω → ℝ} (hc : Measurable c) :
    IsDomainRealization V P (fun ω => confPullbackField Q hφ (restrictTo U (addConst (h ω) (c ω))))
      (fun ω => addConst (hbar ω) (c ω)) fr := by
  obtain ⟨hm, hgc, hfr, hae⟩ := hreal
  refine ⟨?_, SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst hgc hc,
    hfr, ?_⟩
  · refine LQGMetric.measurable_distOn_iff.2 fun g => ?_
    have e : (fun ω => confPullbackField Q hφ (restrictTo U (addConst (h ω) (c ω))) g) =
        fun ω => confPullbackField Q hφ (restrictTo U (h ω)) g + (∫ x, g x) * c ω := by
      funext ω
      simp only [confPullbackField, add_apply]
      change addConst (h ω) (c ω) _ + _ = h ω _ + _ + _
      rw [LQGMetric.GFFInv.addConst_apply]
      have hint : ∫ x, (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤)
          (confPushTest hφ g) : ℂ → ℝ) x = ∫ x, g x := by
        rw [SupercriticalConformalCovariance.Domain.coe_monoCLM le_top]
        exact integral_confPushTest hφ g
      simp only [ContinuousLinearMap.coe_coe] at hint ⊢
      rw [hint]
      ring
    rw [e]
    exact ((LQGMetric.measurable_distOn_apply g).comp hm).add (measurable_const.mul hc)
  · filter_upwards [hae] with ω hω
    ext g
    have h1 := congrArg (fun u : DistOn V => u g) hω
    simp only [confPullbackField, add_apply] at h1 ⊢
    change addConst (h ω) (c ω) _ + _ = addConst (hbar ω) (c ω) _ + _
    change h ω _ + _ = hbar ω _ + _ at h1
    rw [LQGMetric.GFFInv.addConst_apply, LQGMetric.GFFInv.addConst_apply]
    have hint : ∫ x, (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤)
        (confPushTest hφ g) : ℂ → ℝ) x = ∫ x, g x := by
      rw [SupercriticalConformalCovariance.Domain.coe_monoCLM le_top]
      exact integral_confPushTest hφ g
    have hint' : ∫ x, (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) g : ℂ → ℝ) x =
        ∫ x, g x := by
      rw [SupercriticalConformalCovariance.Domain.coe_monoCLM le_top]
    simp only [ContinuousLinearMap.coe_coe] at hint hint' h1 ⊢
    rw [hint, hint']
    linarith

end SupercriticalConformalCovariance.Tangent

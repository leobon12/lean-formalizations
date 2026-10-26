import SupercriticalConformalCovariance.BiLip.Port.FieldLocality

/-! Constant field shifts commute with conformal transport. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set TopologicalSpace Function
open scoped Distributions
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest confPullbackField)
open SmallGammaGeodesics.CC

namespace SupercriticalConformalCovariance.BiLip.PortT
open SupercriticalConformalCovariance.Transport

/-- A constant as a distribution on an open domain. -/
def constOn (V : Opens ℂ) (c : ℝ) : DistOn V :=
  Distribution.ofFun V (fun _ : ℂ => c) volume ⊤

theorem constOn_apply (V : Opens ℂ) (c : ℝ) (ψ : TestOn V) :
    constOn V c ψ = c * ∫ x, ψ x := by
  rw [constOn, Distribution.ofFun_apply
    (by exact (locallyIntegrable_const c).locallyIntegrableOn _)]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- A conformal push of tests preserves their integral. -/
theorem integral_confPushTest_eq {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : TestOn U) :
    ∫ y, (confPushTest hφ ψ) y = ∫ x, ψ x := by
  let inv := invFunOn φ (U : Set ℂ)
  have hψφ : ∀ x ∈ (U : Set ℂ), inv (φ x) = x :=
    fun _ hx => hφ.2.injOn.leftInvOn_invFunOn hx
  have hφψ : ∀ y ∈ (V : Set ℂ), φ (inv y) = y := by
    intro y hy
    exact apply_leftInv hψφ (hφ.2.image_eq.symm ▸ hy)
  have hdiff : DifferentiableOn ℂ inv V := by
    have h := differentiableOn_leftInv U.isOpen hφ.1 hφ.2.injOn hψφ
    rwa [hφ.2.image_eq] at h
  have hinj : InjOn inv V := by
    have h := injOn_leftInv hψφ
    rwa [hφ.2.image_eq] at h
  have himage : inv '' (V : Set ℂ) = (U : Set ℂ) := by
    rw [← hφ.2.image_eq, image_leftInv_image hψφ subset_rfl]
  have hzero : ∀ x ∉ inv '' (V : Set ℂ), (ψ : ℂ → ℝ) x = 0 := by
    intro x hx
    apply ψ.zero_on_compl
    rw [himage] at hx
    exact hx
  have h := integral_confPullFun_mul V.isOpen hdiff hinj hφψ hzero (fun _ => (1 : ℝ))
  change (∫ y, confPullFun inv V ψ y) = ∫ x, ψ x
  simpa only [one_mul, mul_one] using h

/-- The paper's forward transform sends a source constant shift to the same target constant shift. -/
theorem forward_add_const {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (Q c : ℝ) (h : DistOn U) :
    confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) (h + constOn U c) =
      confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) h + constOn V c := by
  ext ψ
  change (h + constOn U c) (confPushTest (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) ψ) + _ =
    h (confPushTest (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) ψ) + _ + constOn V c ψ
  rw [ContinuousLinearMap.add_apply, constOn_apply, constOn_apply,
    integral_confPushTest_eq (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) ψ]
  ring

theorem ext_const_eq_constOn (V : Opens ℂ) (c : ℝ) :
    Distribution.ofFun V
      (Function.extend Subtype.val (ContinuousMap.const V c) 0) volume ⊤ = constOn V c := by
  ext ψ
  have hloc : LocallyIntegrableOn
      (Function.extend Subtype.val (ContinuousMap.const V c) (0 : ℂ → ℝ)) V volume :=
    (SupercriticalConformalCovariance.Domain.continuousOn_extZ (ContinuousMap.const V c)).locallyIntegrableOn
      V.isOpen.measurableSet
  rw [Distribution.ofFun_apply hloc, constOn_apply]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ V
  · change ψ x * SupercriticalConformalCovariance.Domain.extZ (ContinuousMap.const V c) x = c * ψ x
    rw [SupercriticalConformalCovariance.Domain.extZ_of_mem (ContinuousMap.const V c) hx]
    simp [mul_comm]
  · have hz : ψ x = 0 := ψ.zero_on_compl hx
    simp [hz]

/-- A measurable random constant gives a valid realization of the shifted target field. -/
theorem isDomainRealization_forward_add_const {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (Q : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn U} {hbar₀ : Ω → LQGMetric.DistC}
    {fbar : Ω → C(V, ℝ)}
    (hR : SupercriticalConformalCovariance.IsDomainRealization V P
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ) (h ω)) hbar₀ fbar)
    {c : Ω → ℝ} (hc : Measurable c) :
    SupercriticalConformalCovariance.IsDomainRealization V P
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ)
        (h ω + constOn U (c ω))) hbar₀
      (fun ω => fbar ω + ContinuousMap.const V (c ω)) := by
  have hcm : Measurable (fun ω => ContinuousMap.const V (c ω)) := by
    have : LocallyCompactSpace (V : Set ℂ) := V.isOpen.locallyCompactSpace
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    exact hc
  have hR' := SupercriticalConformalCovariance.Domain.isDomainRealization_add hR hcm
  convert hR' using 1
  · funext ω
    rw [forward_add_const hφ Q (c ω) (h ω), ext_const_eq_constOn]

end SupercriticalConformalCovariance.BiLip.PortT

import SupercriticalConformalCovariance.Small.ZoomGeometry
import SupercriticalConformalCovariance.Reversal.Inverse
import SupercriticalConformalCovariance.BiLip.Port.Realize
import SupercriticalConformalCovariance.BiLip.Local

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Function MeasureTheory
open LQGMetric SupercriticalConformalCovariance
open SmallGammaGeodesics.CC (zoomMap zoomSet confPullFun confPullFun_of_mem confPullFun_of_notMem)

namespace SupercriticalConformalCovariance.Small

private theorem confPushTest_precomp_eval {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (d : DistOn V) (t : TestOn U) :
    ((confPushTest hφ).precompCompactConvergenceCLM ℝ d) t =
      d (confPushTest hφ t) := rfl

/-- Test-function transport commutes with the source and target affine zooms.
This is the distributional part of the zoomed realization square. -/
theorem confPushTest_zoom_square {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (t : TestOn (affinePreimage V (φ z) r)) :
    confPushTest (affinePreimage_conformal U z hr)
        (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr)) t) =
      confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
        (confPushTest (affinePreimage_conformal V (φ z) hr) t) := by
  let hψ := zoomConformal hφ z hr
  let hA := affinePreimage_conformal U z hr
  let hB := affinePreimage_conformal V (φ z) hr
  ext x
  have hr0 : r ≠ 0 := hr.ne'
  have hzset : (affinePreimage U z r : Set ℂ) = zoomSet z r U :=
    affinePreimage_eq_zoomSet U z r
  have hleft : (confPushTest hA
      (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hψ) t) : ℂ → ℝ) x =
      (r ^ 2)⁻¹ *
        confPullFun (zoomMap φ z r) (zoomSet z r U) t ((x - z) / r) := by
    rw [affine_confPushTest_apply U z hr]
    rw [testAffinePull_apply r z hr0]
    rw [SupercriticalConformalCovariance.Domain.coe_monoCLM le_top]
    rw [SupercriticalConformalCovariance.Reversal.confPushTest_inverse_eq_confPullFun hψ t]
    rw [hzset]
  have hright : (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
      (confPushTest hB t) : ℂ → ℝ) x =
      confPullFun φ U (confPushTest hB t) x :=
    congrFun (SupercriticalConformalCovariance.Reversal.confPushTest_inverse_eq_confPullFun hφ
      (confPushTest hB t)) x
  rw [hleft, hright]
  have hzoom := SmallGammaGeodesics.CC.confPullFun_zoomMap
    (ϕ := φ) (z := z) (r := r) hr0 U.isOpen hφ.1 (t : ℂ → ℝ) x
  rw [hzoom]
  by_cases hx : x ∈ (U : Set ℂ)
  · rw [confPullFun_of_mem hx, confPullFun_of_mem hx]
    have hφx : φ x ∈ (V : Set ℂ) := hφ.2.mapsTo hx
    have hBt := affine_confPushTest_apply V (φ z) hr t (φ x)
    rw [hBt, testAffinePull_apply r (φ z) hr0,
      SupercriticalConformalCovariance.Domain.coe_monoCLM le_top] 
    ring
  · rw [confPullFun_of_notMem hx, confPullFun_of_notMem hx]
    ring

/-- The inverse derivative of the zoomed map is the original inverse
derivative evaluated after the target affine zoom. -/
theorem inverse_deriv_zoom {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r)
    {t : ℂ} (ht : t ∈ (affinePreimage V (φ z) r : Set ℂ)) :
    deriv (invFunOn (zoomMap φ z r) (affinePreimage U z r)) t =
      deriv (invFunOn φ U) (affinePt r (φ z) t) := by
  let hψ := zoomConformal hφ z hr
  obtain ⟨w, hw, hwt⟩ := hψ.2.surjOn ht
  subst t
  have hAw : affinePt r z w ∈ (U : Set ℂ) := hw
  have hderiv : deriv (zoomMap φ z r) w =
      deriv φ (affinePt r z w) := by
    have hAw' : z + (r : ℂ) * w ∈ (U : Set ℂ) := by
      change (r : ℂ) * w + z ∈ U at hAw
      change z + (r : ℂ) * w ∈ U
      simpa only [add_comm] using hAw
    rw [SmallGammaGeodesics.CC.deriv_zoomMap hr.ne'
      (hφ.1.differentiableAt (U.isOpen.mem_nhds hAw'))]
    congr 1
    change z + (r : ℂ) * w = (r : ℂ) * w + z
    ring
  have h₁ := SupercriticalConformalCovariance.Reversal.inverse_deriv_mul hψ hw
  have h₂ := SupercriticalConformalCovariance.Reversal.inverse_deriv_mul hφ hAw
  rw [hderiv] at h₁
  rw [← affine_zoomMap (φ := φ) z hr w] at h₂
  have hd0 : deriv φ (affinePt r z w) ≠ 0 := by
    intro he
    rw [he, mul_zero] at h₁
    exact zero_ne_one h₁
  exact mul_right_cancel₀ hd0 (h₁.trans h₂.symm)

/-- The logarithmic correction in the transformed zoomed field is the
affine precomposition of the original correction. -/
theorem logDerivInv_zoom (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q (zoomConformal hφ z hr) =
      (SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q hφ).comp
        (SupercriticalConformalCovariance.Root.mapsToCM (affinePreimage_conformal V (φ z) hr)) := by
  ext t
  exact congrArg (fun v : ℂ => Q * Real.log ‖v‖)
    (inverse_deriv_zoom hφ z hr t.2)

/-- The logarithmic distributional correction commutes with the target zoom. -/
theorem logCorrection_zoom_square (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Distribution.ofFun (affinePreimage V (φ z) r)
      (fun t => Q * Real.log
        ‖deriv (invFunOn (zoomMap φ z r) (affinePreimage U z r)) t‖)
      volume ⊤ =
    (confPushTest (affinePreimage_conformal V (φ z) hr)).precompCompactConvergenceCLM ℝ
      (Distribution.ofFun V
        (fun y => Q * Real.log ‖deriv (invFunOn φ U) y‖) volume ⊤) := by
  let hψ := zoomConformal hφ z hr
  let hB := affinePreimage_conformal V (φ z) hr
  rw [SupercriticalConformalCovariance.BiLip.PortTan.ofFun_logDeriv_eq Q hψ,
    SupercriticalConformalCovariance.BiLip.PortTan.ofFun_logDeriv_eq Q hφ]
  rw [logDerivInv_zoom Q hφ z hr]
  rw [← SupercriticalConformalCovariance.Root.precomp_ofFun_extZ hB
    (SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q hφ)]

/-- Exact distributional zoom square for the transformed field, before
subtracting its smooth-average normalization. -/
theorem confPullbackField_zoom_square (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (h : DistC) :
    confPullbackField Q
        (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))
        (restrictTo (affinePreimage U z r) (affineComp r z h)) =
      confPullbackField 0 (affinePreimage_conformal V (φ z) hr)
        (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U h)) := by
  let W := affinePreimage U z r
  let Z := affinePreimage V (φ z) r
  let hA := affinePreimage_conformal U z hr
  let hB := affinePreimage_conformal V (φ z) hr
  let hψ := zoomConformal hφ z hr
  ext t
  have hbase :
      (restrictTo W (affineComp r z h))
        (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hψ) t) =
      (restrictTo U h)
        (confPushTest hA
          (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hψ) t)) := by
    have he := congrArg
      (fun d : DistOn W => d (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hψ) t))
      (confPullbackField_zero_affine_restrict U z hr h)
    rw [confPullbackField, add_apply,
      confPushTest_precomp_eval] at he
    have hz : Distribution.ofFun (affinePreimage U z r) (fun _ => (0 : ℝ)) volume ⊤
        (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hψ) t) = 0 := by
      change (Distribution.ofFun (affinePreimage U z r) (0 : ℂ → ℝ) volume ⊤)
        (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hψ) t) = 0
      rw [Distribution.ofFun_zero]
      rfl
    simp only [zero_mul] at he
    rw [hz, add_zero] at he
    exact he.symm
  rw [confPullbackField, add_apply, confPushTest_precomp_eval]
  rw [confPullbackField, add_apply, confPushTest_precomp_eval]
  rw [hbase, confPushTest_zoom_square hφ z hr t]
  have hlog := congrArg (fun d : DistOn Z => d t)
    (logCorrection_zoom_square Q hφ z hr)
  rw [hlog]
  have hz : Distribution.ofFun (affinePreimage V (φ z) r)
      (fun _ => (0 : ℝ)) volume ⊤ t = 0 := by
    change (Distribution.ofFun (affinePreimage V (φ z) r) (0 : ℂ → ℝ) volume ⊤) t = 0
    rw [Distribution.ofFun_zero]
    rfl
  simp only [zero_mul]
  rw [hz, add_zero]
  rw [confPullbackField, add_apply, confPushTest_precomp_eval]
  rfl

/-- The corrected zoomed target field equals the affine pullback of the
original transformed field, with the same negative normalizer. -/
theorem confPullbackField_zoom_subConst (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (h : DistC) (c : ℝ) :
    let W := affinePreimage U z r
    let Z := affinePreimage V (φ z) r
    confPullbackField Q
        (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))
        (restrictTo W (addConst (affineComp r z h) (-c))) =
      confPullbackField 0 (affinePreimage_conformal V (φ z) hr)
        (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (restrictTo U h)) +
      Distribution.ofFun Z
        (Function.extend Subtype.val (negConstOn Z c) 0) volume ⊤ := by
  dsimp only
  let W := affinePreimage U z r
  let Z := affinePreimage V (φ z) r
  let hψ := zoomConformal hφ z hr
  let hB := affinePreimage_conformal V (φ z) hr
  rw [SupercriticalConformalCovariance.BiLip.restrictTo_addConst_eq W (affineComp r z h) (-c)]
  rw [SupercriticalConformalCovariance.BiLip.PortT.forward_add_const hψ Q (-c)]
  rw [confPullbackField_zoom_square Q hφ z hr h]
  have hconst : Distribution.ofFun Z
      (Function.extend Subtype.val (negConstOn Z c) 0) volume ⊤ =
      SupercriticalConformalCovariance.BiLip.PortT.constOn Z (-c) := by
    have he : negConstOn Z c = ContinuousMap.const Z (-c) := rfl
    rw [he]
    exact SupercriticalConformalCovariance.BiLip.PortT.ext_const_eq_constOn Z (-c)
  rw [hconst]

/-- A realization of the original transformed field yields the corrected
realization on both global zoomed domains. -/
theorem isDomainRealization_zoom_subConst (Q : ℝ) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (z : ℂ) {r : ℝ} (hr : 0 < r)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h g : Ω → DistC} {k : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P
      (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
        (restrictTo U (h ω))) g k)
    (c : Ω → ℝ) (hc : Measurable c) :
    let W := affinePreimage U z r
    let Z := affinePreimage V (φ z) r
    IsDomainRealization Z P
      (fun ω => confPullbackField Q
        (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))
        (restrictTo W
          (addConst (affineComp r z (h ω)) (-(c ω)))))
      (fun ω => affineComp r (φ z) (g ω))
      (fun ω => (k ω).comp
        (SupercriticalConformalCovariance.Root.mapsToCM (affinePreimage_conformal V (φ z) hr)) +
        negConstOn Z (c ω)) := by
  dsimp only
  have hAff := isDomainRealization_affinePull_subConst
    (φ z) hr hR c hc
  have heq : (fun ω => confPullbackField Q
      (SupercriticalConformalCovariance.Reversal.inverse_conformal (zoomConformal hφ z hr))
      (restrictTo (affinePreimage U z r)
        (addConst (affineComp r z (h ω)) (-(c ω))))) =
    (fun ω => confPullbackField 0
      (affinePreimage_conformal V (φ z) hr)
      (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
        (restrictTo U (h ω))) +
      Distribution.ofFun (affinePreimage V (φ z) r)
        (Function.extend Subtype.val
          (negConstOn (affinePreimage V (φ z) r) (c ω)) 0) volume ⊤) := by
    funext ω
    exact confPullbackField_zoom_subConst Q hφ z hr (h ω) (c ω)
  rw [heq]
  exact hAff

end SupercriticalConformalCovariance.Small

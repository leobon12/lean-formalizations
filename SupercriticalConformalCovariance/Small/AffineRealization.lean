import SupercriticalConformalCovariance.Root.Field
import SupercriticalConformalCovariance.Tangent.Normalize
import LQGMetric.Papers.GM.S3.DeterministicScale

set_option autoImplicit false
noncomputable section
open MeasureTheory Set TopologicalSpace Topology Function
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.Small

/-- Preimage of an open domain under a positive affine zoom. -/
def affinePreimage (V : Opens ℂ) (a : ℂ) (r : ℝ) : Opens ℂ :=
  ⟨(LQGMetric.affinePt r a) ⁻¹' (V : Set ℂ),
    V.isOpen.preimage (LQGMetric.affinePt r a).continuous⟩

private theorem affine_apply (a x : ℂ) (r : ℝ) :
    LQGMetric.affinePt r a x = (r : ℂ) * x + a := rfl

/-- The affine zoom bijects the preimage domain onto the original domain. -/
theorem affinePreimage_conformal (V : Opens ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConformalBijection (LQGMetric.affinePt r a) (affinePreimage V a r) V := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  constructor
  · intro x hx
    change DifferentiableWithinAt ℂ (fun t : ℂ => (r : ℂ) * t + a)
      (affinePreimage V a r : Set ℂ) x
    fun_prop
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact hx
    · intro x hx y hy he
      simp only [affine_apply] at he
      have hm : (r : ℂ) * x = (r : ℂ) * y := add_right_cancel he
      exact mul_left_cancel₀ hr0 hm
    · intro y hy
      refine ⟨(y - a) / (r : ℂ), ?_, ?_⟩
      · change LQGMetric.affinePt r a ((y - a) / (r : ℂ)) ∈ V
        rw [affine_apply]
        field_simp
        simpa using hy
      · rw [affine_apply]
        field_simp
        ring

/-- The inverse on the target domain is the elementary affine inverse. -/
theorem affinePreimage_inverse (V : Opens ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r)
    {y : ℂ} (hy : y ∈ (V : Set ℂ)) :
    invFunOn (LQGMetric.affinePt r a) (affinePreimage V a r) y =
      (y - a) / (r : ℂ) := by
  let W := affinePreimage V a r
  let B := LQGMetric.affinePt r a
  have hB := affinePreimage_conformal V a hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hx : (y - a) / (r : ℂ) ∈ W := by
    change B ((y - a) / (r : ℂ)) ∈ V
    change (r : ℂ) * ((y - a) / (r : ℂ)) + a ∈ V
    field_simp
    simpa using hy
  have hBx : B ((y - a) / (r : ℂ)) = y := by
    change (r : ℂ) * ((y - a) / (r : ℂ)) + a = y
    field_simp
    ring
  calc
    invFunOn B W y = invFunOn B W (B ((y - a) / (r : ℂ))) := by rw [hBx]
    _ = _ := hB.2.injOn.leftInvOn_invFunOn hx

/-- Derivative of the local affine inverse. -/
theorem affinePreimage_inverse_deriv (V : Opens ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r)
    {y : ℂ} (hy : y ∈ (V : Set ℂ)) :
    deriv (invFunOn (LQGMetric.affinePt r a) (affinePreimage V a r)) y = (r : ℂ)⁻¹ := by
  have heq : (invFunOn (LQGMetric.affinePt r a) (affinePreimage V a r)) =ᶠ[𝓝 y]
      (fun t : ℂ => (t - a) / (r : ℂ)) :=
    Filter.eventuallyEq_of_mem (V.isOpen.mem_nhds hy)
      (fun t ht => affinePreimage_inverse V a hr ht)
  rw [heq.deriv_eq]
  simp only [deriv_div_const, deriv_sub_const, deriv_id'', one_div]

/-- The frozen conformal test transport agrees with the affine distributional pullback. -/
theorem affine_confPushTest_apply (V : Opens ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r)
    (t : TestOn (affinePreimage V a r)) (y : ℂ) :
    (confPushTest (affinePreimage_conformal V a hr) t : ℂ → ℝ) y =
      (r ^ 2)⁻¹ *
        testAffinePull r a (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
          (Ω₁ := affinePreimage V a r) (Ω₂ := ⊤) t) y := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr0r : r ≠ 0 := hr.ne'
  change (V : Set ℂ).indicator
    (fun t_1 => ‖deriv (invFunOn (LQGMetric.affinePt r a) (affinePreimage V a r)) t_1‖ ^ 2 *
      t (invFunOn (LQGMetric.affinePt r a) (affinePreimage V a r) t_1)) y = _
  rw [LQGMetric.testAffinePull_apply r a hr0r]
  rw [SupercriticalConformalCovariance.Domain.coe_monoCLM le_top]
  by_cases hy : y ∈ (V : Set ℂ)
  · rw [Set.indicator_of_mem hy, affinePreimage_inverse_deriv V a hr hy,
      affinePreimage_inverse V a hr hy]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    field_simp
  · rw [Set.indicator_of_notMem hy]
    have hxy : (y - a) / (r : ℂ) ∉ (affinePreimage V a r : Set ℂ) := by
      intro hxy
      apply hy
      change (r : ℂ) * ((y - a) / (r : ℂ)) + a ∈ V at hxy
      field_simp at hxy
      simpa using hxy
    have hz : (t : ℂ → ℝ) ((y - a) / (r : ℂ)) = 0 := t.zero_on_compl hxy
    rw [hz, mul_zero]

/-- Affine pullback of a whole-plane distribution, restricted to an arbitrary open domain. -/
theorem confPullbackField_zero_affine_restrict (V : Opens ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r)
    (g : DistC) :
    confPullbackField 0 (affinePreimage_conformal V a hr) (restrictTo V g) =
      restrictTo (affinePreimage V a r) (affineComp r a g) := by
  let W := affinePreimage V a r
  let hB := affinePreimage_conformal V a hr
  ext t
  have ht : (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
        (Ω₁ := V) (Ω₂ := ⊤) (confPushTest hB t)) =
      (r ^ 2)⁻¹ • testAffinePull r a
        (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := ⊤) t) := by
    ext y
    rw [TestFunction.monoCLM_apply, smul_apply, smul_eq_mul]
    simp only [le_top, and_self, ↓reduceIte]
    exact affine_confPushTest_apply V a hr t y
  change g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (Ω₁ := V) (Ω₂ := ⊤) (confPushTest hB t)) +
      Distribution.ofFun W (fun y => (0 : ℝ) * Real.log ‖deriv (LQGMetric.affinePt r a) y‖)
        volume ⊤ t =
    affineComp r a g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (Ω₁ := W) (Ω₂ := ⊤) t)
  simp only [zero_mul]
  have hz : (Distribution.ofFun W (fun _ : ℂ => (0 : ℝ)) volume ⊤) t = 0 := by
    change (Distribution.ofFun W (0 : ℂ → ℝ) volume ⊤) t = 0
    rw [Distribution.ofFun_zero]
    rfl
  rw [hz, add_zero, ht, map_smul, smul_eq_mul, LQGMetric.GFFInv.affineComp_apply]

/-- A local realization pulls back through an affine zoom, with the whole-plane
part represented by `affineComp` and the local correction composed with the zoom. -/
theorem isDomainRealization_affinePull
    {V : Opens ℂ} (a : ℂ) {r : ℝ} (hr : 0 < r)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn V} {g : Ω → DistC} {k : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h g k) :
    IsDomainRealization (affinePreimage V a r) P
      (fun ω => confPullbackField 0 (affinePreimage_conformal V a hr) (h ω))
      (fun ω => affineComp r a (g ω))
      (fun ω => (k ω).comp (SupercriticalConformalCovariance.Root.mapsToCM (affinePreimage_conformal V a hr))) := by
  let W := affinePreimage V a r
  let hB := affinePreimage_conformal V a hr
  have hkzoom : Measurable (fun ω => (k ω).comp (SupercriticalConformalCovariance.Root.mapsToCM hB)) := by
    have : LocallyCompactSpace (W : Set ℂ) := W.isOpen.locallyCompactSpace
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    exact (ContinuousMap.measurable_eval (SupercriticalConformalCovariance.Root.mapsToCM hB x)).comp hR.2.2.1
  refine ⟨(SupercriticalConformalCovariance.Root.measurable_confPullbackField 0 hB).comp hR.1,
    LQGMetric.GM.isGFFPlusCont_affineComp hR.2.1 hr a,
    hkzoom, ?_⟩
  filter_upwards [hR.2.2.2] with ω hω
  rw [hω, SupercriticalConformalCovariance.Root.confPullbackField_add,
    confPullbackField_zero_affine_restrict V a hr (g ω),
    SupercriticalConformalCovariance.Root.precomp_ofFun_extZ]

/-- The negative normalization constant, as a local continuous correction. -/
def negConstOn (W : Opens ℂ) (c : ℝ) : C(W, ℝ) :=
  ⟨fun _ => -c, continuous_const⟩

/-- Affine zoom of a domain realization with the normalization in its local
correction, as required by Proposition 4.3. -/
theorem isDomainRealization_affinePull_subConst
    {V : Opens ℂ} (a : ℂ) {r : ℝ} (hr : 0 < r)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn V} {g : Ω → DistC} {k : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h g k)
    (c : Ω → ℝ) (hc : Measurable c) :
    let W := affinePreimage V a r
    let hB := affinePreimage_conformal V a hr
    IsDomainRealization W P
      (fun ω => confPullbackField 0 hB (h ω) +
        Distribution.ofFun W
          (Function.extend Subtype.val (negConstOn W (c ω)) 0) volume ⊤)
      (fun ω => affineComp r a (g ω))
      (fun ω => (k ω).comp (SupercriticalConformalCovariance.Root.mapsToCM hB) + negConstOn W (c ω)) := by
  dsimp only
  let W := affinePreimage V a r
  let hB := affinePreimage_conformal V a hr
  have hcOn : Measurable (fun ω => negConstOn W (c ω)) := by
    have : LocallyCompactSpace (W : Set ℂ) := W.isOpen.locallyCompactSpace
    rw [ContinuousMap.measurable_iff_eval]
    intro x
    exact hc.neg
  exact SupercriticalConformalCovariance.Domain.isDomainRealization_add
    (isDomainRealization_affinePull a hr hR) hcOn

end SupercriticalConformalCovariance.Small

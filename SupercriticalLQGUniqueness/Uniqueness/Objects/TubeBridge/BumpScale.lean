import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.BumpBridge
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Bump




 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge

def scaledMollifier (r : ℝ) (ε : Set.Ioi (0 : ℝ)) (x : ℂ) : ℝ :=
  (r ^ 2)⁻¹ * (Objects.Tube.mollifier ε).normed volume (r⁻¹ • x)

def scaledMollifierTest (r : ℝ) (hr : 0 < r) (ε : Set.Ioi (0 : ℝ)) :
    LQGMetric.TestC :=
  ⟨scaledMollifier r ε,
    by
      unfold scaledMollifier
      exact contDiff_const.mul ((Objects.Tube.mollifier ε).contDiff_normed.comp
        (contDiff_id.const_smul _)),
    by
      unfold scaledMollifier
      exact HasCompactSupport.mul_left
        ((Objects.Tube.mollifier ε).hasCompactSupport_normed.comp_smul (inv_ne_zero hr.ne')),
    subset_univ _⟩

theorem scaledMollifier_nonneg (r : ℝ) (ε : Set.Ioi (0 : ℝ)) (x : ℂ) :
    0 ≤ scaledMollifier r ε x := by
  unfold scaledMollifier
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg r))
    ((Objects.Tube.mollifier ε).nonneg_normed (μ := volume) (r⁻¹ • x))

theorem scaledMollifier_eq_zero_of_dist (r : ℝ) (hr : 0 < r)
    (ε : Set.Ioi (0 : ℝ)) (x : ℂ)
    (hx : (ε : ℝ) * r ≤ dist x 0) : scaledMollifier r ε x = 0 := by
  have hsc : dist (r⁻¹ • x) 0 = r⁻¹ * dist x 0 := by
    calc dist (r⁻¹ • x) 0 = dist (r⁻¹ • x) (r⁻¹ • (0 : ℂ)) := by simp
      _ = ‖r⁻¹‖ * dist x 0 := dist_smul₀ ..
      _ = r⁻¹ * dist x 0 := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have hball : r⁻¹ • x ∉ ball (0 : ℂ) ε := by
    rw [mem_ball, hsc]
    intro h
    rw [inv_mul_lt_iff₀ hr] at h
    nlinarith
  have hsupp : r⁻¹ • x ∉ Function.support ((Objects.Tube.mollifier ε).normed volume) := by
    rw [(Objects.Tube.mollifier ε).support_normed_eq]
    exact hball
  have hz : (Objects.Tube.mollifier ε).normed volume (r⁻¹ • x) = 0 := by
    by_contra hn
    exact hsupp hn
  unfold scaledMollifier
  rw [hz, mul_zero]

theorem scaledMollifier_integral (r : ℝ) (hr : 0 < r) (ε : Set.Ioi (0 : ℝ)) :
    ∫ x : ℂ, scaledMollifier r ε x = 1 := by
  unfold scaledMollifier
  rw [integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
    ((Objects.Tube.mollifier ε).normed volume) hr.le]
  rw [(Objects.Tube.mollifier ε).integral_normed]
  simp only [Complex.finrank_real_complex, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')

theorem mem_thickening_iff_inv_smul (S : Set ℂ) (r A : ℝ) (hr : 0 < r) (x : ℂ) :
    x ∈ thickening (A * r) S ↔
      r⁻¹ • x ∈ thickening A (r⁻¹ • S) := by
  rw [mem_thickening_iff, mem_thickening_iff]
  constructor
  · rintro ⟨u, hu, hxu⟩
    refine ⟨r⁻¹ • u, ⟨u, hu, rfl⟩, ?_⟩
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    rw [inv_mul_lt_iff₀ hr]
    nlinarith
  · rintro ⟨u, ⟨v, hv, rfl⟩, hxu⟩
    refine ⟨v, hv, ?_⟩
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hxu
    rw [inv_mul_lt_iff₀ hr] at hxu
    nlinarith

theorem integral_indicator_scaledMollifier (V S : Set ℂ) (r : ℝ) (hr : 0 < r)
    (ε : Set.Ioi (0 : ℝ)) (x : ℂ)
    (hV : ∀ v : ℂ, r • v ∈ V ↔ v ∈ S) :
    (∫ y : ℂ, V.indicator (fun _ => (1 : ℝ)) y * scaledMollifier r ε (x - y)) =
      Objects.Tube.mollInd S ε (r⁻¹ • x) := by
  classical
  let φ : ℂ → ℝ := (Objects.Tube.mollifier ε).normed volume
  let F : ℂ → ℝ := fun y => V.indicator (fun _ => (1 : ℝ)) y *
    scaledMollifier r ε (x - y)
  have hF (v : ℂ) : F (r • v) = (r ^ 2)⁻¹ *
      (φ (r⁻¹ • x - v) * S.indicator (fun _ => (1 : ℝ)) v) := by
    simp only [F, scaledMollifier]
    have hsmul : r⁻¹ • (x - r • v) = r⁻¹ • x - v := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    rw [hsmul]
    by_cases hv : v ∈ S
    · have hvV : r • v ∈ V := (hV v).2 hv
      simp only [Set.indicator_of_mem hvV, Set.indicator_of_mem hv]
      ring
    · have hvV : r • v ∉ V := fun h => hv ((hV v).1 h)
      simp only [Set.indicator_of_notMem hvV, Set.indicator_of_notMem hv]
      ring
  have hscale := Measure.integral_comp_smul_of_nonneg (μ := volume) F r (hR := hr.le)
  have hscale' : (∫ v : ℂ, F (r • v)) =
      (r ^ 2)⁻¹ * (∫ y : ℂ, F y) := by
    simpa only [Complex.finrank_real_complex, smul_eq_mul] using hscale
  simp_rw [hF] at hscale'
  rw [integral_const_mul] at hscale'
  have hne : (r ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hr.ne')
  have hI : (∫ y : ℂ, F y) =
      ∫ v : ℂ, φ (r⁻¹ • x - v) * S.indicator (fun _ => (1 : ℝ)) v := by
    exact mul_left_cancel₀ hne hscale'.symm
  change (∫ y : ℂ, F y) = Objects.Tube.mollInd S ε (r⁻¹ • x)
  rw [hI, Objects.Tube.mollInd, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, φ]

theorem tubeV_scaled (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r Asup : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r) (v : ℂ) :
    r • v ∈ Objects.CorrectedEvent.tubeV T (Asup / 2) ↔
      v ∈ thickening (Asup / 2) (r⁻¹ • P.tube r) := by
  rw [tubeV_eq T P r (Asup / 2) hr hρ hK hn hα hψu hψv hs hwp hP hrpos]
  change r • v ∈ thickening ((Asup / 2) * r) (P.tube r) ↔
    v ∈ thickening (Asup / 2) (r⁻¹ • P.tube r)
  simpa only [smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul] using
    (mem_thickening_iff_inv_smul (P.tube r) r (Asup / 2) hrpos (r • v))

theorem bumpFormula_eq_bump (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams)
    (r Asup Amax : ℝ) (hAsup : 0 < Asup)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (hψv : T.psiV = P.ψv)
    (hs : T.blockRadius = P.s r) (hwp : P.wp = T.lambda * T.A_endpt)
    (hP : P.Good) (hrpos : 0 < r)
    (hMoll : ∀ y : ℂ, T.mollifier y =
      scaledMollifier r (Objects.Tube.TubeParams.quarter' ⟨Asup, hAsup⟩) y)
    (x : ℂ) :
    Objects.CorrectedEvent.bumpFormula T Amax Asup x =
      P.bump r Amax ⟨Asup, hAsup⟩ x := by
  rw [bumpFormula_eq_convolution, Objects.Tube.TubeParams.bump]
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simp_rw [hMoll]
  rw [integral_indicator_scaledMollifier
    (Objects.CorrectedEvent.tubeV T (Asup / 2))
    (thickening (Asup / 2) (r⁻¹ • P.tube r)) r hrpos
    (Objects.Tube.TubeParams.quarter' ⟨Asup, hAsup⟩) x
    (tubeV_scaled T P r Asup hr hρ hK hn hα hψu hψv hs hwp hP hrpos)]


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge

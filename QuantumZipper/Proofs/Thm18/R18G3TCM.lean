import QuantumZipper.Proofs.Thm18.R18G3TRegion
import QuantumZipper.Proofs.GFF.CameronMartinTV

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-a) groundwork: the Cameron–Martin tilt of the cut-off profile

Sources: Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*,
arXiv:2004.04720, Lemma 3.12 (Cameron–Martin for the GFF: the law of `h + φ` is that of `h`
tilted by `exp((h, ρ) − E(φ)/2)`, `ρ = −Δφ/2π`); Sheffield, arXiv:1012.4797, p. 72 and
Remark 5.7 (adding a smooth function changes the law of the field away from its support only
absolutely continuously).

* (a1) `g3wCut γ η` is `C²`, compactly supported and even across `ℝ`.
* (a2) its Laplacian vanishes on the annulus `η/2 < ‖z‖ < 7/8` (there it is `−γ log‖z‖`, harmonic
  off `0`: mathlib `AnalyticAt.harmonicAt_log_norm`), so the Cameron–Martin measures of the shift
  charge neither half-disc of an index with that `η`.
* (a3) the exact Cameron–Martin identity for the free field (`CameronMartin.integral_mul_tiltDensity`
  as in `CMTV.abs_integral_incr_shift_sub_le`) with the explicit density
  `cmTilt X φ = exp(X μ₀ − X ν₀ − E_H(φ)/2)`, which is measurable for the field outside both
  half-discs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Laplacian
open scoped Topology ENNReal NNReal ComplexConjugate Real

namespace QuantumZipper
namespace R18

open Thm18Asm

/-! ## (a1) Regularity of the cut-off profile -/

theorem contDiff_g3wCut (γ η : ℝ) (hη : 0 < η) : ContDiff ℝ 2 (g3wCut γ η) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have hev : g3wCut γ η =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < η / 4 by positivity)] with w hw
      rw [mem_ball, dist_zero_right] at hw
      have h0 : (‖w‖ - η / 4) / (η / 4) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      simp only [g3wCut, Real.smoothTransition.zero_of_nonpos h0, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hn : ContDiffAt ℝ 2 (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz
    have hlog : ContDiffAt ℝ 2 (fun w : ℂ => Real.log ‖w‖) z :=
      (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hz)).comp z hn
    have hs : ∀ y : ℝ, ContDiffAt ℝ 2 Real.smoothTransition y := fun y =>
      (Real.smoothTransition.contDiff (n := 2)).contDiffAt
    unfold g3wCut g3wProf
    exact (((hs _).comp z ((hn.sub contDiffAt_const).div_const _)).mul
      ((hs _).comp z ((contDiffAt_const.sub hn).mul contDiffAt_const))).mul (contDiffAt_const.mul hlog)

theorem hasCompactSupport_g3wCut (γ η : ℝ) : HasCompactSupport (g3wCut γ η) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) fun z hz => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hz
  have h0 : (1 - ‖z‖) * 8 ≤ 0 := by nlinarith
  simp only [g3wCut, Real.smoothTransition.zero_of_nonpos h0, mul_zero, zero_mul]

theorem g3wCut_conj (γ η : ℝ) (z : ℂ) : g3wCut γ η (conj z) = g3wCut γ η z := by
  simp only [g3wCut, g3wProf, Complex.norm_conj]

/-! ## (a2) The Laplacian vanishes on the annulus -/

theorem harmonicAt_g3wProf (γ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt (g3wProf γ) z := by
  have h := (analyticAt_id (𝕜 := ℂ) (z := z)).harmonicAt_log_norm hz
  have h2 := h.const_smul (c := -γ)
  convert h2 using 1
  funext w
  simp [g3wProf, smul_eq_mul]

theorem laplacian_g3wCut_eq_zero (γ η : ℝ) (hη : 0 < η) {z : ℂ} (h1 : η / 2 < ‖z‖)
    (h2 : ‖z‖ < 7 / 8) : Δ (g3wCut γ η) z = 0 := by
  have hz : z ≠ 0 := fun h => by simp [h] at h1; linarith
  have hev : g3wCut γ η =ᶠ[𝓝 z] g3wProf γ := by
    have hU : IsOpen {w : ℂ | η / 2 < ‖w‖ ∧ ‖w‖ < 7 / 8} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    filter_upwards [hU.mem_nhds ⟨h1, h2⟩] with w hw
    exact g3wCut_eq_of_norm γ η hη hw.1.le hw.2.le
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
  exact (harmonicAt_g3wProf γ hz).2.eq_of_nhds

theorem cmDens_g3wCut_eq_zero_of_mem (γ : ℝ) (i : G3Idx) {z : ℂ}
    (hz : z ∈ ball (i.t₁ : ℂ) i.r₁ ∪ ball (i.t₂ : ℂ) i.r₂) :
    CMTV.cmDens (g3wCut γ i.η) z = 0 := by
  have hη := i.hη; have hηδ := i.hηδ; have hδ := i.hδ
  have hb : 3 * i.η / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2 + i.η / 4 := by
    rcases hz with hz | hz
    · exact norm_bounds_of_mem_ball₁ i hz
    · exact norm_bounds_of_mem_ball₂ i hz
  rw [CMTV.cmDens,
    laplacian_g3wCut_eq_zero γ i.η hη (z := z) (by linarith [hb.1]) (by linarith [hb.2]),
    neg_zero, mul_zero]

theorem cmPos_g3wCut_balls (γ : ℝ) (i : G3Idx) :
    CMTV.cmPos (g3wCut γ i.η) (ball (i.t₁ : ℂ) i.r₁ ∪ ball (i.t₂ : ℂ) i.r₂) = 0 := by
  have hm : Measurable fun z => ENNReal.ofReal (CMTV.cmDens (g3wCut γ i.η) z) :=
    ENNReal.measurable_ofReal.comp
      (CMTV.continuous_cmDens (contDiff_g3wCut γ i.η i.hη)).measurable
  rw [CMTV.cmPos, withDensity_apply_eq_zero hm]
  refine measure_mono_null (fun z hz => ?_) (measure_empty (μ := volume.restrict Hbar))
  exact hz.1 (by simp [cmDens_g3wCut_eq_zero_of_mem γ i hz.2])

theorem cmNeg_g3wCut_balls (γ : ℝ) (i : G3Idx) :
    CMTV.cmNeg (g3wCut γ i.η) (ball (i.t₁ : ℂ) i.r₁ ∪ ball (i.t₂ : ℂ) i.r₂) = 0 := by
  have hm : Measurable fun z => ENNReal.ofReal (-CMTV.cmDens (g3wCut γ i.η) z) :=
    ENNReal.measurable_ofReal.comp
      (CMTV.continuous_cmDens (contDiff_g3wCut γ i.η i.hη)).measurable.neg
  rw [CMTV.cmNeg, withDensity_apply_eq_zero hm]
  refine measure_mono_null (fun z hz => ?_) (measure_empty (μ := volume.restrict Hbar))
  exact hz.1 (by simp [cmDens_g3wCut_eq_zero_of_mem γ i hz.2])

/-! ## (a3) The exact Cameron–Martin identity -/

/-- The Cameron–Martin density of the shift `φ`: `exp(X μ₀ − X ν₀ − E_H(φ)/2)`. -/
def cmTilt {Ω : Type*} (X : Ω → FieldSample) (φ : ℂ → ℝ) (ω : Ω) : ℝ :=
  Real.exp ((X ω (CMTV.cmPos φ) - X ω (CMTV.cmNeg φ)) - dirichletEnergyOn H φ / 2)

section CM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample} {φ : ℂ → ℝ}

theorem covShift_cm (hX : IsFreeGFFModConstH X P) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (heven : ∀ z, φ (conj z) = φ z) (j : K3.BalIdx) :
    CameronMartin.covShift (fun (j : K3.BalIdx) ω => X ω j.1.1 - X ω j.1.2) P
      (Finsupp.single (CMTV.cmIdx hφ hc heven) 1) j = ∫ z, φ z ∂j.1.1 - ∫ z, φ z ∂j.1.2 := by
  set j₀ := CMTV.cmIdx hφ hc heven
  simp only [CameronMartin.covShift, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul, CameronMartin.covK]
  rw [hX.covariance_eq j.1 j₀.1 j.2.1 j.2.2.1 j.2.2.2 j₀.2.1 j₀.2.2.1 j₀.2.2.2]
  exact CMTV.kernelCov2_cm hφ hc heven j

theorem covNorm_cm (hX : IsFreeGFFModConstH X P) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (heven : ∀ z, φ (conj z) = φ z) :
    CameronMartin.covNorm (fun (j : K3.BalIdx) ω => X ω j.1.1 - X ω j.1.2) P
      (Finsupp.single (CMTV.cmIdx hφ hc heven) 1) = dirichletEnergyOn H φ := by
  simp only [CameronMartin.covNorm, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul]
  rw [covShift_cm hX]
  exact CMTV.integral_cm_self hφ hc heven

theorem cmTilt_eq_tiltDensity (hX : IsFreeGFFModConstH X P) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (heven : ∀ z, φ (conj z) = φ z) :
    cmTilt X φ = CameronMartin.tiltDensity (fun (j : K3.BalIdx) ω => X ω j.1.1 - X ω j.1.2) P
      (Finsupp.single (CMTV.cmIdx hφ hc heven) 1) := by
  funext ω
  rw [CameronMartin.tiltDensity, covNorm_cm hX]
  simp only [CameronMartin.comb, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul]
  rfl

theorem cmTilt_pos (φ : ℂ → ℝ) (ω : Ω) : 0 < cmTilt X φ ω := Real.exp_pos _

/-- The tilt is measurable for the field outside two discs its Cameron–Martin measures avoid. -/
theorem measurable_cmTilt_outside (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (heven : ∀ z, φ (conj z) = φ z) {t₁ r₁ t₂ r₂ : ℝ}
    (hp : CMTV.cmPos φ (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0)
    (hn : CMTV.cmNeg φ (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0) :
    Measurable[outsideSigma2 X t₁ r₁ t₂ r₂] (cmTilt X φ) :=
  Real.measurable_exp.comp ((measurable_outsideSigma2 (CMTV.isAdmissibleH_cmPos hφ hc)
    (CMTV.isAdmissibleH_cmNeg hφ hc) (CMTV.cmPos_univ_eq hφ hc heven) hp hn).sub_const _)

end CM

/-- The tilt of the cut-off profile at an index is measurable for the field outside both
half-discs of the index. -/
theorem measurable_cmTilt_g3wCut {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    (γ : ℝ) (i : G3Idx) :
    Measurable[outsideSigma2 X i.t₁ i.r₁ i.t₂ i.r₂] (cmTilt X (g3wCut γ i.η)) :=
  measurable_cmTilt_outside (contDiff_g3wCut γ i.η i.hη) (hasCompactSupport_g3wCut γ i.η)
    (g3wCut_conj γ i.η) (cmPos_g3wCut_balls γ i) (cmNeg_g3wCut_balls γ i)

end R18
end QuantumZipper

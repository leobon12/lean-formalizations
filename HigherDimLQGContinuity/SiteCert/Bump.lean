import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.LogEnergy.QuantDeriv
import HigherDimLQGMetric.LogEnergy.Affine
import HigherDimLQGMetric.LogEnergy.CM
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth plateau profiles for the site certificate

The profile is the convolution of the indicator of a thickened closed set with a
unit-mass smooth radial kernel. The kernel is the normalized Mathlib bump with
inner radius `h / 8` and outer radius `h / 4`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Function ContinuousLinearMap
open scoped Convolution Topology Pointwise
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- The fixed-shape, unit-mass mollifier at scale `h`. -/
def plateauKernel {d : ℕ} (h : ℝ) (hh : 0 < h) : Rd d → ℝ :=
  (⟨h / 8, h / 4, by positivity, by linarith⟩ : ContDiffBump (0 : Rd d)).normed volume

/-- The plateau profile `1_{U^{+h/4}} * φ_{h/4}`. -/
def plateauBump {d : ℕ} (U : Set (Rd d)) (h : ℝ) (hh : 0 < h) : Rd d → ℝ :=
  (plateauKernel h hh ⋆[lsmul ℝ ℝ, volume] (thickening (h / 4) U).indicator (fun _ => (1 : ℝ)))

private def plateauKernelData {d : ℕ} (h : ℝ) (hh : 0 < h) :
    ContDiffBump (0 : Rd d) :=
  ⟨h / 8, h / 4, by positivity, by linarith⟩

private theorem plateauKernel_eq {d : ℕ} (h : ℝ) (hh : 0 < h) :
    plateauKernel (d := d) h hh = (plateauKernelData h hh).normed volume := rfl

private theorem plateauKernelData_scale {d : ℕ} (h : ℝ) (hh : 0 < h)
    (x : Rd d) :
    (plateauKernelData h hh : Rd d → ℝ) x =
      (plateauKernelData 1 one_pos : Rd d → ℝ) (h⁻¹ • x) := by
  simp only [plateauKernelData, ContDiffBump.toFun, Function.comp_apply,
    sub_zero, smul_smul]
  congr 1
  · field_simp
  · field_simp

private theorem plateauKernelData_integral_scale {d : ℕ} (h : ℝ) (hh : 0 < h) :
    (∫ x : Rd d, (plateauKernelData h hh : Rd d → ℝ) x) =
      h ^ d * ∫ x : Rd d, (plateauKernelData 1 one_pos : Rd d → ℝ) x := by
  simp_rw [plateauKernelData_scale h hh]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (plateauKernelData 1 one_pos : Rd d → ℝ) h⁻¹ (hR := by positivity)]
  simp [inv_pow]

theorem plateauKernel_scale {d : ℕ} (h : ℝ) (hh : 0 < h) (x : Rd d) :
    plateauKernel h hh x = (h ^ d)⁻¹ *
      plateauKernel 1 one_pos (h⁻¹ • x) := by
  rw [plateauKernel_eq, plateauKernel_eq]
  simp only [ContDiffBump.normed_def]
  rw [plateauKernelData_integral_scale h hh,
    plateauKernelData_scale h hh x]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

theorem plateauKernel_isCMBounded {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (hh : 0 < h),
      HigherDimLQGMetric.IsCMBounded (plateauKernel (d := d) h hh)
        ((h ^ d)⁻¹ * C) := by
  let φ : ContDiffBump (0 : Rd d) := plateauKernelData 1 one_pos
  obtain ⟨C, hC, hcm⟩ := HigherDimLQGMetric.exists_isCMBounded hd
    (φ.contDiff_normed (μ := volume)) (φ.hasCompactSupport_normed (μ := volume))
  refine ⟨C, hC, ?_⟩
  intro h hh
  have hscaled : HigherDimLQGMetric.IsCMBounded
      (fun x : Rd d => plateauKernel 1 one_pos (h⁻¹ • (x - 0))) C := by
    exact hcm.comp_affine (φ.continuous_normed (μ := volume)) hh 0
  have hscaled' := hscaled.mul_const (h ^ d)⁻¹
  have hpow : 0 ≤ (h ^ d)⁻¹ := by positivity
  convert hscaled' using 1
  · funext x
    simpa only [sub_zero] using plateauKernel_scale h hh x
  · simp only [abs_of_nonneg hpow]

private theorem q7a_convolution_pair_integrable {d : ℕ}
    {f : Rd d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (A : Set (Rd d)) (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (φ : HigherDimLQGMetric.TestRd d) :
    Integrable (fun p : Rd d × Rd d =>
      (A.indicator (fun _ => (1 : ℝ)) p.2 * f (p.1 - p.2)) * φ p.1)
      (volume.prod volume) := by
  let g : Rd d → ℝ := A.indicator (fun _ => 1)
  have hAfinite : volume A ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hAc.measure_lt_top).ne
  have hg : Integrable g volume :=
    (integrableOn_const (C := (1 : ℝ)) hAfinite).integrable_indicator hA
  have hfi : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
  let M : ℝ := sSup (Set.range (fun x : Rd d => ‖φ x‖))
  have hMbd : BddAbove (Set.range (fun x : Rd d => ‖φ x‖)) :=
    φ.continuous.norm.bddAbove_range_of_hasCompactSupport φ.hasCompactSupport.norm
  have hM : ∀ x, ‖φ x‖ ≤ M := fun x => le_csSup hMbd (mem_range_self x)
  have hjoint : Integrable
      (fun p : Rd d × Rd d => g p.2 * f (p.1 - p.2)) (volume.prod volume) := by
    simpa only [lsmul_apply, smul_eq_mul] using
      (hg.convolution_integrand (lsmul ℝ ℝ) hfi)
  apply Integrable.mono' (hjoint.norm.const_mul M)
  · exact hjoint.aestronglyMeasurable.mul
      ((φ.continuous.measurable.comp measurable_fst).aestronglyMeasurable)
  · exact ae_of_all _ fun p => by
      have hm := hM p.1
      rw [Real.norm_eq_abs] at hm
      calc
        ‖(g p.2 * f (p.1 - p.2)) * φ p.1‖ =
            |g p.2 * f (p.1 - p.2)| * |φ p.1| := by simp [Real.norm_eq_abs, abs_mul]
        _ ≤ |g p.2 * f (p.1 - p.2)| * M :=
          mul_le_mul_of_nonneg_left hm (abs_nonneg _)
        _ = M * ‖g p.2 * f (p.1 - p.2)‖ := by rw [Real.norm_eq_abs]; ring

private theorem q7a_convolution_pair_eq {d : ℕ}
    {f : Rd d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (A : Set (Rd d)) (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (φ : HigherDimLQGMetric.TestRd d) :
    (∫ x, (f ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ => (1 : ℝ))) x * φ x) =
      ∫ a, A.indicator (fun _ => (1 : ℝ)) a *
        ∫ x, f (x - a) * φ x := by
  let g : Rd d → ℝ := A.indicator (fun _ => 1)
  have hi := q7a_convolution_pair_integrable hf hfc A hA hAc φ
  calc
    (∫ x, (f ⋆[lsmul ℝ ℝ, volume] g) x * φ x) =
        ∫ x, ∫ a, (g a * f (x - a)) * φ x := by
      congr 1
      ext x
      rw [convolution_eq_swap]
      simp_rw [lsmul_apply, smul_eq_mul]
      rw [integral_mul_const]
      apply congrArg (fun v : ℝ => v * φ x)
      apply integral_congr_ae
      exact ae_of_all _ fun a => by ring
    _ = ∫ a, ∫ x, (g a * f (x - a)) * φ x := integral_integral_swap hi
    _ = ∫ a, g a * ∫ x, f (x - a) * φ x := by
      congr 1
      ext a
      simp_rw [mul_assoc]
      rw [integral_const_mul]

private theorem q7a_convolution_indicator_cm {d : ℕ}
    {f : Rd d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {C : ℝ} (_hC : 0 ≤ C) (hcm : HigherDimLQGMetric.IsCMBounded f C)
    (A : Set (Rd d)) (hA : MeasurableSet A) (hAc : IsCompact (closure A)) :
    HigherDimLQGMetric.IsCMBounded
      (f ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ => (1 : ℝ)))
      ((volume A).toReal * C) := by
  let g : Rd d → ℝ := A.indicator (fun _ => 1)
  have hAfinite : volume A ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hAc.measure_lt_top).ne
  have hg : Integrable g volume :=
    (integrableOn_const (C := (1 : ℝ)) hAfinite).integrable_indicator hA
  intro φ
  have hi := q7a_convolution_pair_integrable hf hfc A hA hAc φ.1
  have houter : Integrable
      (fun a : Rd d => g a * ∫ x, f (x - a) * φ.1 x) volume := by
    have hh := hi.integral_prod_right
    convert hh using 1
    ext a
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  have htr (a : Rd d) :
      |∫ x, f (x - a) * φ.1 x| ≤ C * HigherDimLQGMetric.logNorm φ.1 := by
    have ht := hcm.comp_affine hf one_pos a φ
    simpa only [inv_one, one_smul] using ht
  have hg0 (a : Rd d) : 0 ≤ g a := by
    by_cases ha : a ∈ A <;> simp [g, ha]
  calc
    |∫ x, (f ⋆[lsmul ℝ ℝ, volume] g) x * φ.1 x| =
        |∫ a, g a * ∫ x, f (x - a) * φ.1 x| := by
      rw [q7a_convolution_pair_eq hf hfc A hA hAc φ.1]
    _ ≤ ∫ a, |g a * ∫ x, f (x - a) * φ.1 x| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ a, g a * (C * HigherDimLQGMetric.logNorm φ.1) := by
      apply integral_mono houter.abs (hg.mul_const _)
      intro a
      change |g a * ∫ x, f (x - a) * φ.1 x| ≤
        g a * (C * HigherDimLQGMetric.logNorm φ.1)
      rw [abs_mul, abs_of_nonneg (hg0 a)]
      exact mul_le_mul_of_nonneg_left (htr a) (hg0 a)
    _ = (volume A).toReal * C * HigherDimLQGMetric.logNorm φ.1 := by
      rw [integral_mul_const]
      simp [g, integral_indicator, hA, Measure.real]
      ring

private theorem q7a_plateau_cm_uniform {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Rd d)) (h : ℝ) (hh : 0 < h),
      h ≤ 1 → U ⊆ closedBall 0 4 →
      HigherDimLQGMetric.IsCMBounded (plateauBump U h hh)
        (C * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ))) := by
  obtain ⟨C₀, hC₀, hkernel⟩ := plateauKernel_isCMBounded hd
  let K : Set (Rd d) := cthickening (1 / 4) (closedBall 0 4)
  have hK : IsCompact K := (isCompact_closedBall (0 : Rd d) 4).cthickening
  let V : ℝ := (volume K).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  let C : ℝ := 1 + V * C₀
  have hC : 0 < C := by dsimp [C]; nlinarith [mul_nonneg hV hC₀]
  refine ⟨C, hC, ?_⟩
  intro U h hh hh1 hU
  let A : Set (Rd d) := thickening (h / 4) U
  have hAK : A ⊆ K := by
    exact (thickening_subset_cthickening_of_le (by linarith : h / 4 ≤ 1 / 4) U).trans
      (cthickening_subset_of_subset (1 / 4) hU)
  have hAc : IsCompact (closure A) :=
    hK.of_isClosed_subset isClosed_closure
      (closure_minimal hAK isClosed_cthickening)
  have hAmeas : MeasurableSet A := isOpen_thickening.measurableSet
  have hVol : (volume A).toReal ≤ V :=
    ENNReal.toReal_mono hK.measure_lt_top.ne (measure_mono hAK)
  have hk : d ≤ 2 * (d / 2 + 1) := by omega
  have hpow : (h ^ d)⁻¹ ≤ h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)) := by
    have he : (-(2 * ((d / 2 : ℕ) + 1) : ℝ)) ≤ -(d : ℝ) := by
      exact neg_le_neg (by exact_mod_cast hk)
    have hr := Real.rpow_le_rpow_of_exponent_ge hh hh1 he
    rw [Real.rpow_neg hh.le (d : ℝ), Real.rpow_natCast] at hr
    exact hr
  have hbase : HigherDimLQGMetric.IsCMBounded (plateauBump U h hh)
      ((volume A).toReal * ((h ^ d)⁻¹ * C₀)) := by
    rw [plateauBump, plateauKernel_eq]
    exact (q7a_convolution_indicator_cm
        ((plateauKernelData (d := d) h hh).continuous_normed (μ := volume))
        ((plateauKernelData (d := d) h hh).hasCompactSupport_normed (μ := volume))
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hh.le _)) hC₀)
        (hkernel h hh) A hAmeas hAc)
  apply hbase.mono
  calc
    (volume A).toReal * ((h ^ d)⁻¹ * C₀) ≤ V * ((h ^ d)⁻¹ * C₀) := by
      gcongr
    _ ≤ V * (h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)) * C₀) := by
      gcongr
    _ ≤ C * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)) := by
      have hVC : V * C₀ ≤ C := by dsimp [C]; linarith
      calc
        V * (h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)) * C₀) =
            (V * C₀) * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)) := by ring
        _ ≤ C * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hVC (Real.rpow_nonneg hh.le _)

theorem plateauBump_contDiff {d : ℕ} (U : Set (Rd d)) (h : ℝ) (hh : 0 < h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (plateauBump U h hh) := by
  rw [plateauBump, plateauKernel_eq]
  exact (plateauKernelData h hh).hasCompactSupport_normed.contDiff_convolution_left _
    (plateauKernelData h hh).contDiff_normed
    ((locallyIntegrable_const (1 : ℝ)).indicator isOpen_thickening.measurableSet)

theorem plateauBump_eq_one {d : ℕ} (U : Set (Rd d)) (h : ℝ) (hh : 0 < h)
    {x : Rd d} (hx : x ∈ U) : plateauBump U h hh x = 1 := by
  rw [plateauBump, plateauKernel_eq]
  have hxU : x ∈ thickening (h / 4) U := by
    apply (mem_thickening_iff).2
    exact ⟨x, hx, by simpa using (show 0 < h / 4 by positivity)⟩
  have hconst : ∀ y ∈ ball x (h / 4),
      (thickening (h / 4) U).indicator (fun _ => (1 : ℝ)) y =
        (thickening (h / 4) U).indicator (fun _ => (1 : ℝ)) x := by
    intro y hy
    have hyU : y ∈ thickening (h / 4) U := by
      apply (mem_thickening_iff).2
      exact ⟨x, hx, by simpa [plateauKernelData, dist_comm] using hy⟩
    simp [hyU, hxU]
  rw [(plateauKernelData (d := d) h hh).normed_convolution_eq_right hconst]
  simp [hxU]

theorem plateauBump_mem_Icc {d : ℕ} (U : Set (Rd d)) (h : ℝ) (hh : 0 < h)
    (x : Rd d) : plateauBump U h hh x ∈ Set.Icc (0 : ℝ) 1 := by
  let φ : ContDiffBump (0 : Rd d) := plateauKernelData h hh
  let A : Set (Rd d) := thickening (h / 4) U
  have hφ : ∀ y, 0 ≤ φ.normed volume y := φ.nonneg_normed
  have hg : ∀ y, 0 ≤ A.indicator (fun _ => (1 : ℝ)) y ∧
      A.indicator (fun _ => (1 : ℝ)) y ≤ 1 := by
    intro y
    by_cases hy : y ∈ A <;> simp [hy]
  have hloc : LocallyIntegrable (A.indicator (fun _ => (1 : ℝ))) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator isOpen_thickening.measurableSet
  have hconv : ConvolutionExistsAt (φ.normed volume)
      (A.indicator (fun _ => (1 : ℝ))) x (lsmul ℝ ℝ) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) φ.continuous_normed hloc x
  have hconv0 : ConvolutionExistsAt (φ.normed volume)
      (fun _ : Rd d => (0 : ℝ)) x (lsmul ℝ ℝ) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) φ.continuous_normed
      (locallyIntegrable_const (0 : ℝ)) x
  have hconv1 : ConvolutionExistsAt (φ.normed volume)
      (fun _ : Rd d => (1 : ℝ)) x (lsmul ℝ ℝ) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) φ.continuous_normed
      (locallyIntegrable_const (1 : ℝ)) x
  have hlow := convolution_mono_right hconv0 hconv hφ (fun y => (hg y).1)
  have hup := convolution_mono_right hconv hconv1 hφ (fun y => (hg y).2)
  have hzero : ((φ.normed volume) ⋆[lsmul ℝ ℝ, volume]
      (fun _ : Rd d => (0 : ℝ))) x = 0 := by simp [convolution_def]
  have hone : ((φ.normed volume) ⋆[lsmul ℝ ℝ, volume]
      (fun _ : Rd d => (1 : ℝ))) x = 1 := by
    exact φ.normed_convolution_eq_right (fun _ _ => rfl)
  change 0 ≤ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ => (1 : ℝ))) x ∧
    (φ.normed volume ⋆[lsmul ℝ ℝ, volume] A.indicator (fun _ => (1 : ℝ))) x ≤ 1
  exact ⟨by simpa only [hzero] using hlow, by simpa only [hone] using hup⟩

theorem plateauBump_tsupport_subset {d : ℕ} (U : Set (Rd d))
    (h : ℝ) (hh : 0 < h) :
    tsupport (plateauBump U h hh) ⊆ cthickening (h / 2) U := by
  let φ : ContDiffBump (0 : Rd d) := plateauKernelData h hh
  let A : Set (Rd d) := thickening (h / 4) U
  have hfs : support (φ.normed volume) ⊆ ball (0 : Rd d) (h / 4) := by
    simpa only [φ, plateauKernelData] using φ.support_normed_eq.subset
  have hgs : support (A.indicator (fun _ => (1 : ℝ))) ⊆ A := by
    intro x hx
    by_contra hnx
    exact hx (Set.indicator_of_notMem hnx _)
  have hs : support (plateauBump U h hh) ⊆ thickening (h / 2) U := by
    intro x hx
    have hx' : x ∈ support (φ.normed volume) + support (A.indicator (fun _ => (1 : ℝ))) :=
      (support_convolution_subset (L := lsmul ℝ ℝ)).trans_eq (by rfl) hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx'
    have hyball : y ∈ ball (0 : Rd d) (h / 4) := hfs hy
    have hzA : z ∈ A := hgs hz
    have heq : h / 4 + h / 4 = h / 2 := by ring
    rw [← heq]
    apply (thickening_thickening_subset (h / 4) (h / 4) U)
    apply (mem_thickening_iff).2
    refine ⟨z, hzA, ?_⟩
    simpa [dist_eq_norm] using hyball
  exact (closure_minimal (hs.trans (thickening_subset_cthickening _ U))
    isClosed_cthickening)

theorem plateauBump_hasCompactSupport {d : ℕ} {U : Set (Rd d)}
    (hU : U ⊆ closedBall 0 4) (h : ℝ) (hh : 0 < h) :
    HasCompactSupport (plateauBump U h hh) :=
  ((isCompact_closedBall (0 : Rd d) 4).cthickening).of_isClosed_subset
    (isClosed_tsupport _) ((plateauBump_tsupport_subset U h hh).trans
      (cthickening_subset_of_subset (h / 2) hU))

/-- The profile placed at a site of centre `z` and radius `s`. -/
def placedPlateauBump {d : ℕ} (U : Set (Rd d)) (h : ℝ) (hh : 0 < h)
    (M s : ℝ) (z : Rd d) : Rd d → ℝ :=
  fun x => M * plateauBump U h hh (s⁻¹ • (x - z))

theorem placedPlateauBump_isCMBounded {d : ℕ} {U : Set (Rd d)}
    {h : ℝ} (hh : 0 < h) {M C s : ℝ} (hs : 0 < s) (z : Rd d)
    (hbase : HigherDimLQGMetric.IsCMBounded (fun x => M * plateauBump U h hh x) C) :
    HigherDimLQGMetric.IsCMBounded (placedPlateauBump U h hh M s z) C := by
  exact hbase.comp_affine (by exact continuous_const.mul (plateauBump_contDiff U h hh).continuous)
    hs z

theorem placedPlateauBump_sum_isCMBounded {d : ℕ} {ι : Type*} (Z : Finset ι)
    (U : ι → Set (Rd d)) {h : ℝ} (hh : 0 < h) {M C : ℝ}
    (s : ι → ℝ) (hs : ∀ i ∈ Z, 0 < s i) (z : ι → Rd d)
    (hbase : ∀ i ∈ Z, HigherDimLQGMetric.IsCMBounded
      (fun x => M * plateauBump (U i) h hh x) C) :
    HigherDimLQGMetric.IsCMBounded
      (fun x => ∑ i ∈ Z, placedPlateauBump (U i) h hh M (s i) (z i) x)
      ((Z.card : ℝ) * C) := by
  have hi : ∀ i ∈ Z, HigherDimLQGMetric.IsCMBounded
      (placedPlateauBump (U i) h hh M (s i) (z i)) C := by
    intro i hi
    exact placedPlateauBump_isCMBounded hh (hs i hi) (z i) (hbase i hi)
  have hc : ∀ i ∈ Z, Continuous (placedPlateauBump (U i) h hh M (s i) (z i)) := by
    intro i _
    have ha : Continuous (fun x : Rd d => (s i)⁻¹ • (x - z i)) := by fun_prop
    exact continuous_const.mul ((plateauBump_contDiff (U i) h hh).continuous.comp ha)
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    (HigherDimLQGMetric.IsCMBounded.sum Z hc hi)

/-- A uniform smooth plateau and its quantitative Cameron–Martin bound. The
same `C` applies to every closed plateau in the radius-four ball and every
`h ∈ (0,1]`. -/
theorem bump_energy {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Rd d)) (h M : ℝ) (hh : 0 < h),
      h ≤ 1 → 0 ≤ M → U ⊆ closedBall 0 4 →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => M * plateauBump U h hh x) ∧
      HasCompactSupport (fun x => M * plateauBump U h hh x) ∧
      (∀ x ∈ U, M * plateauBump U h hh x = M) ∧
      (∀ x, 0 ≤ M * plateauBump U h hh x ∧ M * plateauBump U h hh x ≤ M) ∧
      tsupport (fun x => M * plateauBump U h hh x) ⊆ cthickening (h / 2) U ∧
      HigherDimLQGMetric.IsCMBounded (fun x => M * plateauBump U h hh x)
        (C * M * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ))) := by
  obtain ⟨C, hC, hcm⟩ := q7a_plateau_cm_uniform hd
  refine ⟨C, hC, ?_⟩
  intro U h M hh hh1 hM hU
  have hsm := plateauBump_contDiff U h hh
  have hcompact := plateauBump_hasCompactSupport hU h hh
  have hcm0 := hcm U h hh hh1 hU
  constructor
  · exact contDiff_const.mul hsm
  constructor
  · exact hcompact.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_mul_subset_right.trans Subset.rfl)
  constructor
  · intro x hx
    rw [plateauBump_eq_one U h hh hx]
    ring
  constructor
  · intro x
    obtain ⟨hψ0, hψ1⟩ := plateauBump_mem_Icc U h hh x
    exact ⟨mul_nonneg hM hψ0,
      (mul_le_mul_of_nonneg_left hψ1 hM).trans_eq (mul_one M)⟩
  constructor
  · exact tsupport_mul_subset_right.trans (plateauBump_tsupport_subset U h hh)
  · have hmul := hcm0.mul_const M
    apply hmul.mono
    rw [abs_of_nonneg hM]
    exact le_of_eq (by ring)

/-- One quantitative constant works for all plateaus, all their placements,
and every finite sum of placed profiles. -/
theorem bump_energy_placed_sum {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (U : Set (Rd d)) (h M : ℝ) (hh : 0 < h),
        h ≤ 1 → 0 ≤ M → U ⊆ closedBall 0 4 →
        HigherDimLQGMetric.IsCMBounded (fun x => M * plateauBump U h hh x)
          (C * M * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)))) ∧
      (∀ {ι : Type*} (Z : Finset ι) (U : ι → Set (Rd d))
        (h M : ℝ) (hh : 0 < h), h ≤ 1 → 0 ≤ M →
        (s : ι → ℝ) → (∀ i ∈ Z, 0 < s i) →
        (∀ i ∈ Z, U i ⊆ closedBall 0 4) → (z : ι → Rd d) →
        HigherDimLQGMetric.IsCMBounded
          (fun x => ∑ i ∈ Z, placedPlateauBump (U i) h hh M (s i) (z i) x)
          ((Z.card : ℝ) * C * M * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)))) := by
  obtain ⟨C, hC, hcm⟩ := q7a_plateau_cm_uniform hd
  have hscaled (U : Set (Rd d)) (h M : ℝ) (hh : 0 < h)
      (hh1 : h ≤ 1) (hM : 0 ≤ M) (hU : U ⊆ closedBall 0 4) :
      HigherDimLQGMetric.IsCMBounded (fun x => M * plateauBump U h hh x)
        (C * M * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ))) := by
    have hbase := (hcm U h hh hh1 hU).mul_const M
    apply hbase.mono
    rw [abs_of_nonneg hM]
    exact le_of_eq (by ring)
  refine ⟨C, hC, hscaled, ?_⟩
  intro ι Z U h M hh hh1 hM s hs hU z
  have hbase : ∀ i ∈ Z, HigherDimLQGMetric.IsCMBounded
      (fun x => M * plateauBump (U i) h hh x)
      (C * M * h ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ))) := by
    intro i hi
    exact hscaled (U i) h M hh hh1 hM (hU i hi)
  have hsum := placedPlateauBump_sum_isCMBounded Z U hh s hs z hbase
  convert hsum using 1
  ring



end HigherDimLQGContinuity

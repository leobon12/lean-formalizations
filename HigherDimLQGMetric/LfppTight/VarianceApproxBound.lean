import HigherDimLQGMetric.LfppTight.MeasureAbsSub

/-! Uniform covariance bound for the compact tests defining the convolved sphere mean. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_meanCenteredTrunc_measure_le {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1) (n : ℕ)
    {η : ℝ} (hη : 0 < η) :
    let A := ∫ w : Rd d, |convKernel κ w|
    let m := ∫ w : Rd d, l2b_meanTruncTest hd hκ hε.1 n w
    posM (fun w : Rd d =>
      |l2b_meanTruncTest hd hκ hε.1 n w - m * sphMol η (0 : Rd d) 1 w|) ≤
      l6a_kernelEnvelope κ ε + ENNReal.ofReal A • sphLaw 1 (0 : Rd d) η := by
  let T : Rd d → ℝ := l2b_meanTruncTest hd hκ hε.1 n
  let S : Rd d → ℝ := sphMol η (0 : Rd d) 1
  let m : ℝ := ∫ w : Rd d, T w
  let A : ℝ := ∫ w : Rd d, |convKernel κ w|
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hSm : Measurable S := (sphMol η (0 : Rd d) 1).continuous.measurable
  have hS0 (w : Rd d) : 0 ≤ S w := sphMol_nonneg hη 0 1 w
  have hTmeas : Measurable T :=
    (l2b_meanTruncTest hd hκ hε.1 n).continuous.measurable
  have hsub := l6a_posM_abs_sub_le T (fun w => m * S w)
    hTmeas (measurable_const.mul hSm)
  have h1 : posM (fun w => |T w|) ≤ l6a_kernelEnvelope κ ε :=
    l6a_meanTrunc_measure_le_conv hd hκ hε.1 n
  have h2 : posM (fun w => |m * S w|) =
      ENNReal.ofReal |m| • sphLaw 1 (0 : Rd d) η := by
    rw [l6a_posM_abs_const_mul S hSm hS0 m,
      posM_sphMol (by omega : 1 ≤ d) hη]
  have hm : |m| ≤ A := l6a_massTrunc_abs_le hd hκ hε n
  have h3 : ENNReal.ofReal |m| • sphLaw 1 (0 : Rd d) η ≤
      ENNReal.ofReal A • sphLaw 1 (0 : Rd d) η := by
    intro s
    simp only [Measure.smul_apply]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hm) zero_le
  change posM (fun w => |T w - m * S w|) ≤ _
  calc
    _ ≤ posM (fun w => |T w|) + posM (fun w => |m * S w|) := hsub
    _ ≤ l6a_kernelEnvelope κ ε + ENNReal.ofReal A • sphLaw 1 (0 : Rd d) η := by
      rw [h2]
      exact add_le_add h1 h3

theorem l6a_totalEnvelope_bounds {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    let A := ∫ w : Rd d, |convKernel κ w|
    let B := ∫ w : Rd d, |convKernel κ w| * Real.log (2 + ‖w‖)
    let lam := l6a_kernelEnvelope κ ε +
      ENNReal.ofReal A • sphLaw 1 (0 : Rd d) η
    IsFiniteMeasure lam ∧
      lam.real univ = 2 * A ∧
      (∀ z : Rd d, ∀ s > 0,
        lam.real (closedBall z s) ≤ ((2 ^ d : ℝ) * 2 * A) * s) ∧
      Integrable (fun z : Rd d => Real.log (2 + ‖z‖)) lam ∧
      (∫ z : Rd d, Real.log (2 + ‖z‖) ∂lam) ≤
        A * Real.log 3 + B + A * Real.log 4 := by
  let A : ℝ := ∫ w : Rd d, |convKernel κ w|
  let B : ℝ := ∫ w : Rd d, |convKernel κ w| * Real.log (2 + ‖w‖)
  let μ : Measure (Rd d) := l6a_kernelEnvelope κ ε
  let σ : Measure (Rd d) := sphLaw 1 (0 : Rd d) η
  let lam : Measure (Rd d) := μ + ENNReal.ofReal A • σ
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨hμfin, hμmass, hμball, hμmom, hμmom_le⟩ :=
    l6a_kernelEnvelope_bounds hd hκ hε
  obtain ⟨hσball, hσmom, hσmom_le⟩ := l6a_sphLaw_eta_bounds hd hη0 hη1
  letI : IsFiniteMeasure μ := hμfin
  letI : IsProbabilityMeasure σ := isProbabilityMeasure_sphLaw (by omega : 1 ≤ d) 1 0 η
  letI : IsFiniteMeasure (ENNReal.ofReal A • σ) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, measure_univ]
    simp
  letI : IsFiniteMeasure lam := by
    dsimp [lam]
    infer_instance
  have hmass : lam.real univ = 2 * A := by
    dsimp [lam]
    rw [measureReal_add_apply, measureReal_ennreal_smul_apply,
      ENNReal.toReal_ofReal hA, hμmass]
    have hσmass : σ.real univ = 1 := probReal_univ
    rw [hσmass]
    ring
  have hball (z : Rd d) (s : ℝ) (hs : 0 < s) :
      lam.real (closedBall z s) ≤ ((2 ^ d : ℝ) * 2 * A) * s := by
    dsimp [lam]
    rw [measureReal_add_apply, measureReal_ennreal_smul_apply,
      ENNReal.toReal_ofReal hA]
    have h1 := hμball z s hs
    have h2 := hσball z s hs
    nlinarith [mul_le_mul_of_nonneg_left h2 hA]
  have hsmul : Integrable (fun z : Rd d => Real.log (2 + ‖z‖))
      (ENNReal.ofReal A • σ) := hσmom.smul_measure ENNReal.ofReal_ne_top
  have hm : Integrable (fun z : Rd d => Real.log (2 + ‖z‖)) lam :=
    (integrable_add_measure).2 ⟨hμmom, hsmul⟩
  have hmle : (∫ z : Rd d, Real.log (2 + ‖z‖) ∂lam) ≤
      A * Real.log 3 + B + A * Real.log 4 := by
    dsimp [lam]
    rw [integral_add_measure hμmom hsmul,
      integral_smul_measure, ENNReal.toReal_ofReal hA]
    simp only [smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hσmom_le hA]
  exact ⟨inferInstance, hmass, hball, hm, hmle⟩

theorem l6a_uniform_meanTrunc_logCov {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) 1) (n : ℕ),
      let η : ℝ := ((2 : ℝ) ^ n)⁻¹
      let m : ℝ := ∫ w : Rd d, l2b_meanTruncTest hd hκ hε.1 n w
      |logCovRd
        (fun w : Rd d => l2b_meanTruncTest hd hκ hε.1 n w -
          m * sphMol η (0 : Rd d) 1 w)
        (fun w : Rd d => l2b_meanTruncTest hd hκ hε.1 n w -
          m * sphMol η (0 : Rd d) 1 w)| ≤ C := by
  let A : ℝ := ∫ w : Rd d, |convKernel κ w|
  let B : ℝ := ∫ w : Rd d, |convKernel κ w| * Real.log (2 + ‖w‖)
  let D : ℝ := (2 ^ d : ℝ) * 2 * A
  let E : ℝ := A * Real.log 3 + B + A * Real.log 4
  let C : ℝ := D * (2 * A) + 2 * (2 * A) * E
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun x =>
    mul_nonneg (abs_nonneg _) (Real.log_nonneg (by nlinarith [norm_nonneg x]))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε n
  let η : ℝ := ((2 : ℝ) ^ n)⁻¹
  let m : ℝ := ∫ w : Rd d, l2b_meanTruncTest hd hκ hε.1 n w
  let f : Rd d → ℝ := fun w =>
    l2b_meanTruncTest hd hκ hε.1 n w - m * sphMol η (0 : Rd d) 1 w
  let lam : Measure (Rd d) := l6a_kernelEnvelope κ ε +
    ENNReal.ofReal A • sphLaw 1 (0 : Rd d) η
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  obtain ⟨hlam, hmass, hball, hmom, hmom_le⟩ :=
    l6a_totalEnvelope_bounds hd hκ hε hη0 hη1
  letI : IsFiniteMeasure lam := hlam
  have hf : Integrable f := by
    dsimp [f]
    exact (integrable_testOn (l2b_meanTruncTest hd hκ hε.1 n)).sub
      ((integrable_testOn (sphMol η (0 : Rd d) 1)).const_mul m)
  have hfm : Measurable f := by
    dsimp [f]
    exact (l2b_meanTruncTest hd hκ hε.1 n).continuous.measurable.sub
      (measurable_const.mul (sphMol η (0 : Rd d) 1).continuous.measurable)
  have hdom : posM (fun w => |f w|) ≤ lam :=
    l6a_meanCenteredTrunc_measure_le hd hκ hε n hη0
  have hlog : Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖)
      (lam.prod lam) :=
    integrable_log_norm_sub_of_smallBall_logMoment hD hball hmom
  have hcov := l6a_abs_logCovRd_le_energy f hf hfm lam hdom hlog
  have henergy := l6a_abs_log_energy_le hD hball hmom
  change (∫ p : Rd d × Rd d, |Real.log ‖p.1 - p.2‖| ∂(lam.prod lam)) ≤
    D * lam.real univ + 2 * lam.real univ *
      (∫ z : Rd d, Real.log (2 + ‖z‖) ∂lam) at henergy
  change |logCovRd f f| ≤ C
  calc
    |logCovRd f f| ≤
        ∫ p : Rd d × Rd d, |Real.log ‖p.1 - p.2‖| ∂(lam.prod lam) := hcov
    _ ≤ D * lam.real univ + 2 * lam.real univ *
      (∫ z : Rd d, Real.log (2 + ‖z‖) ∂lam) := henergy
    _ ≤ C := by
      rw [hmass]
      dsimp [C, E]
      have h2A : 0 ≤ 2 * A := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hmom_le
        (show 0 ≤ (2 : ℝ) * (2 * A) by positivity)]

end HigherDimLQGMetric

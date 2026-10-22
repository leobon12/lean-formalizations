import HigherDimLQGMetric.Kernel.FourierLogCov

/-!
# Fubini for spectral covariance

Pairability gives integrability of the nonnegative spectral square.  The
cross-spectrum is dominated by half the sum of the two squares.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory FourierTransform Complex Set
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

def scaleSpectralSquare (κ : Rd d → ℝ) (t : ℝ)
    (μ ν : Measure (Rd d)) (ξ : Rd d) : ℝ :=
  t ^ ((d : ℝ) - 1) *
    ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 *
    ‖measureFourier μ ξ - measureFourier ν ξ‖ ^ 2

theorem scaleSpectralSquare_nonneg {t : ℝ} (ht : 0 < t)
    (μ ν : Measure (Rd d)) (ξ : Rd d) :
    0 ≤ scaleSpectralSquare κ t μ ν ξ := by
  unfold scaleSpectralSquare
  positivity

theorem integrable_scaleSpectralSquare
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (scaleSpectralSquare κ t μ ν) := by
  let B := (μ.real univ + ν.real univ) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdom : Integrable (fun ξ : Rd d =>
      B * (t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2)) :=
    (integrable_scaleSpectral hκ ht).const_mul B
  apply Integrable.mono' hdom
  · have hc := continuous_fourier_kernel hκ
    have hm := measurable_measureFourier μ
    have hn := measurable_measureFourier ν
    have h : Measurable (scaleSpectralSquare κ t μ ν) := by
      unfold scaleSpectralSquare
      fun_prop
    exact h.aestronglyMeasurable
  · exact ae_of_all _ fun ξ => by
      have hm := measureFourier_norm_le μ ξ
      have hn := measureFourier_norm_le ν ξ
      have hmn : ‖measureFourier μ ξ - measureFourier ν ξ‖ ≤
          μ.real univ + ν.real univ :=
        (norm_sub_le _ _).trans (add_le_add hm hn)
      have hmn0 : 0 ≤ μ.real univ + ν.real univ := by positivity
      have hs : 0 ≤ t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 := by positivity
      unfold scaleSpectralSquare
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs (sq_nonneg _))]
      calc
        t ^ ((d : ℝ) - 1) *
            ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 *
            ‖measureFourier μ ξ - measureFourier ν ξ‖ ^ 2 ≤
          (μ.real univ + ν.real univ) ^ 2 *
            (t ^ ((d : ℝ) - 1) *
              ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) hmn 2) hs

theorem scalePair_self_eq_fourier
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    HigherDimLFPP.scalePair κ t μ ν μ ν =
      ∫ ξ : Rd d, scaleSpectralSquare κ t μ ν ξ := by
  have hc := scalePair_eq_fourier hκ ht μ ν μ ν
  have hp (ξ : Rd d) :
      (((scaleSpectralSquare κ t μ ν ξ : ℝ) : ℂ)) =
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
          (conj (measureFourier μ ξ) - conj (measureFourier ν ξ)) *
          (measureFourier μ ξ - measureFourier ν ξ) := by
    unfold scaleSpectralSquare
    rw [← map_sub]
    let z := measureFourier μ ξ - measureFourier ν ξ
    change ((t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 * ‖z‖ ^ 2 : ℝ) : ℂ) =
      ((t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
        conj z * z
    rw [Complex.ofReal_mul]
    have hz : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj']
      exact (Complex.ofReal_pow _ _).symm
    rw [mul_assoc, hz]
  have heq : (∫ ξ : Rd d,
      (((scaleSpectralSquare κ t μ ν ξ : ℝ) : ℂ))) =
      ∫ ξ : Rd d,
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
          (conj (measureFourier μ ξ) - conj (measureFourier ν ξ)) *
          (measureFourier μ ξ - measureFourier ν ξ) :=
    integral_congr_ae (ae_of_all _ hp)
  have hcast : ((HigherDimLFPP.scalePair κ t μ ν μ ν : ℝ) : ℂ) =
      ((∫ ξ : Rd d, scaleSpectralSquare κ t μ ν ξ : ℝ) : ℂ) := by
    calc
      _ = ∫ ξ : Rd d,
          ((t ^ ((d : ℝ) - 1) *
            ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
            (conj (measureFourier μ ξ) - conj (measureFourier ν ξ)) *
            (measureFourier μ ξ - measureFourier ν ξ) := hc
      _ = ∫ ξ : Rd d, (((scaleSpectralSquare κ t μ ν ξ : ℝ) : ℂ)) := heq.symm
      _ = _ := integral_complex_ofReal
  exact Complex.ofReal_inj.mp hcast

theorem integrable_scaleSpectralSquare_prod
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hp : HigherDimLFPP.IsPairable κ S μ ν) :
    Integrable (fun p : ℝ × Rd d => scaleSpectralSquare κ p.1 μ ν p.2)
      ((volume.restrict S).prod volume) := by
  have hc := continuous_fourier_kernel hκ
  have hm := measurable_measureFourier μ
  have hn := measurable_measureFourier ν
  have hmeas : Measurable (fun p : ℝ × Rd d =>
      scaleSpectralSquare κ p.1 μ ν p.2) := by
    unfold scaleSpectralSquare
    fun_prop
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem hS] with t ht
    exact integrable_scaleSpectralSquare hκ (hS0 ht) μ ν
  · have hpair := HigherDimLFPP.integrableOn_scalePair hκ hS hS0 hp hp
    apply hpair.congr
    filter_upwards [ae_restrict_mem hS] with t ht
    have ht0 := hS0 ht
    have hnorm : (fun ξ : Rd d => ‖scaleSpectralSquare κ t μ ν ξ‖) =
        scaleSpectralSquare κ t μ ν := by
      funext ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (scaleSpectralSquare_nonneg ht0 μ ν ξ)]
    rw [hnorm]
    exact scalePair_self_eq_fourier hκ ht0 μ ν

def scaleSpectralCross (κ : Rd d → ℝ) (t : ℝ)
    (μ ν μ' ν' : Measure (Rd d)) (ξ : Rd d) : ℂ :=
  ((t ^ ((d : ℝ) - 1) *
    ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
      (conj (measureFourier μ ξ) - conj (measureFourier ν ξ)) *
      (measureFourier μ' ξ - measureFourier ν' ξ)

private theorem norm_cross_le_mean_squares (s : ℝ) (hs : 0 ≤ s) (z w : ℂ) :
    ‖(s : ℂ) * conj z * w‖ ≤
      (s * ‖z‖ ^ 2 + s * ‖w‖ ^ 2) / 2 := by
  have hzw : ‖z‖ * ‖w‖ ≤ (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
  rw [norm_mul, norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs]
  calc
    s * ‖z‖ * ‖w‖ = s * (‖z‖ * ‖w‖) := by ring
    _ ≤ s * ((‖z‖ ^ 2 + ‖w‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hzw hs
    _ = _ := by ring

theorem integrable_scaleSpectralCross_prod
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hp : HigherDimLFPP.IsPairable κ S μ ν)
    (hp' : HigherDimLFPP.IsPairable κ S μ' ν') :
    Integrable (fun p : ℝ × Rd d =>
      scaleSpectralCross κ p.1 μ ν μ' ν' p.2)
      ((volume.restrict S).prod volume) := by
  have h1 := integrable_scaleSpectralSquare_prod hκ hS hS0 μ ν hp
  have h2 := integrable_scaleSpectralSquare_prod hκ hS hS0 μ' ν' hp'
  have hdom : Integrable (fun p : ℝ × Rd d =>
      (scaleSpectralSquare κ p.1 μ ν p.2 +
        scaleSpectralSquare κ p.1 μ' ν' p.2) / 2)
      ((volume.restrict S).prod volume) := (h1.add h2).div_const 2
  apply Integrable.mono' hdom
  · have hc := continuous_fourier_kernel hκ
    have hm := measurable_measureFourier μ
    have hn := measurable_measureFourier ν
    have hm' := measurable_measureFourier μ'
    have hn' := measurable_measureFourier ν'
    have h : Measurable (fun p : ℝ × Rd d =>
        scaleSpectralCross κ p.1 μ ν μ' ν' p.2) := by
      unfold scaleSpectralCross
      fun_prop
    exact h.aestronglyMeasurable
  · have hmem : ∀ᵐ p : ℝ × Rd d ∂((volume.restrict S).prod volume), p.1 ∈ S :=
      (Measure.ae_prod_iff_ae_ae (hS.preimage measurable_fst)).2 (by
        filter_upwards [ae_restrict_mem hS] with t ht
        exact ae_of_all _ fun _ => ht)
    filter_upwards [hmem] with p hpS
    have ht := hS0 hpS
    have hs : 0 ≤ p.1 ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (p.1 • p.2)‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg ht.le _) (sq_nonneg _)
    simpa only [scaleSpectralCross, scaleSpectralSquare, ← map_sub] using
      norm_cross_le_mean_squares
        (p.1 ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (p.1 • p.2)‖ ^ 2)
        hs (measureFourier μ p.2 - measureFourier ν p.2)
        (measureFourier μ' p.2 - measureFourier ν' p.2)

theorem scaleCov_eq_fourier_swapped
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hp : HigherDimLFPP.IsPairable κ S μ ν)
    (hp' : HigherDimLFPP.IsPairable κ S μ' ν') :
    ((HigherDimLFPP.scaleCov κ S μ ν μ' ν' : ℝ) : ℂ) =
      ∫ ξ : Rd d, ∫ t in S,
        scaleSpectralCross κ t μ ν μ' ν' ξ := by
  rw [scaleCov_eq_fourier hκ hS hS0 μ ν μ' ν' hp hp']
  exact integral_integral_swap
    (integrable_scaleSpectralCross_prod hκ hS hS0 μ ν μ' ν' hp hp')

theorem logCov_eq_fourier_swapped
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hmass : μ.real univ = ν.real univ)
    (hmass' : μ'.real univ = ν'.real univ)
    (hlog : HigherDimLFPP.LogPairable μ ν μ' ν') :
    ((HigherDimLFPP.logCov μ ν μ' ν' : ℝ) : ℂ) =
      ∫ ξ : Rd d, ∫ t in Ioi (0 : ℝ),
        scaleSpectralCross κ t μ ν μ' ν' ξ := by
  obtain ⟨hp, hp', hcov⟩ := HigherDimLFPP.scaleCov_eq_logCov hκ hmass hmass' hlog
  rw [← hcov]
  exact scaleCov_eq_fourier_swapped hκ measurableSet_Ioi
    (fun _ h => h) μ ν μ' ν' hp hp'

end HigherDimLQGMetric

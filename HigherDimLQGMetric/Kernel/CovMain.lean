import HigherDimLQGMetric.Kernel.CovLogBridge
import HigherDimLQGMetric.Kernel.CovPairability

/-!
# Exact covariance identity of [1, Lemma 2.9]
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set FourierTransform
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private theorem smoothedDifference_regular {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ.real univ = ν.real univ)
    {D : ℝ} (hμD : ∀ᵐ z ∂μ, ‖z‖ ≤ D)
    (hνD : ∀ᵐ z ∂ν, ‖z‖ ≤ D) :
    ∃ M : ℝ,
      Integrable (fun x : Rd d => measConv κ ε μ x - measConv κ ε ν x) ∧
      Measurable (fun x : Rd d => measConv κ ε μ x - measConv κ ε ν x) ∧
      (∀ x, |measConv κ ε μ x - measConv κ ε ν x| ≤ M) ∧
      Integrable (fun x : Rd d => Real.log (2 + ‖x‖) *
        (measConv κ ε μ x - measConv κ ε ν x)) ∧
      (∫ x : Rd d, measConv κ ε μ x - measConv κ ε ν x) = 0 := by
  have hiμ := integrable_measConv hd hκ hε μ
  have hiν := integrable_measConv hd hκ hε ν
  have hmμ := measurable_measConv hd hκ ε μ
  have hmν := measurable_measConv hd hκ ε ν
  obtain ⟨Bμ, _, hBμ⟩ := abs_measConv_le hd hκ hε μ
  obtain ⟨Bν, _, hBν⟩ := abs_measConv_le hd hκ hε ν
  refine ⟨Bμ + Bν, hiμ.sub hiν, hmμ.sub hmν, fun x => ?_, ?_, ?_⟩
  · have h := abs_sub_le (measConv κ ε μ x) 0 (measConv κ ε ν x)
    have hμ' : |measConv κ ε μ x - 0| ≤ Bμ := by
      simpa only [sub_zero] using hBμ x
    have hν' : |0 - measConv κ ε ν x| ≤ Bν := by
      simpa only [zero_sub, abs_neg] using hBν x
    exact h.trans (add_le_add hμ' hν')
  · have hwμ := integrable_logMoment_measConv hd hκ hε μ
      (integrable_logWeight_of_ae_bounded μ hμD)
    have hwν := integrable_logMoment_measConv hd hκ hε ν
      (integrable_logWeight_of_ae_bounded ν hνD)
    have h := hwμ.sub hwν
    have heq : (fun x : Rd d => Real.log (2 + ‖x‖) *
        (measConv κ ε μ x - measConv κ ε ν x)) =
        (fun x => Real.log (2 + ‖x‖) * measConv κ ε μ x) -
          (fun x => Real.log (2 + ‖x‖) * measConv κ ε ν x) := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [heq]
    exact h
  · rw [integral_sub hiμ hiν, integral_measConv_eq_mass hd hκ hε μ,
      integral_measConv_eq_mass hd hκ hε ν, hmass, sub_self]

/-- [1, Lemma 2.9]: convolution with the inverse Fourier kernel transports
the white-noise covariance above `ε` to the logarithmic covariance of the
smoothed signed densities. -/
theorem l1d_cov : L1d_cov := by
  intro d hd κ hκ ε hε μ ν μ' ν' instμ instν instμ' instν' hmass hmass' hD
  obtain ⟨D, hμD, hνD, hμ'D, hν'D⟩ := hD
  have hp := pairable_above_of_bounded_support hκ hε hmass hμD hνD
  have hp' := pairable_above_of_bounded_support hκ hε hmass' hμ'D hν'D
  refine ⟨hp, hp', ?_⟩
  let f : Rd d → ℝ := fun x => measConv κ ε μ x - measConv κ ε ν x
  let g : Rd d → ℝ := fun x => measConv κ ε μ' x - measConv κ ε ν' x
  obtain ⟨M, hf, hmf, hMf, hwf, hf0⟩ :=
    smoothedDifference_regular hd hκ hε μ ν hmass hμD hνD
  obtain ⟨M', hg, hmg, hMg, hwg, hg0⟩ :=
    smoothedDifference_regular hd hκ hε μ' ν' hmass' hμ'D hν'D
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsFiniteMeasure (posM f) := isFiniteMeasure_posM_of_integrable hf
  haveI : IsFiniteMeasure (posM (-f)) := isFiniteMeasure_posM_of_integrable hf.neg
  haveI : IsFiniteMeasure (posM g) := isFiniteMeasure_posM_of_integrable hg
  haveI : IsFiniteMeasure (posM (-g)) := isFiniteMeasure_posM_of_integrable hg.neg
  have hlog : HigherDimLFPP.LogPairable (posM f) (posM (-f))
      (posM g) (posM (-g)) :=
    logPairable_posM_of_logMoment hf hg hmf hmg hMf hMg hwf hwg
  have hmassf : (posM f).real univ = (posM (-f)).real univ := by
    have h := integral_eq_posM_sub_posM_of_integrable hf
    rw [hf0] at h
    linarith
  have hmassg : (posM g).real univ = (posM (-g)).real univ := by
    have h := integral_eq_posM_sub_posM_of_integrable hg
    rw [hg0] at h
    linarith
  have hbridge : HigherDimLFPP.logCov (posM f) (posM (-f))
      (posM g) (posM (-g)) = convLogCov κ ε μ ν μ' ν' := by
    rw [logCov_posM_of_pairable hmf hmg hlog,
      logCovF_eq_iterated_of_pairable hmf hmg hlog]
    rfl
  have hs := scaleCov_eq_kernelSymbol_fourier (by omega : 0 < d) hκ
    hε.le μ ν μ' ν' hp hp'
  have hl := logCov_eq_universal_fourier (by omega : 0 < d) hκ
    (posM f) (posM (-f)) (posM g) (posM (-g)) hmassf hmassg hlog
  apply Complex.ofReal_inj.mp
  rw [hs, ← hbridge, hl]
  apply integral_congr_ae
  exact ae_of_all _ fun ζ => by
    have hF := measureFourier_smoothed_sub hd hκ hε μ ν ζ
    have hG := measureFourier_smoothed_sub hd hκ hε μ' ν' ζ
    change measureFourier (posM f) ζ - measureFourier (posM (-f)) ζ =
      (kernelSymbol κ (ε • ζ) : ℂ) *
        (measureFourier μ ζ - measureFourier ν ζ) at hF
    change measureFourier (posM g) ζ - measureFourier (posM (-g)) ζ =
      (kernelSymbol κ (ε • ζ) : ℂ) *
        (measureFourier μ' ζ - measureFourier ν' ζ) at hG
    change ((‖ζ‖ ^ (-(d : ℝ)) *
        (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2))⁻¹ *
        (kernelSymbol κ (ε • ζ)) ^ 2 : ℝ) : ℂ) *
        (conj (measureFourier μ ζ) - conj (measureFourier ν ζ)) *
        (measureFourier μ' ζ - measureFourier ν' ζ) =
      ((‖ζ‖ ^ (-(d : ℝ)) *
        (2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2))⁻¹ : ℝ) : ℂ) *
        (conj (measureFourier (posM f) ζ) -
          conj (measureFourier (posM (-f)) ζ)) *
        (measureFourier (posM g) ζ - measureFourier (posM (-g)) ζ)
    have hconj : conj (measureFourier (posM f) ζ) -
        conj (measureFourier (posM (-f)) ζ) =
        conj ((kernelSymbol κ (ε • ζ) : ℂ) *
          (measureFourier μ ζ - measureFourier ν ζ)) := by
      simpa only [← map_sub] using congrArg conj hF
    rw [hconj, hG]
    simp only [map_mul, map_sub, Complex.conj_ofReal,
      Complex.ofReal_mul, Complex.ofReal_pow]
    ring

end HigherDimLQGMetric

import QuantumZipper.Proofs.GFF.K3.MixedM7D4

/-!
# K3-mixed M7-a3, half-disc covariance, step D5: polarization and the disc-kernel node

From the reflection identity (D4, `dualNormSq_halfDisc_eq_m7d`) by polarization,

  `dualCov U V₀ μ ν = ½ dualCov B (zeroSpace B) μ̃ ν̃`,  `μ̃ = μ + conj_* μ`
  (`dualCov_halfDisc_eq_m7d`),

so the explicit half-disc covariance `HalfDiscMixedCovStmt t r r'` follows from the covariance of
the zero-boundary field of the disc `B = ball t r` at symmetrized measures
(`HalfDiscDiscKernelStmt`, the remaining node: `G_U(z,w) = G_B(z,w) + G_B(z,w̄)`, Sheffield,
*Gaussian free fields for mathematicians* (2007), §2.2, via the Cayley map of `B` onto `ℍ`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Real Topology ComplexConjugate ENNReal

namespace QuantumZipper.K3

/-- **D5 (polarized reflection identity).** -/
theorem dualCov_halfDisc_eq_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r)
    {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμH : ∀ᵐ z ∂μ, z ∈ Hbar) (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0)
    (hνH : ∀ᵐ z ∂ν, z ∈ Hbar) (hνK : ν (closedBall (t : ℂ) r')ᶜ = 0) :
    dualCov (ball (t : ℂ) r ∩ H)
        (mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r)))) μ ν =
      dualCov (ball (t : ℂ) r) (zeroSpace (ball (t : ℂ) r)) (μ + μ.map conj)
        (ν + ν.map conj) / 2 := by
  have hconjm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hadd : (μ + ν) + (μ + ν).map conj = (μ + μ.map conj) + (ν + ν.map conj) := by
    rw [Measure.map_add _ _ hconjm, add_add_add_comm]
  have hH : ∀ᵐ z ∂(μ + ν), z ∈ Hbar := ae_add_measure_iff.2 ⟨hμH, hνH⟩
  have hK : (μ + ν) (closedBall (t : ℂ) r')ᶜ = 0 := by
    rw [Measure.add_apply, hμK, hνK, add_zero]
  unfold dualCov
  rw [dualNormSq_halfDisc_eq_m7d hr' hr'r hH hK, hadd, dualNormSq_halfDisc_eq_m7d hr' hr'r hμH hμK,
    dualNormSq_halfDisc_eq_m7d hr' hr'r hνH hνK]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  ring

/-- Admissible measures live on `Hbar`. -/
theorem ae_Hbar_of_isAdmissibleH_m7d {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    ∀ᵐ z ∂μ, z ∈ Hbar := by
  obtain ⟨-, ⟨K, -, hKH, hμK⟩, -⟩ := hμ
  filter_upwards [mem_ae_iff.2 hμK] with z hz using hKH hz

/-- **Remaining node (disc kernel).** The covariance of the zero-boundary field of the disc
`ball t r` at the symmetrized local measures is twice the half-disc Green kernel. -/
def HalfDiscDiscKernelStmt (t r r' : ℝ) : Prop :=
  0 < r' → r' < r → ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
    IsAdmissibleH ν → ν (closedBall (t : ℂ) r')ᶜ = 0 →
      dualCov (ball (t : ℂ) r) (zeroSpace (ball (t : ℂ) r)) (μ + μ.map conj) (ν + ν.map conj) =
        2 * kernelCov (halfDiscGreen t r) μ ν

/-- **D5: the half-disc covariance from the disc kernel.** -/
theorem halfDiscMixedCov_of_discKernel {t r r' : ℝ} (h : HalfDiscDiscKernelStmt t r r') :
    HalfDiscMixedCovStmt t r r' := by
  intro hr' hr'r μ ν hμ hμK hν hνK
  have := hμ.1; have := hν.1
  rw [dualCov_halfDisc_eq_m7d hr' hr'r (ae_Hbar_of_isAdmissibleH_m7d hμ) hμK
    (ae_Hbar_of_isAdmissibleH_m7d hν) hνK, h hr' hr'r μ ν hμ hμK hν hνK]
  ring

end QuantumZipper.K3

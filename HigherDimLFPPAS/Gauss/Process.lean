import HigherDimLFPPAS.Signed.Radial
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Sphere.Proc
import LQGMetric.Field.CircleAvgIndep

/-!
# Gaussianity of the signed-seed convolution field

The compact truncations of the convolution kernel need not have zero mass. We subtract their mass
times a shrinking mollified unit-sphere test. The subtraction is a mean-zero test pairing at every
finite stage, and its limit vanishes on the normalization event `h₁(0) = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace HigherDimLFPPAS.Gauss

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- A compact, mean-zero test obtained by subtracting the mass of a convolution truncation against
a mollified unit-sphere average. -/
def centeredConvTruncTestF2 (hd : 2 ≤ d) (p : ℝ × Rd d) (n : ℕ) : TestRd0 d :=
  testSub0 (convTrunc κ (Real.exp (-p.1)) p.2 n)
    ((∫ w : Rd d, convTrunc κ (Real.exp (-p.1)) p.2 n w) •
      sphMol (((2 : ℝ) ^ n)⁻¹) 0 1) (by
        change (∫ w : Rd d, convTrunc κ (Real.exp (-p.1)) p.2 n w) =
          ∫ w : Rd d, (∫ w : Rd d, convTrunc κ (Real.exp (-p.1)) p.2 n w) *
            sphMol (((2 : ℝ) ^ n)⁻¹) 0 1 w
        rw [integral_const_mul, integral_sphMol (by omega) (by positivity) 0 1]
        simp)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

/-- Almost-sure convergence of the centered compact test pairings to the pathwise convolution
field. -/
theorem ae_tendsto_centeredConvTruncTestF2 (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (hh : IsNormalizedLGF h P)
    (p : ℝ × Rd d) :
    ∀ᵐ ω ∂P, Tendsto (fun n => h ω (centeredConvTruncTestF2 (κ := κ) hd p n).1) atTop
      (𝓝 (convMollify κ (Real.exp (-p.1)) (h ω) p.2)) := by
  filter_upwards [@HigherDimLFPPAS.Signed.l2b_ae_convMollify_tendsto_seed
      d hd κ hκ Ω inferInstance P inferInstance h hh,
    @HigherDimLQGMetric.IsWholeSpaceLGF.ae_tendsto_sphProc
      d Ω inferInstance P h hd hh.1 0 1 le_rfl one_pos 0, hh.2]
    with ω htrunc hsphere hnorm
  have hε : 0 < Real.exp (-p.1) := Real.exp_pos _
  have hraw : Tendsto (fun n => h ω (convTrunc κ (Real.exp (-p.1)) p.2 n)) atTop
      (𝓝 (convMollify κ (Real.exp (-p.1)) (h ω) p.2)) := by
    have ht := htrunc (Real.exp (-p.1)) hε p.2
    have heq := l2b_convMollify_eq_of_tendsto ht
    rw [← heq] at ht
    exact ht
  have hmass : Tendsto
      (fun n : ℕ => ∫ w : Rd d, convTrunc κ (Real.exp (-p.1)) p.2 n w)
      atTop (𝓝 1) :=
    HigherDimLFPPAS.Signed.l2b_tendsto_integral_convTrunc_seed
      (hd := hd) (hκ := hκ) hε p.2
  have hsphere' : Tendsto
      (fun n : ℕ => h ω (sphMol (((2 : ℝ) ^ n)⁻¹) 0 1)) atTop (𝓝 0) := by
    have hs := hsphere
    rw [sphProc_zero, hnorm] at hs
    simpa only [approxScale_zero] using hs
  have hprod := hmass.mul hsphere'
  have hdiff : Tendsto
      (fun n : ℕ => h ω (convTrunc κ (Real.exp (-p.1)) p.2 n) -
        (∫ w : Rd d, convTrunc κ (Real.exp (-p.1)) p.2 n w) *
          h ω (sphMol (((2 : ℝ) ^ n)⁻¹) 0 1))
      atTop (𝓝 (convMollify κ (Real.exp (-p.1)) (h ω) p.2)) := by
    simpa only [sub_zero, mul_zero] using hraw.sub hprod
  have hpair (n : ℕ) : h ω (centeredConvTruncTestF2 (κ := κ) hd p n).1 =
      h ω (convTrunc κ (Real.exp (-p.1)) p.2 n) -
        (∫ w : Rd d, convTrunc κ (Real.exp (-p.1)) p.2 n w) *
          h ω (sphMol (((2 : ℝ) ^ n)⁻¹) 0 1) := by
    simp only [centeredConvTruncTestF2, testSub0_val, map_sub, map_smul, smul_eq_mul]
  exact hdiff.congr' (Filter.Eventually.of_forall fun n => (hpair n).symm)

/-- For every admissible signed seed, the pathwise convolution field indexed by logarithmic scale
and location is a centered Gaussian process. -/
theorem convMollify_isGaussianProcess_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (hh : IsNormalizedLGF h P) :
    IsGaussianProcess
      (fun p : ℝ × Rd d => fun ω =>
        convMollify κ (Real.exp (-p.1)) (h ω) p.2) P := by
  let Y : ℝ × Rd d → Ω → ℝ := fun p ω =>
    convMollify κ (Real.exp (-p.1)) (h ω) p.2
  let Yn : ℕ → ℝ × Rd d → Ω → ℝ := fun n p ω =>
    h ω (centeredConvTruncTestF2 (κ := κ) hd p n).1
  have hG (n : ℕ) : IsGaussianProcess (Yn n) P := by
    exact hh.1.gaussian.comp_right (centeredConvTruncTestF2 (κ := κ) hd · n)
  have hC (n : ℕ) (p : ℝ × Rd d) : ∫ ω, Yn n p ω ∂P = 0 :=
    hh.1.centered (centeredConvTruncTestF2 (κ := κ) hd p n)
  have hm (p : ℝ × Rd d) : Measurable (Y p) := by
    have hm' (n : ℕ) : StronglyMeasurable fun ω : Ω =>
        h ω (convTrunc κ (Real.exp (-p.1)) p.2 n) :=
      ((measurable_distOn_apply _).comp hh.1.measurable).stronglyMeasurable
    exact (StronglyMeasurable.limUnder (l := atTop) hm').measurable
  have hlim (p : ℝ × Rd d) : ∀ᵐ ω ∂P,
      Tendsto (fun n => Yn n p ω) atTop (𝓝 (Y p ω)) := by
    simpa only [Yn, Y] using ae_tendsto_centeredConvTruncTestF2 hd hκ hh p
  simpa only [Y] using LQGMetric.CircleAvgIndep.isGaussianProcess_of_ae_tendsto hG hC hm hlim

/-- The covariance of the pathwise convolution field is the limit of the logarithmic covariances
of its centered compact test approximations. -/
theorem convMollify_covariance_tendsto_test_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (hh : IsNormalizedLGF h P)
    (p q : ℝ × Rd d) :
    Tendsto
      (fun n : ℕ => logCovRd (centeredConvTruncTestF2 (κ := κ) hd p n).1
        (centeredConvTruncTestF2 (κ := κ) hd q n).1)
      atTop
      (𝓝 (cov[fun ω => convMollify κ (Real.exp (-p.1)) (h ω) p.2,
        fun ω => convMollify κ (Real.exp (-q.1)) (h ω) q.2; P])) := by
  let Y : ℝ × Rd d → Ω → ℝ := fun p ω =>
    convMollify κ (Real.exp (-p.1)) (h ω) p.2
  let Yn : ℕ → ℝ × Rd d → Ω → ℝ := fun n p ω =>
    h ω (centeredConvTruncTestF2 (κ := κ) hd p n).1
  have hG (n : ℕ) : IsGaussianProcess (Yn n) P :=
    hh.1.gaussian.comp_right (centeredConvTruncTestF2 (κ := κ) hd · n)
  have hC (n : ℕ) (p : ℝ × Rd d) : ∫ ω, Yn n p ω ∂P = 0 :=
    hh.1.centered (centeredConvTruncTestF2 (κ := κ) hd p n)
  have hm (p : ℝ × Rd d) : Measurable (Y p) := by
    have hm' (n : ℕ) : StronglyMeasurable fun ω : Ω =>
        h ω (convTrunc κ (Real.exp (-p.1)) p.2 n) :=
      ((measurable_distOn_apply _).comp hh.1.measurable).stronglyMeasurable
    exact (StronglyMeasurable.limUnder (l := atTop) hm').measurable
  have hlim (p : ℝ × Rd d) : ∀ᵐ ω ∂P,
      Tendsto (fun n => Yn n p ω) atTop (𝓝 (Y p ω)) := by
    simpa only [Yn, Y] using ae_tendsto_centeredConvTruncTestF2 hd hκ hh p
  have ht := LQGMetric.CircleAvgIndep.tendsto_covariance_of_ae_tendsto hG hC hm hlim p q
  simpa only [Yn, Y, hh.1.covariance_eq] using ht

/-- Variances of the Gaussian convolution field are limits of the test-pairing logarithmic
energies. This reduces (A.4) to a deterministic logarithmic-energy estimate. -/
theorem convMollify_variance_tendsto_test_seed (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (hh : IsNormalizedLGF h P)
    (p : ℝ × Rd d) :
    Tendsto
      (fun n : ℕ => logCovRd (centeredConvTruncTestF2 (κ := κ) hd p n).1
        (centeredConvTruncTestF2 (κ := κ) hd p n).1)
      atTop
      (𝓝 (Var[fun ω => convMollify κ (Real.exp (-p.1)) (h ω) p.2; P])) := by
  have hlim := convMollify_covariance_tendsto_test_seed hd hκ hh p p
  have hG := (convMollify_isGaussianProcess_seed hd hκ hh).hasGaussianLaw_eval p
  simpa only [covariance_self hG.aemeasurable] using hlim

end HigherDimLFPPAS.Gauss

import HigherDimLQGMetric.LfppTight.SphereMeanFar
import HigherDimLQGMetric.Sphere.Conv
import LQGMetric.Field.CircleAvgIndep

/-! A7(2): the convolved sphere mean is a centered Gaussian random variable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l6a_meanCenteredTest {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) : TestRd0 d := by
  let η : ℝ := ((2 : ℝ) ^ n)⁻¹
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨l2b_meanTruncTest hd hκ hε n -
    (∫ w : Rd d, l2b_meanTruncTest hd hκ hε n w) •
      sphMol η (0 : Rd d) 1, ?_⟩
  change (∫ w : Rd d, l2b_meanTruncTest hd hκ hε n w -
    (∫ w : Rd d, l2b_meanTruncTest hd hκ hε n w) *
      sphMol η (0 : Rd d) 1 w) = 0
  rw [integral_sub (integrable_testOn _) ((integrable_testOn _).const_mul _),
    integral_const_mul, integral_sphMol (by omega : 1 ≤ d) hη,
    mul_one, sub_self]

theorem l6a_gaussianClosure_sphereMean {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) :
    HasGaussianLaw (fun ω => l6a_convSphereMean κ ε (h ω)) P ∧
      ∫ ω, l6a_convSphereMean κ ε (h ω) ∂P = 0 ∧
      Tendsto (fun n => Var[(fun ω =>
        h ω (l6a_meanCenteredTest hd hκ hε n).1); P]) atTop
        (𝓝 (Var[fun ω => l6a_convSphereMean κ ε (h ω); P])) := by
  let mass : ℕ → ℝ := fun n => ∫ w : Rd d, l2b_meanTruncTest hd hκ hε n w
  let f : ℕ → TestRd0 d := l6a_meanCenteredTest hd hκ hε
  let Y : ℕ → Ω → ℝ := fun n ω => h ω (f n).1
  have hG (n : ℕ) : HasGaussianLaw (Y n) P :=
    hh.1.gaussian.hasGaussianLaw_eval (f n)
  have hmean (n : ℕ) : ∫ ω, Y n ω ∂P = 0 := hh.1.centered (f n)
  have hmass : Tendsto mass atTop (𝓝 (1 : ℝ)) := by
    have ht := l2b_tendsto_integral_convTrunc hd hκ hε (0 : Rd d)
    convert ht using 1
    funext n
    exact l2b_integral_meanTruncTest hd hκ hε n
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop
      (𝓝 (l6a_convSphereMean κ ε (h ω))) := by
    filter_upwards [l2b_ae_tendsto_sphereMean_convTrunc d hd κ hκ P h hh,
      hh.1.ae_exists_tendsto_sphereAvgSeq hd one_pos (0 : Rd d), hh.2]
      with ω hX hS hzero
    have h1 : Tendsto (fun n => h ω (l2b_meanTruncTest hd hκ hε n)) atTop
        (𝓝 (l6a_convSphereMean κ ε (h ω))) := by
      simpa only [l6a_convSphereMean,
        l2b_meanTruncTest_pair hd hκ hε] using hX ε hε
    have h2 : Tendsto (fun n => h ω (sphMol (((2 : ℝ) ^ n)⁻¹)
        (0 : Rd d) 1)) atTop (𝓝 (0 : ℝ)) := by
      have ht := tendsto_sphereAvgSeq_sphereAvg hS
      rw [hzero] at ht
      have heq : (fun n => h ω (sphMol (((2 : ℝ) ^ n)⁻¹)
          (0 : Rd d) 1)) = sphereAvgSeq (h ω) 1 0 := by
        funext n
        exact (sphereAvgSeq_eq_apply_sphMol (h ω) 1 0 n).symm
      rw [heq]
      exact ht
    have ht := h1.sub (hmass.mul h2)
    simpa only [Y, f, l6a_meanCenteredTest, map_sub, map_smul, smul_eq_mul,
      mass, mul_zero, sub_zero] using ht
  have hm := l6a_aemeasurable_sphereMean hd κ hκ P h hh hε
  obtain ⟨hG', hmean', hvar⟩ :=
    LQGMetric.CircleAvgIndep.gaussian_of_ae_tendsto hG hmean hm hlim
  exact ⟨hG', hmean', hvar⟩

theorem l6a_hasGaussianLaw_sphereMean {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) :
    HasGaussianLaw (fun ω => l6a_convSphereMean κ ε (h ω)) P ∧
      ∫ ω, l6a_convSphereMean κ ε (h ω) ∂P = 0 :=
  ⟨(l6a_gaussianClosure_sphereMean hd κ hκ P h hh hε).1,
    (l6a_gaussianClosure_sphereMean hd κ hκ P h hh hε).2.1⟩

end HigherDimLQGMetric

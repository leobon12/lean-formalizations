import HigherDimLQGMetric.ConvField.MeanTest
import HigherDimLQGMetric.Sphere.Conv
import LQGMetric.Field.CircleAvgIndep

/-! Gaussian closure upgrades a.s. convergence of centered test pairings to L² convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l2b_centeredTrunc_L2_tendsto (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) (x : Rd d) :
    Tendsto (fun n : ℕ => ∫ ω,
      (h ω (l2b_centeredTruncTest hd hκ hε x n).1 -
        (convMollify κ ε (h ω) x -
          ∫ u : Rd d, convMollify κ ε (h ω) u ∂(unitSphereProb d))) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let φ : ℕ → TestRd0 d := fun n => l2b_centeredTruncTest hd hκ hε x n
  let X : ℕ → Ω → ℝ := fun n ω => h ω (φ n).1
  let Z : Ω → ℝ := fun ω => convMollify κ ε (h ω) x -
    ∫ u : Rd d, convMollify κ ε (h ω) u ∂(unitSphereProb d)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [l2b_ae_centeredTrunc_tendsto d hd κ hκ P h hh] with ω hω
    exact hω ε hε x
  have hXG (n : ℕ) : HasGaussianLaw (X n) P :=
    hh.1.gaussian.hasGaussianLaw_eval (φ n)
  have hXm (n : ℕ) : AEMeasurable (X n) P := (hXG n).aemeasurable
  have hZm : AEMeasurable Z P :=
    aemeasurable_of_tendsto_metrizable_ae' hXm hlim
  have hdiffG (n m : ℕ) : HasGaussianLaw (fun ω => X n ω - X m ω) P := by
    exact hh.1.hasGaussianLaw_sub (by rw [(φ n).2, (φ m).2])
  have hdiff0 (n m : ℕ) : ∫ ω, X n ω - X m ω ∂P = 0 := by
    exact hh.1.integral_sub_eq_zero (by rw [(φ n).2, (φ m).2])
  have hlimdiff (n : ℕ) : ∀ᵐ ω ∂P,
      Tendsto (fun m => X n ω - X m ω) atTop (𝓝 (X n ω - Z ω)) := by
    filter_upwards [hlim] with ω hω
    exact tendsto_const_nhds.sub hω
  have hdiffGZ (n : ℕ) : HasGaussianLaw (fun ω => X n ω - Z ω) P ∧
      (∫ ω, X n ω - Z ω ∂P) = 0 := by
    have hZm' : AEMeasurable (fun ω => X n ω - Z ω) P := (hXm n).sub hZm
    obtain ⟨hG, hmean, _⟩ := LQGMetric.CircleAvgIndep.gaussian_of_ae_tendsto
      (fun m => hdiffG n m) (fun m => hdiff0 n m) hZm' (hlimdiff n)
    exact ⟨hG, hmean⟩
  have hlimzero : ∀ᵐ ω ∂P,
      Tendsto (fun n => X n ω - Z ω) atTop (𝓝 0) := by
    filter_upwards [hlim] with ω hω
    simpa only [sub_self] using hω.sub (tendsto_const_nhds (x := Z ω))
  obtain ⟨_, _, hvar⟩ := LQGMetric.CircleAvgIndep.gaussian_of_ae_tendsto
    (Y := fun n ω => X n ω - Z ω) (Z := fun _ => (0 : ℝ))
    (fun n => (hdiffGZ n).1) (fun n => (hdiffGZ n).2)
    aemeasurable_const hlimzero
  have hsq (n : ℕ) : Var[(fun ω => X n ω - Z ω); P] =
      ∫ ω, (X n ω - Z ω) ^ 2 ∂P := by
    rw [variance_eq_integral ((hdiffGZ n).1.aemeasurable), (hdiffGZ n).2]
    simp only [sub_zero]
  have hzero : Var[(fun _ : Ω => (0 : ℝ)); P] = 0 := by
    exact variance_zero P
  simpa only [hsq, hzero, X, Z, φ] using hvar

end HigherDimLQGMetric

import HigherDimLQGMetric.ShellDec.Cylinder
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Stability of Gaussian Hölder under bounded almost-sure limits
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

theorem shellHolder_ae_limit {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℝ} (hK : 1 ≤ K)
    (G : ℕ → ι → Ω → ℝ) (F : ι → Ω → ℝ)
    (hGm : ∀ m i, Measurable (G m i))
    (hG0 : ∀ m i ω, 0 ≤ G m i ω)
    (hG1 : ∀ m i ω, G m i ω ≤ 1)
    (hlim : ∀ i, ∀ᵐ ω ∂P,
      Tendsto (fun m => G m i ω) atTop (𝓝 (F i ω)))
    (hfinite : ∀ m,
      ∫ ω, ∏ i, G m i ω ∂P ≤
        ∏ i, (∫ ω, G m i ω ^ K ∂P) ^ K⁻¹) :
    ∫ ω, ∏ i, F i ω ∂P ≤
      ∏ i, (∫ ω, F i ω ^ K ∂P) ^ K⁻¹ := by
  classical
  have hK0 : 0 ≤ K := by linarith
  have hKinv : 0 ≤ K⁻¹ := inv_nonneg.mpr hK0
  have hprod_lim : ∀ᵐ ω ∂P,
      Tendsto (fun m => ∏ i, G m i ω) atTop (𝓝 (∏ i, F i ω)) := by
    filter_upwards [ae_all_iff.2 hlim] with ω hω
    exact tendsto_finsetProd Finset.univ (fun i _ => hω i)
  have hprod_bound : ∀ m ω, ‖∏ i, G m i ω‖ ≤ (1 : ℝ) := by
    intro m ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Finset.prod_nonneg fun i _ => hG0 m i ω)]
    exact Finset.prod_le_one₀ (fun i _ => hG0 m i ω)
      (fun i _ => hG1 m i ω)
  have hprod_int : Tendsto
      (fun m => ∫ ω, ∏ i, G m i ω ∂P) atTop
      (𝓝 (∫ ω, ∏ i, F i ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun m => Finset.aestronglyMeasurable_fun_prod Finset.univ
        (fun i _ => (hGm m i).aestronglyMeasurable))
      (integrable_const 1) (fun m => ae_of_all _ (hprod_bound m)) hprod_lim
  have hrpow_int (i : ι) : Tendsto
      (fun m => ∫ ω, G m i ω ^ K ∂P) atTop
      (𝓝 (∫ ω, F i ω ^ K ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun m => ((hGm m i).pow_const K).aestronglyMeasurable)
      (integrable_const 1) (fun m => ae_of_all _ fun ω => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hG0 m i ω) K)]
      exact Real.rpow_le_one (hG0 m i ω) (hG1 m i ω) hK0
    · filter_upwards [hlim i] with ω hω
      exact (Real.continuous_rpow_const hK0).tendsto _ |>.comp hω
  have hrhs : Tendsto
      (fun m => ∏ i, (∫ ω, G m i ω ^ K ∂P) ^ K⁻¹) atTop
      (𝓝 (∏ i, (∫ ω, F i ω ^ K ∂P) ^ K⁻¹)) := by
    apply tendsto_finsetProd Finset.univ
    intro i hi
    exact (Real.continuous_rpow_const hKinv).tendsto _ |>.comp (hrpow_int i)
  exact le_of_tendsto_of_tendsto hprod_int hrhs (Eventually.of_forall hfinite)

end HigherDimLQGMetric

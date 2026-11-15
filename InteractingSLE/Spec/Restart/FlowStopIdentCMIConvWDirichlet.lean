/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWSource

/-! # Dirichlet pairings for a CMCut comparison shift -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal Laplacian
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper QuantumZipper.Thm11Asm LQGMetric LocalSets
open LocalExt
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)
namespace CMCut
variable (F : CMCut)

/-- Dominated source approximations can be tested against any bounded continuous function. -/
theorem tendsto_integral_mul_of_dominated {s : ℕ → TestOn upperHalfPlaneOpens}
    (hs : ∀ n z, |s n z| ≤ |F.src z|)
    (hlim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z)))
    {u : ℂ → ℝ} (hu : ContinuousOn u H) {C : ℝ} (hC : ∀ z ∈ H, |u z| ≤ C) :
    Tendsto (fun k => ∫ z, u z * s k z) atTop (𝓝 (∫ z, u z * F.src z)) := by
  refine tendsto_integral_of_dominated_convergence (fun z => C * |F.src z|)
    (fun k => (LocalExt.integrable_mul_testOn hu (s k)).aestronglyMeasurable)
    (F.integrable_src.abs.const_mul C) (fun k => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : z ∈ H
    · exact mul_le_mul (hC z hz) (hs k z) (abs_nonneg _) ((abs_nonneg _).trans (hC z hz))
    · have h1 := hs k z
      rw [F.src_of_notMem hz, abs_zero] at h1
      rw [abs_nonpos_iff.1 h1, F.src_of_notMem hz, abs_zero, mul_zero, mul_zero]
  · exact tendsto_const_nhds.mul (hlim z)

/-- Green's identity identifies the shift's Dirichlet pairings with the source. -/
theorem smoothDist_shift_lapTest {q : ℂ → ℝ} (hq : InnerProductSpace.HarmonicOnNhd q H)
    (U : Opens ℂ) (hU : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)) :
    smoothDist upperHalfPlaneOpens (fun z => q z - F.f z) (lapTest U g) =
      ∫ z, g.1 z * F.src z := by
  have hqc : ContinuousOn q H := hq.continuousOn
  have hfc : ContinuousOn F.f H := F.smooth.continuous.continuousOn
  have hlap : ⇑(lapTest U g) = fun z => -(2 * Real.pi)⁻¹ * Δ g.1 z := by
    rw [coe_lapTest hU]; rfl
  have hqI : Integrable (fun z => lapTest U g z * q z) :=
    (LocalExt.integrable_mul_testOn hqc (lapTest U g)).congr (ae_of_all _ fun z => mul_comm _ _)
  have hfI : Integrable (fun z => lapTest U g z * F.f z) :=
    (LocalExt.integrable_mul_testOn hfc (lapTest U g)).congr (ae_of_all _ fun z => mul_comm _ _)
  have hq0 : ∫ z, lapTest U g z * q z = 0 := by
    have h := LQGMetric.HarmLoc.integral_mul_cmTest_of_harmonic U.isOpen (hq.mono hU)
      (MarkovZB.zsTest g.2) g.2.2.2
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    rw [coe_lapTest hU]
    exact mul_comm _ _
  rw [smoothDist_apply (hqc.sub hfc)]
  have hsub : (∫ z, lapTest U g z * (q z - F.f z)) =
      (∫ z, lapTest U g z * q z) - ∫ z, lapTest U g z * F.f z := by
    rw [← integral_sub hqI hfI]
    exact integral_congr_ae (ae_of_all _ fun z => mul_sub _ _ _)
  rw [hsub, hq0, zero_sub]
  have hG := LQGMetric.CONF.ZBM.integral_mul_laplacian_comm
    (F.smooth.of_le (by simp)) (g.2.1.of_le (by simp)) g.2.2.1
  have he : (fun z => lapTest U g z * F.f z) =
      fun z => -(2 * Real.pi)⁻¹ * (F.f z * Δ g.1 z) := by
    funext z; rw [hlap]; ring
  rw [he, integral_const_mul, hG, ← integral_const_mul, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  dsimp only
  by_cases hz : z ∈ H
  · rw [F.src_of_mem hz]
    simp only [QuantumZipper.K3.greenDensity]
    ring
  · have hgz : g.1 z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hU (g.2.2.2 h))
    simp only [hgz, zero_mul, mul_zero, neg_zero]

/-- The exact source-limit premise of the general local-set Cameron–Martin theorem. -/
theorem tendsto_integral_mul_eq_shift_lapTest {s : ℕ → TestOn upperHalfPlaneOpens}
    (hs : ∀ n z, |s n z| ≤ |F.src z|)
    (hlim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z)))
    {q : ℂ → ℝ} (hq : InnerProductSpace.HarmonicOnNhd q H)
    (U : Opens ℂ) (hU : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)) :
    Tendsto (fun k => ∫ z, s k z * g.1 z) atTop
      (𝓝 (smoothDist upperHalfPlaneOpens (fun z => q z - F.f z) (lapTest U g))) := by
  obtain ⟨C, hC⟩ := g.2.1.continuous.bounded_above_of_compact_support g.2.2.1
  have h := F.tendsto_integral_mul_of_dominated hs hlim g.2.1.continuous.continuousOn
    (fun z _ => (Real.norm_eq_abs _).symm.le.trans (hC z))
  rw [F.smoothDist_shift_lapTest hq U hU g]
  exact h.congr fun k => integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)

end CMCut
end InteractingSLE.Restart.FlowStopIdentCMI

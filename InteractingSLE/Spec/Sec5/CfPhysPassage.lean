/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ImgChartConstDyadic

/-!
# Projection-member identities along strict upper dyadic lines

Packet PROVE-CFCHART2. The raw image filtration records announcing events, for
which the landed stopped-history transfer is strict in the capacity clock.
The projection identity itself has a constant Gaussian factor, so its passage
needs only eventual safety of strict upper dyadic physical lines. No inclusive
clock-cut measurability or limit of conditional means is required.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfPhys

open WangWu.ChartConst

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- A constant-factor integral identity passes from the disjoint strict upper
dyadic pieces to their limiting event. Pieces need only be null measurable. -/
theorem setIntegral_mul_eq_of_dyadic {a b : Ω → ℂ} (ha : Integrable a μ) (hb : Integrable b μ)
    {θ : Ω → ℝ≥0} {D : Set Ω} (hD : MeasurableSet D) {Av : ℝ≥0 → Set Ω} (c : ℂ)
    (hpiece : ∀ n k, NullMeasurableSet (D ∩ {ω | dyIdx n (θ ω) = k} ∩ Av (dyq n k)) μ)
    (hline : ∀ n k,
      ∫ ω in D ∩ {ω | dyIdx n (θ ω) = k} ∩ Av (dyq n k), a ω ∂μ =
        c * ∫ ω in D ∩ {ω | dyIdx n (θ ω) = k} ∩ Av (dyq n k), b ω ∂μ)
    (hsafe : ∀ᵐ ω ∂μ, ω ∈ D → ∀ᶠ n in atTop, ω ∈ Av (dyF n (θ ω))) :
    ∫ ω in D, a ω ∂μ = c * ∫ ω in D, b ω ∂μ := by
  let E : ℕ → ℕ → Set Ω := fun n k => D ∩ {ω | dyIdx n (θ ω) = k} ∩ Av (dyq n k)
  let U : ℕ → Set Ω := fun n => ⋃ k, E n k
  have hEm : ∀ n k, NullMeasurableSet (E n k) μ := hpiece
  have hUm : ∀ n, NullMeasurableSet (U n) μ := fun n => NullMeasurableSet.iUnion (hEm n)
  have hmem : ∀ n ω, ω ∈ U n ↔ ω ∈ D ∧ ω ∈ Av (dyF n (θ ω)) := by
    intro n ω
    simp only [U, E, mem_iUnion, mem_inter_iff, mem_ofPred_eq, dyF]
    constructor
    · rintro ⟨k, ⟨hωD, rfl⟩, hωA⟩
      exact ⟨hωD, hωA⟩
    · rintro ⟨hωD, hωA⟩
      exact ⟨_, ⟨hωD, rfl⟩, hωA⟩
  have hdis : ∀ n, Pairwise (Function.onFun (AEDisjoint μ) (E n)) := by
    intro n k l hkl
    exact Disjoint.aedisjoint (Set.disjoint_left.2 fun _ hk hl => hkl (hk.1.2.symm.trans hl.1.2))
  have heq : ∀ n, ∫ ω in U n, a ω ∂μ = c * ∫ ω in U n, b ω ∂μ := by
    intro n
    rw [integral_iUnion_ae (hEm n) (hdis n) ha.integrableOn,
      integral_iUnion_ae (hEm n) (hdis n) hb.integrableOn, ← tsum_mul_left]
    exact tsum_congr fun k => hline n k
  have hlim : ∀ g : Ω → ℂ, Integrable g μ →
      Tendsto (fun n => ∫ ω in U n, g ω ∂μ) atTop (𝓝 (∫ ω in D, g ω ∂μ)) := by
    intro g hg
    simp only [← integral_indicator₀ (hUm _), ← integral_indicator hD]
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖g ω‖)
      (fun n => hg.aestronglyMeasurable.indicator₀ (hUm n)) hg.norm ?_ ?_
    · intro n
      exact ae_of_all _ fun ω => norm_indicator_le_norm_self _ _
    · filter_upwards [hsafe] with ω hω
      by_cases hωD : ω ∈ D
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hω hωD] with n hn
        rw [indicator_of_mem hωD, indicator_of_mem ((hmem n ω).2 ⟨hωD, hn⟩)]
      · exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => by
          change D.indicator g ω = (U n).indicator g ω
          rw [indicator_of_notMem hωD,
            indicator_of_notMem (fun h => hωD ((hmem n ω).1 h).1)])
  exact tendsto_nhds_unique ((hlim a ha).congr heq) ((hlim b hb).const_mul c)

end InteractingSLE.Sec5.CfPhys

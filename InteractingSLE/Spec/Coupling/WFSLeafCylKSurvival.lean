/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafCylKDensity

/-!
# Concrete finite-cylinder approximations of the survival discount

Finite-window density is pulled back along a measurable full killed history.
The landed Galmarino identity reads the cutoff from this full history, so
its lifetime discount has these approximations without a new density input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF

/-- Pull finite-cylinder L¹ density back along a measurable history map.
The pushforward is used only with its established measurability. -/
theorem exists_historyWindow_comp_L1_approx
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {nL nR : ℕ} {Y : Ω → HistorySpace nL nR} (hY : Measurable Y)
    {F : HistorySpace nL nR → ℝ} (hFm : Measurable F) (hFi : Integrable F (P.map Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ g : HistoryWindow nL nR n →ᵇ ℝ,
      (∫ ω, ‖F (Y ω) - g (historyWindow n (Y ω))‖ ∂P) < ε := by
  obtain ⟨n, g, hg⟩ := exists_historyWindow_L1_approx hFi hε
  refine ⟨n, g, ?_⟩
  have he : Measurable (fun γ => ‖F γ - g (historyWindow n γ)‖) :=
    (hFm.sub (g.continuous.measurable.comp (measurable_historyWindow n))).norm
  have hi := integral_map (μ := P) hY.aemeasurable he.aestronglyMeasurable
  exact hi ▸ hg

/-- The actual Galmarino lifetime discount is L¹-approximable by bounded
continuous finite cylinders of the full continuation history. No conditional-
mean continuity or additional approximation hypothesis is assumed. -/
theorem exists_survival_historyWindow_L1_approx
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    (hVζ : ∀ ω, V ω ≤ ζ ω)
    (hself : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ g : HistoryWindow nL nR n →ᵇ ℝ,
      Integrable (fun ω => g (historyWindow n (killedHistory W VL VR ζ ω))) P ∧
      (∫ ω, ‖g (historyWindow n (killedHistory W VL VR ζ ω)) - survivalDiscount (V ω)‖ ∂P)
        < ε := by
  have hY := measurable_killedHistory
    (Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE)
  have hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω)
      {t | (t : ℝ≥0∞) < ζ ω} :=
    hE.isSLEEvolutionUpTo.ae_path.mono fun _ hp => continuousOn_state_of_isSLEPathUpTo hp
  have hR := ae_rule_full_eq_of_self hRg hc hVζ hself
  obtain ⟨n, g, hg⟩ := exists_historyWindow_comp_L1_approx (P := P) hY
    (measurable_survivalDiscount.comp hRm) (integrable_survivalDiscount hRm) hε
  refine ⟨n, g, integrable_historyWindow_comp hY g, ?_⟩
  calc
    _ = ∫ ω, ‖survivalDiscount (R (killedHistory W VL VR ζ ω)) -
        g (historyWindow n (killedHistory W VL VR ζ ω))‖ ∂P := by
      apply integral_congr_ae
      filter_upwards [hR] with ω hω
      rw [← hω, norm_sub_rev]
    _ < ε := hg

end InteractingSLE.WFS

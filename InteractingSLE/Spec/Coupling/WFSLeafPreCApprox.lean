/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPreCZero

/-!
# Regular approximation from strict history stopping rules

The original field and coordinates themselves realize each strict prefix.
Cofinality on the reference follows from the already proved driving-marginal
comparison. Thus no separate stopped models or reference approximations are inputs.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Strict cofinal own-history stopping rules supply every clause of the
previous regular-prefix approximation predicate. -/
theorem hasRegularRuleApprox_of_strictRules
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    (hV : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω))
    {Q : ℕ → HistorySpace nL nR → ℝ≥0∞}
    (hQ : ∀ n, Measurable (Q n) ∧ IsHistGalmarino (Q n))
    (hstop : ∀ n, IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
      fun ω => (Q n (killedHistory W VL VR V ω) : WithTop ℝ≥0))
    (hstrict : ∀ n, ∀ᵐ ω ∂P, Q n (killedHistory W VL VR V ω) < V ω)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Q n (killedHistory W VL VR V ω)) atTop (𝓝 (V ω)))
    {Ω₀ : Type u} [mΩ₀ : MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hC₀ : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀) :
    HasRegularRuleApprox κ xL xR ρL ρR P h (killedHistory W VL VR V) P₀
      (ruleKill R ∘ killedHistory W₀ VL₀ VR₀ ζ₀) := by
  have hY := measurable_killedHistory hC.2.2.2.2.choose
  have hY₀ := (measurable_ruleKill hRm).comp (measurable_killedHistory
    (Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₀.1))
  have hco : ∀ᵐ ω ∂P, (∀ n, Q n (killedHistory W VL VR V ω) ≤ V ω) ∧
      Tendsto (fun n => Q n (killedHistory W VL VR V ω)) atTop (𝓝 (V ω)) :=
    (ae_all_iff.2 hstrict).and hconv |>.mono fun _ hc => ⟨fun n => (hc.1 n).le, hc.2⟩
  have hlaw := map_killedHistory_eq_of_through hκ hF hRm hRg hC hV hC₀.1
  rw [← ruleKill_killedHistory] at hlaw
  refine ⟨Q, hQ, hco, ae_rule_cofinal_of_map_eq hY hY₀ hlaw (fun n => (hQ n).1) hco, ?_⟩
  intro n
  have hVs := Restart.Aux54.isStoppingTime_lifetime_driving (P := P) hC.2.2.2.2.choose
  have hS := (hstop n).min hVs
  have hlt : ∀ᵐ ω ∂P, min (Q n (killedHistory W VL VR V ω)) (V ω) < V ω :=
    (hstrict n).mono fun _ ht => (min_le_left _ _).trans_lt ht
  obtain ⟨hSC, hreg⟩ := isStoppedHullCoupling_of_through_strict hC hS
    (fun _ => min_le_right _ _) hlt
  refine ⟨usualAugmentation 𝓕 P, W, VL, VR, B,
    (fun ω => min (Q n (killedHistory W VL VR V ω)) (V ω)), hSC, hreg, ?_⟩
  exact Eventually.of_forall fun ω => congrFun (ruleKill_killedHistory (Q n) W VL VR V).symm ω

end InteractingSLE.WFS

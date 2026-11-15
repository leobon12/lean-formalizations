/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafAuxRJoint
import InteractingSLE.Spec.Coupling.WFSLeafAuxRLimit

/-!
# Joint-law comparison from regular stopped prefix models

The open input now concerns only cofinal own-history rules and regular
stopped realizations of their prefixes, keeping the given whole field.
Aux. 54 identifies each prefix law, and weak convergence identifies the
terminal joint law. No retained Gaussian kernel or mean graph is assumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LQGMetric LawUnique Restart.StoppedExtendWF Restart.StoppedExtend

/-- A geometric/stochastic approximation input for a pair of recorded laws.
The regular stopped models live on the original space with its original field.
This input asserts neither a field kernel nor any joint-law equality. -/
def HasRegularRuleApprox {nL nR : ℕ} (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω Ω₀ : Type u} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω₀]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (Y : Ω → HistorySpace nL nR) (P₀ : Measure Ω₀) (Y₀ : Ω₀ → HistorySpace nL nR) : Prop :=
  ∃ Q : ℕ → HistorySpace nL nR → ℝ≥0∞,
    (∀ n, Measurable (Q n) ∧ IsHistGalmarino (Q n)) ∧
    (∀ᵐ ω ∂P, (∀ n, Q n (Y ω) ≤ (Y ω).1) ∧
      Tendsto (fun n => Q n (Y ω)) atTop (𝓝 (Y ω).1)) ∧
    (∀ᵐ ω ∂P₀, (∀ n, Q n (Y₀ ω) ≤ (Y₀ ω).1) ∧
      Tendsto (fun n => Q n (Y₀ ω)) atTop (𝓝 (Y₀ ω).1)) ∧
    ∀ n, ∃ (𝓕s : Filtration ℝ≥0 mΩ) (Ws : ℝ≥0 → Ω → ℝ)
      (VLs : Fin nL → ℝ≥0 → Ω → ℝ) (VRs : Fin nR → ℝ≥0 → Ω → ℝ)
      (Bs : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0∞),
      IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕s Ws VLs VRs Bs S h ∧
      Restart.Aux54.IsRegularStop ρL ρR P Ws VLs VRs S ∧
      killedHistory Ws VLs VRs S =ᵐ[P] ruleKill (Q n) ∘ Y

/-- Cofinal regular stopped models give the exact through/full joint-law
comparison. Only the construction of those models remains an input. -/
theorem map_field_ruleHistory_eq_of_regularApprox
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hC₀ : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (hA : HasRegularRuleApprox κ xL xR ρL ρR P h (killedHistory W VL VR V) P₀
      (ruleKill R ∘ killedHistory W₀ VL₀ VR₀ ζ₀)) :
    P.map (fun ω => (h ω, killedHistory W VL VR V ω)) =
      P₀.map (fun ω => (h₀ ω, killedHistory W₀ VL₀ VR₀
        (fun ω => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω)) ω)) := by
  let Y := killedHistory W VL VR V
  let Y₀ := ruleKill R ∘ killedHistory W₀ VL₀ VR₀ ζ₀
  have hY : Measurable Y := measurable_killedHistory hC.2.2.2.2.choose
  have hX₀ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₀.1
  have hY₀ : Measurable Y₀ := (measurable_ruleKill hRm).comp (measurable_killedHistory hX₀)
  have hc : ∀ᵐ ω ∂P, IsKilledContHist (Y ω) := by
    filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact isKilledContHist_killedHistory ((continuousOn_state_of_isSLEPathUpTo hp).mono
      (fun t ht => ht.trans_le (hC.2.1 ω)))
  have hc₀ : ∀ᵐ ω ∂P₀, IsKilledContHist (Y₀ ω) := by
    filter_upwards [hC₀.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact isKilledContHist_killAt
      (isKilledContHist_killedHistory (continuousOn_state_of_isSLEPathUpTo hp)) (min_le_right _ _)
  have hn : ∀ᵐ ω ∂P, historyNormalize (Y ω) = Y ω :=
    Eventually.of_forall fun ω => historyNormalize_killedHistory W VL VR V ω
  have hn₀ : ∀ᵐ ω ∂P₀, historyNormalize (Y₀ ω) = Y₀ ω := by
    rw [show Y₀ = killedHistory W₀ VL₀ VR₀
      (fun ω => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω)) from ruleKill_killedHistory _ _ _ _ _]
    exact Eventually.of_forall fun ω => historyNormalize_killedHistory _ _ _ _ ω
  obtain ⟨Q, hQ, hg, hg₀, hmodels⟩ := hA
  have heq : P.map (fun ω => (h ω, Y ω)) = P₀.map (fun ω => (h₀ ω, Y₀ ω)) := by
    apply map_field_history_eq_of_rule_limits hC.2.2.1 hC₀.2.1 hY hY₀ hn hn₀
      (fun n => (hQ n).1) (hg.mono fun _ h => h.2) (hg₀.mono fun _ h => h.2)
    intro n
    obtain ⟨𝓕s, Ws, VLs, VRs, Bs, S, hSC, hreg, hmatch⟩ := hmodels n
    have hS : ∀ᵐ ω ∂P, S ω = Q n (killedHistory Ws VLs VRs S ω) := by
      filter_upwards [hmatch, hg, hc] with ω he hg hc
      calc
        S ω = min (Q n (Y ω)) (Y ω).1 := congrArg Prod.fst he
        _ = Q n (Y ω) := min_eq_left (hg.1 n)
        _ = Q n (killedHistory Ws VLs VRs S ω) := by
          rw [he]
          exact (rule_apply_ruleKill (hQ n).2 hc (hg.1 n)).symm
    have hlaw := map_field_ruleHistory_eq_of_regularStopped hκ hF hdet (hQ n).1 (hQ n).2
      hSC hS hreg hC₀
    rw [← ruleKill_killedHistory] at hlaw
    have he₀ : ∀ᵐ ω ∂P₀, ruleKill (Q n) (killedHistory W₀ VL₀ VR₀ ζ₀ ω) =
        ruleKill (Q n) (Y₀ ω) := by
      filter_upwards [hg₀, hc₀, hC₀.1.isSLEEvolutionUpTo.ae_path] with ω hg hc hp
      refine ruleKill_eq_ruleKill_of_prefix (hQ n).2 hc
        (isKilledContHist_killedHistory (continuousOn_state_of_isSLEPathUpTo hp))
        (hg.1 n) (min_le_right _ _) ?_
      intro p hpt
      change (dyadicTime p : ℝ≥0∞) <
        min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω) at hpt
      change (if (dyadicTime p : ℝ≥0∞) < min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω)
        then (killedHistory W₀ VL₀ VR₀ ζ₀ ω).2 p else 0) = _
      simp only [hpt, ↓reduceIte]
    calc
      P.map (fun ω => (h ω, ruleKill (Q n) (Y ω))) =
          P.map (fun ω => (h ω, killedHistory Ws VLs VRs S ω)) := by
        apply Measure.map_congr
        filter_upwards [hmatch] with ω he using Prod.ext rfl he.symm
      _ = _ := hlaw
      _ = P₀.map (fun ω => (h₀ ω, ruleKill (Q n) (Y₀ ω))) := by
        apply Measure.map_congr
        filter_upwards [he₀] with ω he using Prod.ext rfl he
  simpa only [Y, Y₀, ruleKill_killedHistory] using heq

end InteractingSLE.WFS

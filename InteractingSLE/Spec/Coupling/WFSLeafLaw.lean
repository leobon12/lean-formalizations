/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSTargets
import InteractingSLE.Spec.Exist.Param12Kernel

/-!
# The driving marginal and full-reference joint law at WFS rule stops

The driving marginal of a through coupling already follows from Theorem 2.2;
no whole-field identification is needed for it. Theorems 1.2–1.3 also give the
joint field–history law at any measurable rule of a full optional coupling.
The still missing comparison is between a through coupling and a full coupling.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

variable {nL nR : ℕ}

/-- Reading the capped rule from the full killed history gives the history killed
at that rule. No stopping-time assertion about the rule is needed. -/
theorem ruleKill_killedHistory (R : HistorySpace nL nR → ℝ≥0∞)
    {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    ruleKill R ∘ killedHistory W VL VR ζ =
      killedHistory W VL VR (fun ω => min (R (killedHistory W VL VR ζ ω)) (ζ ω)) := by
  funext ω
  exact killAt_killedHistory (W := W) (VL := VL) (VR := VR) (ζ := ζ)
    (V := fun ω => min (R (killedHistory W VL VR ζ ω)) (ζ ω)) (min_le_right _ _)

/-- Measurability of a full history killed at a measurable rule. -/
theorem measurable_ruleHistory {Ω : Type*} [MeasurableSpace Ω]
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    {R : HistorySpace nL nR → ℝ≥0∞} (hR : Measurable R) :
    Measurable (killedHistory W VL VR
      (fun ω => min (R (killedHistory W VL VR ζ ω)) (ζ ω))) := by
  rw [← ruleKill_killedHistory]
  exact (measurable_ruleKill hR).comp (measurable_killedHistory hX)

/-- The driving marginal of a through coupling at a Galmarino cutoff is the
capped-rule driving marginal of every full integrated evolution. -/
theorem map_killedHistory_eq_of_through
    {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    (hV : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω))
    {Ω₀ : Type v} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞}
    (hE₀ : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀) :
    P.map (killedHistory W VL VR V) =
      P₀.map (killedHistory W₀ VL₀ VR₀
        (fun ω => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω))) := by
  have hc : ∀ᵐ ω ∂P,
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
        {t | (t : ℝ≥0∞) < V ω} := by
    filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact (continuousOn_state_of_isSLEPathUpTo hp).mono
      (fun _ ht => ht.trans_le (hC.2.1 ω))
  exact map_killedHistory_eq_of_continuation hκ hF hRm hRg hC.2.2.2.2.choose hV hc
    measurable_id (by rw [Measure.map_id]) hC.1
    (ae_of_all _ fun ω => ⟨hC.2.1 ω, fun _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩⟩) hE₀

/-- Full optional couplings have the same joint law after applying a measurable
rule to their killed histories. This uses the approved Theorems 1.2–1.3 inputs. -/
theorem map_field_ruleHistory_eq
    {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR)
    {R : HistorySpace nL nR → ℝ≥0∞} (hR : Measurable R)
    {Ω₁ Ω₂ : Type u} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    {W₁ : ℝ≥0 → Ω₁ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ℝ}
    {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ}
    {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₁ : Ω₁ → ℝ≥0∞} {ζ₂ : Ω₂ → ℝ≥0∞}
    {h₁ : Ω₁ → DistOn upperHalfPlaneOpens} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    P₁.map (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁
      (fun ω => min (R (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) (ζ₁ ω)) ω)) =
    P₂.map (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂
      (fun ω => min (R (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) (ζ₂ ω)) ω)) := by
  have hlaw := Lemma75Bridge.map_field_dyadicHistory_eq hdet hC₁ hC₂
  have hT : Measurable (fun p : DistOn upperHalfPlaneOpens × HistorySpace nL nR =>
      (p.1, ruleKill R p.2)) := measurable_fst.prodMk ((measurable_ruleKill hR).comp measurable_snd)
  have hX₁ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₁.1
  have hX₂ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₂.1
  have heq := congrArg (fun μ => μ.map (fun p => (p.1, ruleKill R p.2))) hlaw
  rw [Measure.map_map hT (hC₁.2.1.prodMk (measurable_killedHistory hX₁)),
    Measure.map_map hT (hC₂.2.1.prodMk (measurable_killedHistory hX₂))] at heq
  change P₁.map (fun ω => (h₁ ω, (ruleKill R ∘ killedHistory W₁ VL₁ VR₁ ζ₁) ω)) =
    P₂.map (fun ω => (h₂ ω, (ruleKill R ∘ killedHistory W₂ VL₂ VR₂ ζ₂) ω)) at heq
  rwa [ruleKill_killedHistory, ruleKill_killedHistory] at heq

end InteractingSLE.WFS

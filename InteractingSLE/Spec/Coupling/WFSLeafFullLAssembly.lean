/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafFullLProcess

/-!
# WFS from continuous cylinder means in the full SLE evolution

The remaining regularity input concerns only a full integrated SLE evolution.
Finite-history density constructs its closed survival process. Galmarino's
test and the proved conditional-expectation comparison transfer that same
process to the cutoff filtration. The field coupling supplies no regularity
assumption in the new input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Remaining full-evolution regularity: continuous closed versions for
bounded continuous finite-history cylinders, in the full driving filtration.
This is an unproved mathematical input. No cutoff, rule, or field occurs. -/
def FullEvolutionCylinderRegularityStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ),
      ∀ n : ℕ, ∀ g : HistoryWindow nL nR n →ᵇ ℝ,
        ∃ M : ℝ≥0 → Ω → ℝ,
          StronglyAdapted (drivingFiltration P
            (Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE)) M ∧
          (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
          ∀ t, M t =ᵐ[P]
            P[fun ω => g (historyWindow n (killedHistory W VL VR ζ ω)) |
              drivingFiltration P
                (Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE) t]

/-- Full-evolution cylinder regularity supplies the continuous survival
process in the actual cutoff filtration. All cutoff transfer is proved. -/
theorem continuousClosedSurvivalProcessStatement_of_fullEvolutionCylinders
    {κ : ℝ} (hreg : FullEvolutionCylinderRegularityStatement.{u} κ) :
    ContinuousClosedSurvivalProcessStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  have hXζ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC.1
  have hXV := hC.2.2.2.2.choose
  have hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω)
      {t | (t : ℝ≥0∞) < ζ ω} :=
    hC.1.isSLEEvolutionUpTo.ae_path.mono fun _ hp => continuousOn_state_of_isSLEPathUpTo hp
  have hR := ae_rule_full_eq_of_self hRg hc hC.2.1 hself
  have hV := isStoppingTime_full_of_galmarino_self hXζ hXV hC.2.1 hc hRm hRg hself
  obtain ⟨X, hXa, hXc, hXe⟩ := exists_continuous_closed_of_history_cylinders
    (drivingFiltration P hXζ)
    (fun t => Ito.nullSets_le_usualAugmentation (killedDrivingFiltration hXζ) P t)
    (measurable_killedHistory hXζ) (measurable_survivalDiscount.comp hRm)
    (integrable_survivalDiscount hRm)
    (hreg xL xR ρL ρR hF P 𝓕 W VL VR B ζ hC.1)
  have he : (fun ω => survivalDiscount (R (killedHistory W VL VR ζ ω))) =ᵐ[P]
      fun ω => survivalDiscount (V ω) :=
    hR.mono fun ω hω => congrArg survivalDiscount hω
  have hclosed : ∀ t, X t =ᵐ[P]
      P[fun ω => survivalDiscount (V ω) | drivingFiltration P hXζ t] :=
    fun t => (hXe t).trans (condExp_congr_ae he)
  obtain ⟨hXaV, hXeV⟩ := stronglyAdapted_closed_cutoff_of_full hXζ hXV hC.2.1 hV
    measurable_survivalDiscount
    (integrable_survivalDiscount (measurable_of_isMeasurableKilledDriving hXV)) hXa hclosed
  exact ⟨X, hXaV, hXc, hXeV⟩

/-- The unchanged WFS target from the stated full-evolution regularity
input, using only the permitted Theorems 1.2 and 1.3 as other theorem inputs. -/
theorem throughKernelStatement_of_fullEvolutionCylinders
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hreg : FullEvolutionCylinderRegularityStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_continuousClosedProcess h12 h13 hκ
    (continuousClosedSurvivalProcessStatement_of_fullEvolutionCylinders hreg)

end InteractingSLE.WFS

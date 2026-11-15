/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafDenseIProcess

/-!
# WFS from dyadic conditional-mean regularity

The remaining input concerns only limits of the countable dyadic collection
of conditional means. It is equivalent to the former continuous-process
existence input. Neither regularity assertion is proved here; the continuous
version, adaptedness, and all nondyadic closing identities are constructed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Remaining regularity input: on one conull event, the dyadic conditional
means have a limit as the dyadic time approaches each nonnegative time. -/
def DyadicSurvivalLimitsStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h),
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
      (∀ᵐ ω ∂P, 0 < V ω) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ c : ℝ,
        Tendsto (fun d : dyadicTimes =>
          P[fun ω' => survivalDiscount (V ω') | drivingFiltration P hC.2.2.2.2.choose d] ω)
          (comap (fun d : dyadicTimes => (d : ℝ≥0)) (𝓝 t)) (𝓝 c)

/-- Construct the old continuous-process input from the dyadic regularity
input. No version-selection or fixed-time closing assertion is assumed. -/
theorem continuousClosedSurvivalProcessStatement_of_dyadicLimits
    {κ : ℝ} (hlim : DyadicSurvivalLimitsStatement.{u} κ) :
    ContinuousClosedSurvivalProcessStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  have hVm := measurable_of_isMeasurableKilledDriving hC.2.2.2.2.choose
  have hZ : MemLp (fun ω => survivalDiscount (V ω)) 2 P :=
    MemLp.of_bound (measurable_survivalDiscount.comp hVm).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (survivalDiscount_mem_Icc (V ω)).1]
        exact (survivalDiscount_mem_Icc (V ω)).2)
  have : (drivingFiltration P hC.2.2.2.2.choose).IsRightContinuous :=
    Ito.isRightContinuous_usualAugmentation _ _
  exact exists_continuous_closed_process_of_dyadic_limits _
    (fun t => Ito.nullSets_le_usualAugmentation _ P t) hZ
    (hlim xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B ζ V h hC hself hpos)

/-- The new dyadic regularity input follows from the old continuous version
input; hence it does not strengthen the remaining mathematical obligation. -/
theorem dyadicSurvivalLimitsStatement_of_continuousClosedProcess
    {κ : ℝ} (hc : ContinuousClosedSurvivalProcessStatement.{u} κ) :
    DyadicSurvivalLimitsStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  obtain ⟨X, _, hXc, hXe⟩ := hc xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B ζ V h hC hself hpos
  exact ae_dyadic_limits_of_continuous_closed hXc hXe

/-- Exact equivalence of the two remaining regularity formulations. -/
theorem continuousClosedSurvivalProcessStatement_iff_dyadicLimits {κ : ℝ} :
    ContinuousClosedSurvivalProcessStatement.{u} κ ↔ DyadicSurvivalLimitsStatement.{u} κ :=
  ⟨dyadicSurvivalLimitsStatement_of_continuousClosedProcess,
    continuousClosedSurvivalProcessStatement_of_dyadicLimits⟩

/-- The unchanged WFS target from the explicitly unproved dyadic mean-limit
input and the permitted Theorems 1.2 and 1.3. -/
theorem throughKernelStatement_of_dyadicSurvivalLimits
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hlim : DyadicSurvivalLimitsStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_continuousClosedProcess h12 h13 hκ
    (continuousClosedSurvivalProcessStatement_of_dyadicLimits hlim)

end InteractingSLE.WFS

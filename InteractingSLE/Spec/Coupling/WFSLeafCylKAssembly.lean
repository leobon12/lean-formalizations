/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafCylKSurvival

/-!
# WFS from regularity of concrete finite history cylinders

The finite-cylinder approximation of the lifetime discount is proved in the
preceding files. Continuity of the closed conditional means of these concrete
cylinders remains an explicit SLE-specific input. The landed L¹ closure theorem
then constructs the survival martingale and gives the unchanged WFS target.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Remaining model-specific regularity: bounded continuous observables of
finitely many full-history coordinates have continuous closed versions in the
actual cutoff-driving filtration. The full lifetime is a window coordinate.
This assertion is not proved here. -/
def FullHistoryCylinderRegularityStatement (κ : ℝ) : Prop :=
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
      ∀ n : ℕ, ∀ g : HistoryWindow nL nR n →ᵇ ℝ,
        ∃ M : ℝ≥0 → Ω → ℝ,
          StronglyAdapted (drivingFiltration P hC.2.2.2.2.choose) M ∧
          (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
          ∀ t, M t =ᵐ[P]
            P[fun ω => g (historyWindow n (killedHistory W VL VR ζ ω)) |
              drivingFiltration P hC.2.2.2.2.choose t]

/-- The concrete finite-cylinder density theorem supplies the former
approximation-existence input. Only cylinder regularity is assumed. -/
theorem survivalL1ApproximationStatement_of_fullHistoryCylinderRegularity
    {κ : ℝ} (hcyl : FullHistoryCylinderRegularityStatement.{u} κ) :
    SurvivalL1ApproximationStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos ε hε
  obtain ⟨n, g, hgi, hge⟩ := exists_survival_historyWindow_L1_approx
    hC.1 hRm hRg hC.2.1 hself hε
  refine ⟨fun ω => g (historyWindow n (killedHistory W VL VR ζ ω)), hgi, hge, ?_⟩
  exact hcyl xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B ζ V h hC hself hpos n g

/-- L¹ closure constructs the actual survival martingale from continuous
closed versions for the concrete finite history cylinders. -/
theorem continuousClosedSurvivalProcessStatement_of_fullHistoryCylinderRegularity
    {κ : ℝ} (hcyl : FullHistoryCylinderRegularityStatement.{u} κ) :
    ContinuousClosedSurvivalProcessStatement.{u} κ :=
  continuousClosedSurvivalProcessStatement_of_L1Approximation
    (survivalL1ApproximationStatement_of_fullHistoryCylinderRegularity hcyl)

/-- The unchanged WFS target from the stated cylinder regularity input and
the packet's permitted Theorems 1.2 and 1.3. -/
theorem throughKernelStatement_of_fullHistoryCylinderRegularity
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hcyl : FullHistoryCylinderRegularityStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_L1SurvivalApproximation h12 h13 hκ
    (survivalL1ApproximationStatement_of_fullHistoryCylinderRegularity hcyl)

end InteractingSLE.WFS

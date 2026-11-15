/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafCloseJProcess

/-!
# WFS from L¹ approximation by continuous closed martingales

The analytic closure argument is proved. The SLE-specific approximation
assertion remains an explicit input; no dense approximating family or
Brownian-filtration identification is asserted here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Arbitrarily accurate L¹ approximation by closing variables admitting
continuous closed versions suffices. Fast approximations are selected here. -/
theorem exists_continuous_closed_process_of_L1_approx
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (𝓓 : Filtration ℝ≥0 mΩ) (hn : ∀ t, nullSigma P ≤ 𝓓 t)
    {Z : Ω → ℝ} (hZ : Integrable Z P)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ Y : Ω → ℝ, Integrable Y P ∧
      (∫ ω, ‖Y ω - Z ω‖ ∂P) < ε ∧
      ∃ M : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 M ∧
        (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
        ∀ t, M t =ᵐ[P] P[Y | 𝓓 t]) :
    ∃ X : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 X ∧
      (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) ∧
      ∀ t, X t =ᵐ[P] P[Z | 𝓓 t] := by
  have hy (n : ℕ) := happrox ((1 / 4 : ℝ) ^ n) (by positivity)
  choose Y hYi hYe hYc using hy
  exact exists_continuous_closed_process_of_fast_L1_approx 𝓓 hn hZ hYi
    (fun n => (hYe n).le) hYc

/-- The remaining SLE-specific density input. For each through model, the
lifetime discount can be approximated in L¹ by integrable variables whose
closed martingales have continuous adapted versions. This is not proved. -/
def SurvivalL1ApproximationStatement (κ : ℝ) : Prop :=
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
      ∀ ε : ℝ, 0 < ε → ∃ Y : Ω → ℝ, Integrable Y P ∧
        (∫ ω, ‖Y ω - survivalDiscount (V ω)‖ ∂P) < ε ∧
        ∃ M : ℝ≥0 → Ω → ℝ,
          StronglyAdapted (drivingFiltration P hC.2.2.2.2.choose) M ∧
          (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
          ∀ t, M t =ᵐ[P] P[Y | drivingFiltration P hC.2.2.2.2.choose t]

/-- Apply the proved L¹ closure theorem to the actual lifetime discount.
Only the stated SLE-specific approximation assertion is left as an input. -/
theorem continuousClosedSurvivalProcessStatement_of_L1Approximation
    {κ : ℝ} (happrox : SurvivalL1ApproximationStatement.{u} κ) :
    ContinuousClosedSurvivalProcessStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  exact exists_continuous_closed_process_of_L1_approx _
    (fun t => Ito.nullSets_le_usualAugmentation _ P t)
    (integrable_survivalDiscount (measurable_of_isMeasurableKilledDriving hC.2.2.2.2.choose))
    (happrox xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B ζ V h hC hself hpos)

/-- The old regularity input implies the new approximation input by taking
the closing variable itself. Thus the new interface does not strengthen it. -/
theorem survivalL1ApproximationStatement_of_continuousClosedProcess
    {κ : ℝ} (hc : ContinuousClosedSurvivalProcessStatement.{u} κ) :
    SurvivalL1ApproximationStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos ε hε
  refine ⟨fun ω => survivalDiscount (V ω),
    integrable_survivalDiscount (measurable_of_isMeasurableKilledDriving hC.2.2.2.2.choose),
    ?_, hc xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B ζ V h hC hself hpos⟩
  simpa only [sub_self, norm_zero, integral_zero] using hε

/-- Audit the new input against the unchanged continuous-process input.
Neither equivalent assertion is discharged for the SLE model here. -/
theorem continuousClosedSurvivalProcessStatement_iff_L1Approximation {κ : ℝ} :
    ContinuousClosedSurvivalProcessStatement.{u} κ ↔ SurvivalL1ApproximationStatement.{u} κ :=
  ⟨survivalL1ApproximationStatement_of_continuousClosedProcess,
    continuousClosedSurvivalProcessStatement_of_L1Approximation⟩

/-- The unchanged WFS target, conditionally on the SLE approximation input
and the packet's permitted Theorem 1.2 and 1.3 inputs. -/
theorem throughKernelStatement_of_L1SurvivalApproximation
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (happrox : SurvivalL1ApproximationStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_continuousClosedProcess h12 h13 hκ
    (continuousClosedSurvivalProcessStatement_of_L1Approximation happrox)

end InteractingSLE.WFS

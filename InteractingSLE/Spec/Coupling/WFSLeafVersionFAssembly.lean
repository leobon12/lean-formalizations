/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafVersionFProcess

/-!
# WFS from a continuous closed process and raw-past compatibility

The optional history reader is constructed, including its single common
continuous version. The remaining inputs concern an ordinary adapted process
and a deterministic-time conditional-expectation comparison. Neither is
proved here; neither asks for a history reader or an announcing rule.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Remaining continuous-version existence in the actual driving filtration.
Only deterministic-time closing identities are requested. -/
def ContinuousClosedSurvivalProcessStatement (κ : ℝ) : Prop :=
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
      ∃ X : ℝ≥0 → Ω → ℝ,
        StronglyAdapted (drivingFiltration P hC.2.2.2.2.choose) X ∧
        (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) ∧
        ∀ t, X t =ᵐ[P] P[fun ω => survivalDiscount (V ω) | drivingFiltration P hC.2.2.2.2.choose t]

/-- Remaining raw-past compatibility. The lifetime mark and the usual
augmentation must not add conditional information about the discount beyond
these raw state samples, at each deterministic dyadic time. -/
def SurvivalPastCondExpStatement (κ : ℝ) : Prop :=
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
      ∀ p : ℕ × ℕ,
        P[fun ω => survivalDiscount (V ω) | drivingFiltration P hC.2.2.2.2.choose (dyadicTime p)] =ᵐ[P]
        P[fun ω => survivalDiscount (V ω) | samplePastSigma (killedHistory W VL VR V) (dyadicTime p)]

/-- The former optional-reader input follows from the two deterministic-time
stochastic inputs. All version selection and optional sampling is proved. -/
theorem continuousSurvivalReaderStatement_of_closedProcess_past
    {κ : ℝ} (hclosed : ContinuousClosedSurvivalProcessStatement.{u} κ)
    (hpast : SurvivalPastCondExpStatement.{u} κ) : ContinuousSurvivalReaderStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hm hgal Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  obtain ⟨X, hXa, hXc, hXe⟩ := hclosed xL xR ρL ρR hF R hm hgal P 𝓕 W VL VR B ζ V h hC hself hpos
  exact exists_optionalSurvivalReader_of_closed_process
    (measurable_killedHistory hC.2.2.2.2.choose) hXa
    (fun t => Ito.nullSets_le_usualAugmentation (killedDrivingFiltration hC.2.2.2.2.choose) P t)
    hXc hXe (hpast xL xR ρL ρR hF R hm hgal P 𝓕 W VL VR B ζ V h hC hself hpos)

/-- The unchanged WFS target from the remaining ordinary-process construction
and raw-past comparison, with the permitted Theorem 1.2/1.3 inputs. -/
theorem throughKernelStatement_of_closedSurvivalProcess
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hclosed : ContinuousClosedSurvivalProcessStatement.{u} κ)
    (hpast : SurvivalPastCondExpStatement.{u} κ) : ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_continuousSurvivalReader h12 h13 hκ
    (continuousSurvivalReaderStatement_of_closedProcess_past hclosed hpast)

end InteractingSLE.WFS

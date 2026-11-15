/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafAuxRApprox

/-!
# WFS from cofinal regular stopped prefix models

R79 proves Aux. 54 without a whole-field-kernel premise for regular stopped
couplings. The open input below is the construction of cofinal regular
stopped prefixes of a through coupling. Joint-law comparison and the original
WFS target then follow; no mean graph or Gaussian kernel is an extra input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LQGMetric LawUnique Restart.StoppedExtendWF

/-- Remaining stochastic construction: cofinal Galmarino rules and regular
stopped prefix models preserving the original field. Not proved here. -/
def RegularRuleApproxStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h →
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
    ∀ {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W₀ : ℝ≥0 → Ω₀ → ℝ)
      (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ)
      (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞) (h₀ : Ω₀ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ →
      HasRegularRuleApprox κ xL xR ρL ρR P h (killedHistory W VL VR V) P₀
        (ruleKill R ∘ killedHistory W₀ VL₀ VR₀ ζ₀)

/-- The exact WFS endpoint from the cofinal regular-prefix construction and
the permitted Theorem 1.2/1.3 inputs. The construction remains open. -/
theorem throughKernelStatement_of_regularApprox
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hA : RegularRuleApproxStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ := by
  apply throughKernelStatement_of_jointLaw h12 h13 hκ
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hV
    Ω₀ mΩ₀ P₀ hP₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀
  exact map_field_ruleHistory_eq_of_regularApprox hκ hF
    (Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ hF) hRm hC hC₀
    (hA xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B ζ V h hC hV
      P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀)

end InteractingSLE.WFS

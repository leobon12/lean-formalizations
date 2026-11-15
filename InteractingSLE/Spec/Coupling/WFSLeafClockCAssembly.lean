/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafClockCRules

/-!
# WFS from a continuous history blowup clock

The explicit level-hit construction supplies the strict cofinal Galmarino
rules, including their stopping-time property. What remains is the stochastic
existence of a Borel non-anticipating continuous scalar reader which becomes
unbounded before an arbitrary positive own-history cutoff.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF LQGMetric

/-- Remaining stochastic clock construction. It asks for a single scalar
history observable and no stopping rules, stopped models, or field-law equality.
This construction is not proved here. -/
def HistoryBlowupClockStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ R : HistorySpace nL nR → ℝ≥0∞, Measurable R → IsHistGalmarino R →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ V : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h →
      (∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) →
      (∀ᵐ ω ∂P, 0 < V ω) → HasHistoryBlowupClock P (killedHistory W VL VR V)

/-- A history blowup clock supplies the entire previous announcing-rule input. -/
theorem strictRuleAnnounceStatement_of_historyBlowupClock
    {κ : ℝ} (hclock : HistoryBlowupClockStatement.{u} κ) : StrictRuleAnnounceStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF R hm hgal Ω mΩ P hP 𝓕 W VL VR B ζ V h hC hself hpos
  exact exists_strictRules_of_historyBlowupClock hC
    (hclock xL xR ρL ρR hF R hm hgal P 𝓕 W VL VR B ζ V h hC hself hpos)

/-- The exact unchanged WFS target, conditional only on the remaining clock
construction and the permitted Theorem 1.2/1.3 inputs. -/
theorem throughKernelStatement_of_historyBlowupClock
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hclock : HistoryBlowupClockStatement.{u} κ) :
    ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_strictRuleAnnounce h12 h13 hκ
    (strictRuleAnnounceStatement_of_historyBlowupClock hclock)

end InteractingSLE.WFS

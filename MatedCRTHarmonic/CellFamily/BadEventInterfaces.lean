import MatedCRTHarmonic.CellFamily.BadEventCore
import MatedCRTHarmonic.CellFamily.Interfaces
import MatedCRTHarmonic.CellFamily.MeasurableCurve

/-!
# Bad-event forms of the scaled-grid estimate probability interfaces

The event bounds are stated as upper bounds on outer measure of failure events. These
interfaces avoid measurability assumptions on the graph-dependent walk-law events.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

/-- Outer-measure tail bound for failure of the Lemma 2.7 cell-diameter event. -/
def Lemma27CellDiamBad (F : RandomCellFamily) (q ρ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, ∀ k,
    F.P (DiameterGood F k q ρ)ᶜ ≤ ENNReal.ofReal (C * mesh k ^ α)

/-- Corrected [18] Lemma 3.8 stated as an outer-measure bound on failure of its environment event. -/
def Lemma38AnnulusHitBad (F : RandomCellFamily) (ρ : ℝ) : Prop :=
  ∃ α₈ : ℝ, 0 < α₈ ∧ ∃ β₈ : ℝ, 0 < β₈ ∧ ∃ A₈ C₈ : ℝ,
    ∀ k (z : ℂ) (r : ℝ), mesh k ^ β₈ ≤ r → r ≤ ρ → ball z r ⊆ ball (0 : ℂ) ρ →
      F.P (Lemma38EnvironmentGood F k z r β₈ A₈)ᶜ ≤
        ENNReal.ofReal (C₈ * mesh k ^ α₈)

/-- Outer-measure tail bound for failure of the finite polar-template itinerary event. -/
def ItineraryEstimateBad (F : RandomCellFamily) (ρ : ℝ) : Prop :=
  ∃ s₀ αᵢ βᵢ Cᵢ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 10 ∧ 0 < αᵢ ∧ 0 < βᵢ ∧
    ∀ k (z : ℂ) (r : ℝ), mesh k ^ βᵢ ≤ r → r ≤ ρ → ball z (2 * r) ⊆ ball (0 : ℂ) ρ →
      F.P (PolarItineraryGood F k z r s₀)ᶜ ≤
        ENNReal.ofReal (Cᵢ * mesh k ^ αᵢ)

/-- Legacy Lemma 2.7 good-event form implies the bad-event form when its diameter event is
measurable. The curve measurability producer `measurable_diameterGood_of_curveCells` supplies this
part of the legacy premise. -/
theorem lemma27CellDiamBad_of_good
    (F : RandomCellFamily) (q ρ : ℝ) (hgood : Lemma27CellDiam F q ρ)
    (hmeas : ∀ k, MeasurableSet (DiameterGood F k q ρ)) : Lemma27CellDiamBad F q ρ := by
  rcases hgood with ⟨α, hα, C, hprob⟩
  refine ⟨α, hα, C, fun k => ?_⟩
  exact measure_compl_le_of_lower F.P (hmeas k) (by simpa [DiameterGood] using hprob k)

/-- Curve-generated diameter events are measurable by CMEAS, so the old Lemma 2.7 good-event
statement converts to its bad-event form without requiring the unavailable walk-event measurability. -/
theorem lemma27CellDiamBad_of_good_curveCells
    (F : RandomCellFamily) (q ρ : ℝ) (hgood : Lemma27CellDiam F q ρ)
    (η : F.Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (hcell : ∀ k ω x, (F.H k ω).cell x = curveCell η (mesh k) ω x) :
    Lemma27CellDiamBad F q ρ := by
  apply lemma27CellDiamBad_of_good F q ρ hgood
  apply measurable_diameterGood_of_curveCells F η hη q ρ
  · intro k
    rw [show mesh k = ((2 : ℝ) ^ k)⁻¹ by simp [mesh, zpow_neg, zpow_natCast]]
    positivity
  · exact hcell

/-- Legacy corrected Lemma 3.8 good-event form implies its bad-event form under event
measurability. -/
theorem lemma38AnnulusHitBad_of_good
    (F : RandomCellFamily) (ρ : ℝ) (hgood : Lemma38AnnulusHit F ρ)
    (hmeas : ∀ k z r β₈ A₈, MeasurableSet (Lemma38EnvironmentGood F k z r β₈ A₈)) :
    Lemma38AnnulusHitBad F ρ := by
  rcases hgood with ⟨α₈, hα₈, β₈, hβ₈, A₈, C₈, hprob⟩
  refine ⟨α₈, hα₈, β₈, hβ₈, A₈, C₈, fun k z r hkr hr hball => ?_⟩
  exact measure_compl_le_of_lower F.P (hmeas k z r β₈ A₈)
    (by simpa [Lemma38EnvironmentGood] using hprob k z r hkr hr hball)

/-- Legacy good itinerary estimate implies its bad-event form under itinerary-event measurability. -/
theorem itineraryEstimateBad_of_good
    (F : RandomCellFamily) (ρ : ℝ) (hgood : ItineraryEstimate F ρ)
    (hmeas : ∀ s₀ k z r, MeasurableSet (PolarItineraryGood F k z r s₀)) :
    ItineraryEstimateBad F ρ := by
  rcases hgood with ⟨s₀, αᵢ, βᵢ, Cᵢ, hs₀, hs₀le, hαᵢ, hβᵢ, hprob⟩
  refine ⟨s₀, αᵢ, βᵢ, Cᵢ, hs₀, hs₀le, hαᵢ, hβᵢ, fun k z r hkr hr hball => ?_⟩
  exact measure_compl_le_of_lower F.P (hmeas s₀ k z r) (hprob k z r hkr hr hball)

end MatedCRTHarmonic.CellFamily

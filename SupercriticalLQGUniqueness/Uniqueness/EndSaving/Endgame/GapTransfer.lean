import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.AssemblyV2




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem closed_gap_of_auxiliary_and_counting_exclusion_double
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cPlus : ℝ≥0∞) (R : AdmissibleRadii)
    (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set DistC)
    (b ε δ : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (ω : Ω)
    (hεpow : (ε : ℝ) ^ (2 * (ξ : ℝ) * (Q + 3)) = 2 * (δ : ℝ))
    (hAux : ω ∈ AuxiliaryGoodV2 h ξ Q R event b ε)
    (hnot : ω ∉ CountingBadEventV2 h D D' ξ Q cPlus R event b ε K₁ K₂) :
    ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
      OptimalConstants.Ratios.setDist (D' (h ω)) K₁ K₂ +
        ENNReal.ofReal ((δ : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr)) <
        cPlus * OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ := by
  have hAux' := hAux
  obtain ⟨hbr, hCircle, _, _⟩ := hAux
  refine ⟨hbr, hCircle, ?_⟩
  apply closed_gap_of_auxiliary_and_counting_exclusion_v2 h D D' ξ Q
    cPlus R event b ε K₁ K₂ ω hAux' hnot
  intro hbr' hCircle'
  have hEq : hbr' = hbr := tendsto_nhds_unique hCircle' hCircle
  subst hbr'
  have heq : (δ : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr) =
      (1 / 2 : ℝ) * (ε : ℝ) ^ (2 * (ξ : ℝ) * (Q + 3)) *
        (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr) := by
    rw [hεpow]
    ring
  exact le_of_eq (congrArg ENNReal.ofReal heq)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

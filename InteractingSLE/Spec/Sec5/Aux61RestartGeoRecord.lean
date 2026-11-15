import InteractingSLE.Spec.Sec5.Aux61RestartFin

/-!
# The canonical compact record of an original-target restart domain

Packet PROVE-AUX61-R1. A bounded half-plane hull is its own filling. Its
Euclidean closure is a compact record with the same filling, including the
correct real boundary points. No traced-range representation is needed.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

open Restart

/-- The canonical raw compact record, formed after retargeting the domain. -/
def originalTargetRecord (D : Set ℂ) : Set ℂ := closure (stripTargetHull D)

/-- Taking the Euclidean closure adds no new filled hull. -/
theorem fillH_closure_of_isHPHull {A : Set ℂ} (hA : IsHPHull A) :
    fillH (closure A) = A := by
  have heq : fillH (closure A) = fillH A := by
    simp only [fillH, closure_closure]
  exact heq.trans hA.fillH_eq

/-- The closure record has the connectivity required by the canonical log API. -/
theorem isPreconnected_closure_union_lowerHalf {A : Set ℂ} (hA : IsHPHull A) :
    IsPreconnected (closure A ∪ lowerHalf) := by
  have hclosed : IsClosed lowerHalf := isClosed_le continuous_im continuous_const
  have hp : IsPreconnected (A ∪ lowerHalf) := hA.isPreconnected_union_lowerHalf
  simpa only [closure_union, hclosed.closure_eq] using
    hp.closure

/-- All deterministic compact-record properties follow from the original-target
collar and the topology of the selected domain. -/
theorem originalTargetRecord_properties {D : Set ℂ} (hDo : IsOpen D)
    (hDs : IsSimplyConnected D) (hDH : D ⊆ H)
    (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D) :
    IsCompact (originalTargetRecord D) ∧
      IsPreconnected (originalTargetRecord D ∪ lowerHalf) ∧
      fillH (originalTargetRecord D) = stripTargetHull D := by
  have hB := isHPHull_stripTargetHull hDo hDs hDH htarget
  exact ⟨hB.2.1.isCompact_closure,
    isPreconnected_closure_union_lowerHalf hB, fillH_closure_of_isHPHull hB⟩

/-- The previous exact record-identity input is now an actual construction. -/
theorem isOriginalTargetHullRecord_originalTargetRecord
    {Ω : Type*} {D : Ω → Set ℂ} (hDo : ∀ ω, IsOpen (D ω))
    (hDs : ∀ ω, IsSimplyConnected (D ω)) (hDH : ∀ ω, D ω ⊆ H)
    (htarget : ∀ ω, ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D ω) :
    IsOriginalTargetHullRecord (fun ω => originalTargetRecord (D ω)) D :=
  fun ω => (originalTargetRecord_properties (hDo ω) (hDs ω) (hDH ω) (htarget ω)).2.2

end InteractingSLE.Sec5.Aux61Restart

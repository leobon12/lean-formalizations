/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalAnnounce

/-!
# The real-contact history rule, including infinite lifetimes

The finite-contact identification is already available. Before a first positive
real contact, the countable closed-piece hitting rule is at least the lifetime;
this also identifies it when the lifetime is infinite.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchLift

open Restart.RetAux79 Restart.FlowStopIdentG LawUnique

variable {nL nR : ℕ} {Ω : Type*}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
  {γ : ℝ≥0 → ℂ}

/-- An interior trace before its lifetime has no detected positive real
contact earlier than that lifetime. -/
theorem life_le_retPositiveRealRule
    (hc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      {t | (t : ℝ≥0∞) < V ω})
    (h0 : W 0 ω = 0) (hg : IsGeneratingTrace (fun t => W t ω) (V ω) γ)
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → γ t ∈ QuantumZipper.H) :
    V ω ≤ retPositiveRealRule (killedHistory W VL VR V ω) := by
  have hg' : IsGeneratingTrace (fun t => W t ω) (V ω)
      (fun t => γ t - (0 : ℝ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using hg
  apply le_hitRuleSeq_of_off isClosed_retPositiveRealPiece
    (g := fun t => (t, γ t))
    (continuous_id.continuousOn.prodMk
      (hg.2.1.mono fun t (ht : (t : ℝ≥0∞) < V ω) => ht.le))
  · intro m t ht hmem
    have ht0 : 0 < t := lt_of_lt_of_le
      (by positivity : (0 : ℝ≥0) < 1 / (m + 1)) hmem.1
    exact (ne_of_gt (hH t ht0 ht)) hmem.2
  · intro p hp _
    exact Prod.ext rfl (histTrace_killedHistory hc h0 hg' hp)

/-- The uncapped positive real-contact rule identifies a positive lifetime
when all earlier positive trace points are interior and every finite terminal
point is real. Infinite lifetimes are included. -/
theorem retPositiveRealRule_eq_life
    (hV : 0 < V ω)
    (hc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      {t | (t : ℝ≥0∞) < V ω})
    (h0 : W 0 ω = 0) (hg : IsGeneratingTrace (fun t => W t ω) (V ω) γ)
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → γ t ∈ QuantumZipper.H)
    (hend : ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → (γ T).im = 0) :
    retPositiveRealRule (killedHistory W VL VR V ω) = V ω := by
  by_cases htop : V ω = ⊤
  · apply le_antisymm
    · rw [htop]
      exact le_top
    · exact life_le_retPositiveRealRule hc h0 hg hH
  · have he : V ω = ((V ω).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal htop).symm
    have hT : 0 < (V ω).toNNReal := by
      rw [he] at hV
      exact ENNReal.coe_pos.1 hV
    exact retPositiveRealRule_killedHistory hT he hc h0 hg hH
      (hend (V ω).toNNReal he.symm)

end InteractingSLE.Wire.RetMatchLift

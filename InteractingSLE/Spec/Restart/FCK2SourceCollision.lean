/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2SourceInitial
import InteractingSLE.Spec.Restart.RetPlumbProofDriverModelInputs

/-!
# Collision criteria for the first-contact lifetime equality

The source collision argument has two geometric parts: no bad force group
before death, and a bad force group at each finite terminal state. The existing
attained-threshold theorem supplies one inequality; membership of the terminal
state in the threshold set supplies the other. Neither geometric part is
asserted to follow merely from the canonical capacity clock.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCPlumb
open Sec7.PocketTraversal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
  {U : Ω → ℝ≥0∞} {M : Set Ω}

omit mΩ in
/-- Reaching a bad force group gives the upper bound on the first threshold.
This is the existing threshold-set characterization specialized to geometric
force coordinates. -/
theorem thr_le_of_force_threshold (hc : ∀ ω, Continuous (W · ω)) {ω : Ω} {T : ℝ≥0}
    (ht : ForceWord.ThresholdCondition ρL ρR (W T ω)
      (fun i => geomLW W xL i T ω) (fun j => geomRW W xR j T ω)) :
    FCDet.thr ρL ρR W xL xR ω ≤ T := by
  apply (MartChar.thresholdTime_le_iff (hc ω)
    (fun i => (isForcePath_geomLW hc xL ω i).1)
    (fun j => (isForcePath_geomRW hc xR ω j).1)
    (fun i j s t hst he => geomLW_merge hc xL ω i j s t hst he)
    (fun i j s t hst he => geomRW_merge hc xR ω i j s t hst he) T).2
  exact ⟨T, le_rfl, ht⟩

/-- The exact two collision checks imply the canonical-lifetime/threshold
equality. The infinite-lifetime case needs no terminal input. -/
theorem ae_life_eq_thr_of_preterminal (hc : ∀ ω, Continuous (W · ω))
    (hpre : RetAux79.RetPrelifeNonThreshold (P := P) ρL ρR W xL xR U M)
    (hterminal : ∀ᵐ ω ∂P, ω ∈ M → ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω →
      ForceWord.ThresholdCondition ρL ρR (W T ω)
        (fun i => geomLW W xL i T ω) (fun j => geomRW W xR j T ω)) :
    ∀ᵐ ω ∂P, ω ∈ M → U ω = FCDet.thr ρL ρR W xL xR ω := by
  filter_upwards [RetAux79.life_le_thr_of_retPrelifeNonThreshold hc hpre, hterminal]
    with ω hle ht hω
  apply le_antisymm (hle hω)
  by_cases hU : U ω = ⊤
  · rw [hU]
    exact le_top
  · have he : ((U ω).toNNReal : ℝ≥0∞) = U ω := ENNReal.coe_toNNReal hU
    exact he ▸ thr_le_of_force_threshold hc (ht hω _ he)

end InteractingSLE.Restart.FCPlumb

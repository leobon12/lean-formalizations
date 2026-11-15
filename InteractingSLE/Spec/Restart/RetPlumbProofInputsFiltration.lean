/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsCond

/-!
# Null augmentation and announcing sequences under conditioning

Packet PROVE-RETPLUMB. Absolute continuity enlarges the available null sets.
Consequently stopping and announcing sequences in the original augmented
filtration remain valid under conditioning on a nonnull initial type event.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P Q : Measure Ω}

/-- Absolute continuity preserves every measurable null-set generator. -/
theorem nullSets_le_of_absolutelyContinuous (hQP : Q ≪ P) : Ito.nullSets P ≤ Ito.nullSets Q :=
  MeasurableSpace.generateFrom_mono (fun _ hs => ⟨hs.1, hQP hs.2⟩)

/-- The usual augmentation can only increase when passing to an absolutely
continuous measure on the same measurable sample space. -/
theorem usualAugmentation_le_of_absolutelyContinuous (𝓕 : Filtration ℝ≥0 mΩ)
    (hQP : Q ≪ P) : usualAugmentation 𝓕 P ≤ usualAugmentation 𝓕 Q := by
  intro t
  rw [Ito.usualAugmentation_apply, Ito.usualAugmentation_apply]
  exact iInf₂_mono fun _ _ => sup_le_sup_left (nullSets_le_of_absolutelyContinuous hQP) _

/-- The same monotonicity applies to the completed killed-driving filtration. -/
theorem drivingFiltration_le_of_absolutelyContinuous {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR V) (hQP : Q ≪ P) :
    drivingFiltration P hX ≤ drivingFiltration Q hX :=
  usualAugmentation_le_of_absolutelyContinuous (killedDrivingFiltration hX) hQP

/-- Announcing sequences survive both filtration enlargement and an absolutely
continuous change of probability measure. -/
theorem isAnnouncingSeq_of_absolutelyContinuous {𝓕 𝓖 : Filtration ℝ≥0 mΩ}
    {V : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0}
    (h : Coupling.IsAnnouncingSeq 𝓕 P V T) (hle : 𝓕 ≤ 𝓖) (hQP : Q ≪ P) :
    Coupling.IsAnnouncingSeq 𝓖 Q V T :=
  ⟨fun n t => hle t _ (h.1 n t), h.2.1,
    fun n => (h.2.2.1 n).filter_mono hQP.ae_le, h.2.2.2.filter_mono hQP.ae_le⟩

/-- In particular the original announcing times remain announcing times after
conditioning, with the new measure's usual augmentation. -/
theorem isAnnouncingSeq_usualAugmentation_cond {𝓕 : Filtration ℝ≥0 mΩ}
    {V : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} (M : Set Ω)
    (h : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P V T) :
    Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P[|M]) P[|M] V T :=
  isAnnouncingSeq_of_absolutelyContinuous h
    (usualAugmentation_le_of_absolutelyContinuous 𝓕 ProbabilityTheory.cond_absolutelyContinuous)
    ProbabilityTheory.cond_absolutelyContinuous

end InteractingSLE.Restart.RetAux79

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR3Inverse
import InteractingSLE.Spec.Supplement.GB6ReadDMeas
import InteractingSLE.Spec.Supplement.GB6LineL1
import InteractingSLE.Spec.Coupling.SafeFamily

/-!
# Borel inverse hulls and physical capacity in the GW2 chart

Read the physical hull by applying the recorded inverse chart to the relative
hull. This is hitting-measurable on the whole record space. Consequently its
grid capacity is a Borel physical-capacity functional, without a trace-selector
or boundary-landing hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR3

open Supp8.GB6 Exist.StagedLaw Coupling

/-- Applying the recorded inverse chart to a random hitting-measurable subset
of `H` preserves hitting measurability. Only interior chart values are used. -/
theorem measurable_image_relInv {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (s : ℝ≥0) {r : Ω → RecData} (hr : Measurable r)
    {K : Ω → Set ℂ} (hK : Measurable[mΩ, hittingSigma] K)
    (hKH : ∀ ω, K ω ⊆ H) :
    Measurable[mΩ, hittingSigma] (fun ω => relInv (rdrv (r ω)) s '' K ω) := by
  choose D hDsub hDcnt hDdense using fun F : Finset (ℚ × ℚ × ℚ) =>
    (TopologicalSpace.IsSeparable.of_separableSpace (ballsU F)).exists_countable_dense_subset
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, _, rfl⟩
  have heq : (fun ω => relInv (rdrv (r ω)) s '' K ω) ⁻¹'
      {A : Set ℂ | (A ∩ U).Nonempty} =
      ⋃ F ∈ {F : Finset (ℚ × ℚ × ℚ) | ballsK F ⊆ H},
      ⋃ G ∈ {G : Finset (ℚ × ℚ × ℚ) | ballsK G ⊆ U},
      {ω | (K ω ∩ ballsU F).Nonempty} ∩
        ⋂ z ∈ D F, {ω | relInv (rdrv (r ω)) s z ∈ ballsK G} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, exists_prop, mem_inter_iff,
      mem_iInter]
    constructor
    · rintro ⟨_, ⟨z, hzK, rfl⟩, hzU⟩
      obtain ⟨G, hGz, hGU⟩ := exists_rationalBalls isCompact_singleton hU
        (singleton_subset_iff.mpr hzU)
      let O := H ∩ (relInv (rdrv (r ω)) s) ⁻¹' ballsU G
      have hO : IsOpen O := (continuousOn_relInv (continuous_rdrv _) (rdrv_zero _)
        s.coe_nonneg).isOpen_inter_preimage QuantumZipper.isOpen_H (isOpen_ballsU G)
      obtain ⟨F, hFz, hFO⟩ := exists_rationalBalls isCompact_singleton hO
        (singleton_subset_iff.mpr ⟨hKH ω hzK, hGz rfl⟩)
      refine ⟨F, (fun z hz => (hFO hz).1), G, hGU, ⟨z, hzK, hFz rfl⟩, ?_⟩
      intro z hz
      exact ballsU_subset_ballsK G (hFO (ballsU_subset_ballsK F (hDsub F hz))).2
    · rintro ⟨F, hFH, G, hGU, ⟨z, hzK, hzF⟩, hD⟩
      have hzc : relInv (rdrv (r ω)) s z ∈ closure
          (relInv (rdrv (r ω)) s '' D F) :=
        ((continuousOn_relInv (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg).continuousAt
          (QuantumZipper.isOpen_H.mem_nhds (hKH ω hzK))).continuousWithinAt.mem_closure_image
            (hDdense F hzF)
      have hsub : relInv (rdrv (r ω)) s '' D F ⊆ ballsK G := by
        rintro _ ⟨x, hx, rfl⟩
        exact hD x hx
      exact ⟨_, ⟨z, hzK, rfl⟩,
        hGU (closure_minimal hsub (isCompact_ballsK G).isClosed hzc)⟩
  rw [heq]
  refine MeasurableSet.biUnion (Set.to_countable _) fun F hF =>
    MeasurableSet.biUnion (Set.to_countable _) fun G _ => ?_
  refine (hK (LocalSets.measurableSet_hitting (isOpen_ballsU F)
    ((ballsU_subset_ballsK F).trans hF))).inter ?_
  exact MeasurableSet.biInter (hDcnt F) fun z hz =>
    ((ReadD.measurable_relInv_record s (hF (ballsU_subset_ballsK F (hDsub F hz)))).comp hr)
      (isCompact_ballsK G).isClosed.measurableSet

/-- The physical hull read from the counterflow record and relative record. -/
def inverseHull (s q : ℝ≥0) (p : RecData × RecData) : Set ℂ :=
  relInv (rdrv p.1) s '' fwdHull (rdrv p.2) q

theorem measurable_inverseHull (s q : ℝ≥0) :
    Measurable[_, hittingSigma] (inverseHull s q) := by
  apply measurable_image_relInv s measurable_fst
  · exact (Supp8.GB6LineL.measurable_fwdHull_rdrv q).comp measurable_snd
  · intro p
    exact (isHPHull_fwdHull (continuous_rdrv p.2) q.coe_nonneg).1

/-- Half the grid capacity of the pulled-back relative hull. -/
def physicalCapacity (s q : ℝ≥0) (p : RecData × RecData) : ℝ :=
  (WholeField.hcapHit (inverseHull s q p)).toReal / 2

theorem measurable_physicalCapacity (s q : ℝ≥0) : Measurable (physicalCapacity s q) :=
  ((WholeField.measurable_hcapHit.comp (measurable_inverseHull s q)).ennreal_toReal).div_const 2

end InteractingSLE.Theorem14.GW2JDetR3

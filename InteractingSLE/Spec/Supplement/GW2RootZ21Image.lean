/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootY20Chart
import InteractingSLE.Spec.Supplement.GB6LineL4
import InteractingSLE.Spec.Coupling.SafeFamily

/-!
# Hitting measurability of forward images in the retained joint chart

Packet PROVE-T14-GW2ROOT2. Compact domain certificates adapt the landed
inverse-image argument to the forward chart's random open domain.
The random set needs only its hitting observations, with no chosen trace.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootZ21

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.CoordB Coupling

/-- A compact set inside `H` lies in the recorded joint domain on a
Borel event: its inverted compact set avoids the recorded Loewner hull. -/
theorem measurableSet_compact_subset_record_domain (s : ℝ≥0) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) :
    MeasurableSet {r : RecData | K ⊆ relDomain (rdrv r) s} := by
  have hc : ContinuousOn (fun z : ℂ => -z⁻¹) K :=
    (continuousOn_id.inv₀ fun z hz => ne_zero_of_mem_H (hKH hz)).neg
  have hm := Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand
    (B := fun t (r : RecData) => rdrv r t)
    (fun r => (continuous_rdrv r).comp NNReal.continuous_coe)
    (fun t => measurable_rdrv_apply t) (measurable_const (a := (s : ℝ)))
    (fun _ => s.coe_nonneg) (hK.image_of_continuousOn hc).isClosed
  rw [Supp8.GB6LineL.drive_rdrv] at hm
  have he : {r : RecData | K ⊆ relDomain (rdrv r) s} =
      {r : RecData | Disjoint ((fun z : ℂ => -z⁻¹) '' K)
        (QuantumZipper.fwdHull (rdrv r) s)} := by
    ext r
    constructor
    · intro h
      refine disjoint_left.mpr ?_
      rintro _ ⟨z, hz, rfl⟩ hbad
      exact ((mem_relDomain_iff _ _ _).mp (h hz)).2 hbad
    · intro h z hz
      exact (mem_relDomain_iff _ _ _).mpr ⟨hKH hz,
        fun hbad => disjoint_left.mp h ⟨z, hz, rfl⟩ hbad⟩
  rwa [he]

/-- The recorded forward chart preserves hitting measurability after
restriction to its actual open domain. This holds at every sample. -/
theorem measurable_image_relMap {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (s : ℝ≥0) {r : Ω → RecData} (hr : Measurable r)
    {K : Ω → Set ℂ} (hK : Measurable[mΩ, hittingSigma] K) :
    Measurable[mΩ, hittingSigma] fun ω =>
      relMap (rdrv (r ω)) s '' (K ω ∩ relDomain (rdrv (r ω)) s) := by
  classical
  choose D hDsub hDcnt hDdense using fun F : Finset (ℚ × ℚ × ℚ) =>
    (TopologicalSpace.IsSeparable.of_separableSpace (ballsU F)).exists_countable_dense_subset
  let f : ℂ → Ω → ℂ := fun z => {ω | z ∈ relDomain (rdrv (r ω)) s}.indicator
    fun ω => relMap (rdrv (r ω)) s z
  have hfm : ∀ z, Measurable (f z) := fun z =>
    RootY20.measurable_indicator_record_chart s hr measurable_const
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, _, rfl⟩
  have he : (fun ω => relMap (rdrv (r ω)) s '' (K ω ∩ relDomain (rdrv (r ω)) s)) ⁻¹'
      {A : Set ℂ | (A ∩ U).Nonempty} =
      ⋃ F ∈ {F : Finset (ℚ × ℚ × ℚ) | ballsK F ⊆ H},
      ⋃ G ∈ {G : Finset (ℚ × ℚ × ℚ) | ballsK G ⊆ U},
        ({ω | ballsK F ⊆ relDomain (rdrv (r ω)) s} ∩
          {ω | (K ω ∩ ballsU F).Nonempty}) ∩
        ⋂ z ∈ D F, (f z) ⁻¹' ballsK G := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, exists_prop, mem_inter_iff,
      mem_iInter]
    constructor
    · rintro ⟨_, ⟨z, ⟨hzK, hzD⟩, rfl⟩, hzU⟩
      obtain ⟨G, hGz, hGU⟩ := exists_rationalBalls isCompact_singleton hU
        (singleton_subset_iff.mpr hzU)
      let O := relDomain (rdrv (r ω)) s ∩ (relMap (rdrv (r ω)) s) ⁻¹' ballsU G
      have hcont : ContinuousOn (relMap (rdrv (r ω)) s) (relDomain (rdrv (r ω)) s) :=
        fun z hz => (continuousAt_relMap (continuous_rdrv _) s.coe_nonneg
          ((mem_relDomain_iff _ _ _).mp hz).1
          ((mem_relDomain_iff _ _ _).mp hz).2).continuousWithinAt
      have hO : IsOpen O := hcont.isOpen_inter_preimage
        (isOpen_relDomain (continuous_rdrv _) s.coe_nonneg) (isOpen_ballsU G)
      obtain ⟨F, hFz, hFO⟩ := exists_rationalBalls isCompact_singleton hO
        (singleton_subset_iff.mpr ⟨hzD, hGz rfl⟩)
      have hFD : ballsK F ⊆ relDomain (rdrv (r ω)) s := fun z hz => (hFO hz).1
      refine ⟨F, (fun z hz => (hFD hz).1), G, hGU, ⟨hFD, z, hzK, hFz rfl⟩, ?_⟩
      intro y hy
      have hyF := ballsU_subset_ballsK F (hDsub F hy)
      rw [show f y ω = relMap (rdrv (r ω)) s y from
        indicator_of_mem (show ω ∈ {ω | y ∈ relDomain (rdrv (r ω)) s} from hFD hyF) _]
      exact ballsU_subset_ballsK G (hFO hyF).2
    · rintro ⟨F, _, G, hGU, ⟨hFD, z, hzK, hzF⟩, hD⟩
      have hzD := hFD (ballsU_subset_ballsK F hzF)
      have hzc : relMap (rdrv (r ω)) s z ∈ closure
          (relMap (rdrv (r ω)) s '' D F) :=
        (continuousAt_relMap (continuous_rdrv _) s.coe_nonneg
          ((mem_relDomain_iff _ _ _).mp hzD).1
          ((mem_relDomain_iff _ _ _).mp hzD).2).continuousWithinAt.mem_closure_image
            (hDdense F hzF)
      have hsub : relMap (rdrv (r ω)) s '' D F ⊆ ballsK G := by
        rintro _ ⟨y, hy, rfl⟩
        have hyD := hFD (ballsU_subset_ballsK F (hDsub F hy))
        have hh := hD y hy
        rwa [show f y ω = relMap (rdrv (r ω)) s y from
          indicator_of_mem (show ω ∈ {ω | y ∈ relDomain (rdrv (r ω)) s} from hyD) _] at hh
      exact ⟨_, ⟨z, ⟨hzK, hzD⟩, rfl⟩,
        hGU (closure_minimal hsub (isCompact_ballsK G).isClosed hzc)⟩
  rw [he]
  refine MeasurableSet.biUnion (Set.to_countable _) fun F hFH =>
    MeasurableSet.biUnion (Set.to_countable _) fun G _ => ?_
  refine (((measurableSet_compact_subset_record_domain s
    (isCompact_ballsK F) hFH).preimage hr).inter
    (hK (LocalSets.measurableSet_hitting (isOpen_ballsU F)
      ((ballsU_subset_ballsK F).trans hFH)))).inter ?_
  exact MeasurableSet.biInter (hDcnt F) fun z _ =>
    (hfm z) (isCompact_ballsK G).isClosed.measurableSet

end InteractingSLE.Theorem14.GW2TipSystem.RootZ21

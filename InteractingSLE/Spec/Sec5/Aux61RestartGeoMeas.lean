import InteractingSLE.Spec.Sec5.Aux61RestartGeoRecord
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYFillMeas

/-!
# Measurability of the canonical restart hull record

Packet PROVE-AUX61-R1. Closed-ball observations of a random domain determine
open hits of its complement. Retargeting preserves hitting measurability, and
the existing compact-avoidance reader determines closed-square hits of its
Euclidean closure. Thus the canonical record needs no extra stochastic input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

open InteractingSLE.Restart LocalSets

/-- Closed-ball inclusion tests determine the hitting-measurable complement
inside H. Rational discs witness every open hit, including thin hulls. -/
theorem measurable_complementH_of_closedBall
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → Set ℂ}
    (hDm : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ D ω}) :
    Measurable[_, hittingSigma] (fun ω => H \ D ω) := by
  apply measurable_generateFrom
  rintro _ ⟨V, hVo, hVH, rfl⟩
  have heq : (fun ω => H \ D ω) ⁻¹' {A | (A ∩ V).Nonempty} =
      ⋃ k : ℕ, {_ω | closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ V} ∩
        {ω | closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ D ω}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨z, ⟨_, hzD⟩, hzV⟩
      obtain ⟨k, hzk, hkV⟩ := exists_ratDisc hVo hzV
      exact ⟨k, hkV, fun h => hzD (h (ball_subset_closedBall hzk))⟩
    · rintro ⟨k, hkV, hkD⟩
      obtain ⟨z, hzk, hzD⟩ := not_subset.1 hkD
      exact ⟨z, ⟨hVH (hkV hzk), hzD⟩, hkV hzk⟩
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    (MeasurableSet.const _).inter (hDm _ _).compl

/-- A fixed continuous retargeting of H preserves the hitting sigma algebra. -/
theorem measurable_image_stripRightRetarget :
    Measurable[hittingSigma, hittingSigma]
      (fun A : Set ℂ => stripRightRetarget '' (A ∩ H)) := by
  refine @measurable_generateFrom (Set ℂ) (Set ℂ) hittingSigma _ _ ?_
  rintro _ ⟨V, hVo, _, rfl⟩
  have heq : (fun A : Set ℂ => stripRightRetarget '' (A ∩ H)) ⁻¹'
      {B | (B ∩ V).Nonempty} =
      {A | (A ∩ (H ∩ stripRightRetarget ⁻¹' V)).Nonempty} := by
    ext A
    constructor
    · rintro ⟨_, ⟨z, ⟨hzA, hzH⟩, rfl⟩, hzV⟩
      exact ⟨z, hzA, hzH, hzV⟩
    · rintro ⟨z, hzA, hzH, hzV⟩
      exact ⟨stripRightRetarget z, ⟨z, ⟨hzA, hzH⟩, rfl⟩, hzV⟩
  rw [heq]
  exact measurableSet_hitting
    (isConformalBijection_stripRightRetarget.1.continuousOn.isOpen_inter_preimage
      QuantumZipper.isOpen_H hVo) inter_subset_left

/-- Retargeting the domain complement gives exactly the filled retained hull. -/
theorem stripTargetHull_eq_image_complement {D : Set ℂ} (hDH : D ⊆ H) :
    stripTargetHull D = stripRightRetarget '' (H \ D) := by
  rw [isConformalBijection_stripRightRetarget.2.injOn.image_sdiff_subset hDH,
    isConformalBijection_stripRightRetarget.2.image_eq]
  rfl

/-- The actual retargeted filled hull is hitting-measurable from the old domain
observations; its unbounded physical predecessor need not have a compact trace. -/
theorem measurable_stripTargetHull
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → Set ℂ}
    (hDH : ∀ ω, D ω ⊆ H)
    (hDm : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ D ω}) :
    Measurable[_, hittingSigma] (fun ω => stripTargetHull (D ω)) := by
  have hm := measurable_image_stripRightRetarget.comp
    (measurable_complementH_of_closedBall hDm)
  convert hm using 1
  funext ω
  change stripTargetHull (D ω) = stripRightRetarget '' ((H \ D ω) ∩ H)
  rw [inter_eq_left.mpr sdiff_subset, stripTargetHull_eq_image_complement (hDH ω)]

/-- Closed-square hits of the canonical Euclidean closure record follow from
the existing compact-avoidance reader for hitting-measurable H-hulls. -/
theorem isDyadicHitMeasurable_originalTargetRecord
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → Set ℂ}
    (hDH : ∀ ω, D ω ⊆ H)
    (hDm : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ D ω}) :
    IsDyadicHitMeasurable (fun ω => originalTargetRecord (D ω)) := by
  intro n k
  have hm := measurable_stripTargetHull hDH hDm
    (FlowStopIdentCMI.measurableSet_disjoint_closure_interH (isCompact_dyadicSquare n k)).compl
  convert hm using 1
  ext ω
  simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff,
    not_disjoint_iff_nonempty_inter]
  change (dyadicSquare n k ∩ closure (stripTargetHull (D ω))).Nonempty ↔
    (dyadicSquare n k ∩ closure (stripTargetHull (D ω) ∩ H)).Nonempty
  have hh : stripTargetHull (D ω) ∩ H = stripTargetHull (D ω) :=
    inter_eq_left.mpr sdiff_subset
  rw [hh]

end InteractingSLE.Sec5.Aux61Restart

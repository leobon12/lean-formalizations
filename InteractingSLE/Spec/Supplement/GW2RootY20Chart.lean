/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlFwd
import InteractingSLE.Spec.Supplement.GB6CoordBMeas
import InteractingSLE.Spec.Exist.StagedLaw3Beta
import InteractingSLE.Spec.Exist.StagedLaw2Flow

/-!
# Borel forward chart images of countable physical codes

Packet PROVE-T14-GW2ROOT2. The retained record supplies a continuous
normalized driver at every sample. R5's random-point evaluation theorem
then applies to its forward relative chart. Only points in the actual
open domain are kept in the image code.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootY20

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.CoordB

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A recorded joint chart's domain event at a measurable physical point. -/
theorem measurableSet_record_domain (s : ℝ≥0) {r : Ω → RecData}
    (hr : Measurable r) {z : Ω → ℂ} (hz : Measurable z) :
    MeasurableSet {ω | z ω ∈ relDomain (rdrv (r ω)) s} := by
  have hsol := (measurable_fwdMap_param
    (fun ω => continuous_rdrv (r ω))
    (fun t => (measurable_rdrv_apply t).comp hr)
    (fun ω => rdrv_zero (r ω)) (measurable_const (a := (s : ℝ)))
    (fun _ => s.coe_nonneg) hz.inv.neg).2
  have he : {ω | z ω ∈ relDomain (rdrv (r ω)) s} =
      {ω | z ω ∈ H} ∩ {ω | ∃ u, QuantumZipper.IsForwardSol
        (rdrv (r ω)) (-(z ω)⁻¹) s u} := by
    ext ω
    simp only [mem_relDomain_iff, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hH, hK⟩
      exact ⟨hH, QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull
        s.coe_nonneg (neg_inv_mem_H hH) hK⟩
    · rintro ⟨hH, u, hu⟩
      exact ⟨hH, Ito.notMem_fwdHull_of_isForwardSol (continuous_rdrv _)
        (neg_inv_mem_H hH) s.coe_nonneg hu⟩
  rw [he]
  exact (hz QuantumZipper.isOpen_H.measurableSet).inter hsol

/-- R5's random-point forward-map evaluation for the actual recorded chart. -/
theorem measurable_indicator_record_chart (s : ℝ≥0) {r : Ω → RecData}
    (hr : Measurable r) {z : Ω → ℂ} (hz : Measurable z) :
    Measurable ({ω | z ω ∈ relDomain (rdrv (r ω)) s}.indicator
      fun ω => relMap (rdrv (r ω)) s (z ω)) := by
  let E := {ω | z ω ∈ relDomain (rdrv (r ω)) s}
  have hE : MeasurableSet E := measurableSet_record_domain s hr hz
  let V : ℝ≥0 → Ω → ℝ := fun t ω => rdrv (r ω) t
  have he : ∀ ω, Ito.rpath (V · ω) = rdrv (r ω) := by
    intro ω
    funext t
    simp only [Ito.rpath, V, rdrv, Real.toNNReal_coe]
  have hm : ∀ y, Measurable ({ω | y ∈ relDomain (rdrv (r ω)) s}.indicator
      fun ω => relMap (rdrv (r ω)) s y) := by
    intro y
    have h := measurable_indicator_relMap (V := V)
      (fun t => (measurable_rdrv_apply t).comp hr)
      (fun ω => (continuous_rdrv _).comp NNReal.continuous_coe)
      (fun ω => rdrv_zero (r ω)) s y
    simpa only [he] using h
  apply Sec7.R5Enl.measurable_indicator_comp_of_continuousAt hE
    (D := fun ω => relDomain (rdrv (r ω)) s)
    (fun ω _ => isOpen_relDomain (continuous_rdrv _) s.coe_nonneg)
    (fun y => hE.inter (measurableSet_record_domain s hr measurable_const))
    (fun y => ?_) hz (fun _ hω => hω) (fun ω hω => ?_)
  · simpa only [indicator_indicator, inter_comm] using (hm y).indicator hE
  · exact continuousAt_relMap (continuous_rdrv _) s.coe_nonneg
      ((mem_relDomain_iff _ _ _).mp hω).1 ((mem_relDomain_iff _ _ _).mp hω).2

/-- The visible image of a countable physical code in a recorded chart. -/
def codeImage {ι : Type*} (s : ℝ≥0) (r : RecData) (F : ι → ℂ) : Set ℂ :=
  relMap (rdrv r) s '' (range F ∩ relDomain (rdrv r) s)

/-- This image is hitting measurable on the entire sample space. -/
theorem measurable_codeImage {ι : Type*} [Countable ι] (s : ℝ≥0)
    {r : Ω → RecData} (hr : Measurable r) {F : Ω → ι → ℂ}
    (hF : ∀ i, Measurable fun ω => F ω i) :
    Measurable[mΩ, hittingSigma] fun ω => codeImage s (r ω) (F ω) := by
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, _, rfl⟩
  have he : (fun ω => codeImage s (r ω) (F ω)) ⁻¹'
      {A : Set ℂ | (A ∩ U).Nonempty} =
      ⋃ i, {ω | F ω i ∈ relDomain (rdrv (r ω)) s} ∩
        ({ω | F ω i ∈ relDomain (rdrv (r ω)) s}.indicator
          fun ω => relMap (rdrv (r ω)) s (F ω i)) ⁻¹' U := by
    ext ω
    simp only [codeImage, mem_preimage, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨_, ⟨z, ⟨⟨i, rfl⟩, hz⟩, rfl⟩, hU⟩
      exact ⟨i, hz, by rwa [indicator_of_mem (show ω ∈ {ω | F ω i ∈ relDomain (rdrv (r ω)) s} from hz)]⟩
    · rintro ⟨i, hz, hU⟩
      rw [indicator_of_mem (show ω ∈ {ω | F ω i ∈ relDomain (rdrv (r ω)) s} from hz)] at hU
      exact ⟨_, ⟨_, ⟨mem_range_self i, hz⟩, rfl⟩, hU⟩
  rw [he]
  exact MeasurableSet.iUnion fun i =>
    (measurableSet_record_domain s hr (hF i)).inter
      ((measurable_indicator_record_chart s hr (hF i)) hU.measurableSet)

end InteractingSLE.Theorem14.GW2TipSystem.RootY20

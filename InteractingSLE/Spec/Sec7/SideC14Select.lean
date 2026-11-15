/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainRecord
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofStrip
import InteractingSLE.Spec.Sec7.PocketStopFieldUnion

/-!
# Selecting the original change pocket from the labelled wall record

PROVE-SIDE-COLLAR2. Use the existing pocket membership and filled-record
criteria. The source pocket is a component of the complement of its
complete walls; off the candidate event the selected open set is empty.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideC14

open LocalSets Aux119Nested PocketCoord PocketJordan PocketUnionPt PocketStopSide PocketStopWalls
open WangWu (negInv)
open PocketStopField

open Classical in
/-- The original open pocket on its candidate event, empty elsewhere. -/
def selectedChangePocket {Ω : Type*} (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) : Ω → Set ℂ :=
  fun ω => if ω ∈ A then changePocket (R ω) (L ω) r else ∅

/-- The original walls bound the original flow pocket, in both shapes.
Transport the existing counterflow frontier enclosure back by inversion. -/
theorem changePocket_wall_props {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r) :
    Disjoint (H ∩ (range R ∪ range L)) (changePocket R L r) ∧
      frontier (changePocket R L r) ∩ H ⊆ range R ∪ range L := by
  refine ⟨Set.disjoint_left.2 (fun z hz hzC => (h.changePocket_subset hzC).2 hz.2), ?_⟩
  intro z hz
  have hz0 := WangWu.ne_zero_of_mem_H hz.2
  have hcl : negInv z ∈ closure (cfPocket R L r) :=
    ((continuousAt_id.inv₀ hz0).neg).continuousWithinAt.mem_closure_image hz.1.1
  have hnot : negInv z ∉ cfPocket R L r := by
    rintro ⟨w, hw, he⟩
    have he' : w = z := by simpa only [WangWu.negInv_negInv] using congrArg negInv he
    exact hz.1.2 (by rw [h.isOpen_changePocket.interior_eq]; exact he' ▸ hw)
  have hfr : negInv z ∈ frontier (cfPocket R L r) := by
    change negInv z ∈ frontier (negInv '' changePocket R L r)
    rw [(isOpen_image_negInv' h.isOpen_changePocket h.changePocket_subset_H).frontier_eq]
    exact ⟨hcl, hnot⟩
  obtain ⟨w, hw, he⟩ := (cfPocket_walls_props h).2
    ⟨hfr, WangWu.negInv_mem_H hz.2⟩
  have he' : w = z := by simpa only [WangWu.negInv_negInv] using congrArg negInv he
  exact he' ▸ hw

/-- All selected-pocket component facts hold pathwise, without any
hypothesis about a conditional mean or the counterflow. -/
theorem selectedChangePocket_geometry {Ω : Type*} {A : Set Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r) :
    (∀ ω, IsOpen (selectedChangePocket A R L r ω)) ∧
    (∀ ω, selectedChangePocket A R L r ω ⊆ H \ wallUnion L R ω) ∧
    (∀ ω, ∀ z ∈ selectedChangePocket A R L r ω,
      connectedComponentIn (H \ wallUnion L R ω) z ⊆ selectedChangePocket A R L r ω) := by
  have hU : ∀ ω, H \ wallUnion L R ω = H \ (range (R ω) ∪ range (L ω)) := by
    intro ω; rw [H_diff_wallUnion, union_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ A
    · simpa only [selectedChangePocket, ite_eq_left hω] using (hcfg ω hω).isOpen_changePocket
    · simp only [selectedChangePocket, ite_eq_right hω, isOpen_empty]
  · intro ω
    by_cases hω : ω ∈ A
    · simpa only [selectedChangePocket, ite_eq_left hω, hU] using (hcfg ω hω).changePocket_subset
    · simp only [selectedChangePocket, ite_eq_right hω, empty_subset]
  · intro ω z hz
    have hω : ω ∈ A := by
      by_contra hn
      simp only [selectedChangePocket, ite_eq_right hn, mem_empty_iff_false] at hz
    rw [selectedChangePocket, ite_eq_left hω] at hz ⊢
    obtain ⟨w, -, he, -⟩ := (hcfg ω hω).changePocket_eq
    rw [he] at hz ⊢
    rw [hU, ← connectedComponentIn_eq hz]

/-- The exact original exterior is measurable from the same wall record
that selects the candidate event; no field law is used for selection. -/
theorem measurable_selectedChangePocket_exterior
    {Ω : Type*} {ℋ : MeasurableSpace Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {A : Set Ω}
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hRm : ∀ t, Measurable[ℋ] fun ω => R ω t)
    (hLm : ∀ t, Measurable[ℋ] fun ω => L ω t)
    (hA : MeasurableSet[ℋ] A) (hcfg : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r) :
    Measurable[ℋ, hittingSigma] (fun ω => H \ selectedChangePocket A R L r ω) := by
  have hPoint : ∀ z, MeasurableSet[ℋ] {ω | ω ∈ A ∧ z ∈ changePocket (R ω) (L ω) r} := by
    intro z
    have hm := measurableSet_mem_cfPocket_of_subset hRm hLm hA hcfg hA (Subset.refl A) (negInv z)
    have he : {ω | ω ∈ A ∧ negInv z ∈ cfPocket (R ω) (L ω) r} =
        {ω | ω ∈ A ∧ z ∈ changePocket (R ω) (L ω) r} := by
      ext ω
      constructor
      · rintro ⟨hω, w, hw, he⟩
        have he' : w = z := by simpa only [WangWu.negInv_negInv] using congrArg negInv he
        exact ⟨hω, he' ▸ hw⟩
      · rintro ⟨hω, hz⟩
        exact ⟨hω, mem_image_of_mem negInv hz⟩
    rwa [he] at hm
  have hHist : Measurable[ℋ] (fullHist ![R, L]) :=
    measurable_fullHist (mΩ := ℋ) (by intro i; fin_cases i <;> assumption)
  have hWalls := (FlatClockProof.measurable_wallUnion_fullHist hRc hLc).mono hHist.comap_le le_rfl
  have hFilled := measurable_eventFilled hA hPoint
    (fun ω hω => (hcfg ω hω).isOpen_changePocket)
    (fun ω hω => (changePocket_wall_props (hcfg ω hω)).1)
    (fun ω hω => (changePocket_wall_props (hcfg ω hω)).2)
    (F := fun _ => ∅) (by
      have he : (fun ω => H ∩ ((range (R ω) ∪ range (L ω)) ∪ ∅)) = wallUnion R L := by
        funext ω
        rw [union_empty, inter_comm]
        rfl
      rw [he]
      exact hWalls)
  have he : eventFilled A (fun ω => changePocket (R ω) (L ω) r) (fun _ => ∅) =
      fun ω => H \ selectedChangePocket A R L r ω := by
    funext ω
    by_cases hω : ω ∈ A <;>
      simp only [eventFilled, selectedChangePocket, hω, ↓reduceIte, PocketUnionPt.extHullSet,
        union_empty, sdiff_empty]
    ext z
    simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
  rw [he] at hFilled
  exact hFilled

end InteractingSLE.Sec7.SideC14

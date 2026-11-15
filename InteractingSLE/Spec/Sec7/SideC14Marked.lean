/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC13Filled
import InteractingSLE.Spec.Sec6.Prop61BMarked
import InteractingSLE.Spec.Sec7.PocketStopWallsWalls
import InteractingSLE.Spec.Sec7.Aux119Nested
import InteractingSLE.Spec.Sec7.PocketWordPerQSigma
import InteractingSLE.Spec.Sec7.Lemma72EHit

/-!
# The filled mean for a pocket selected from the complete labelled walls

PROVE-SIDE-COLLAR2. Discharge the history-marked locality needed for
filling using Lemma 6.2's complete ordered histories. The selected pocket
may be any union of components measurable from these histories.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideC14

open LocalSets WholeField Aux119Nested PocketStopWalls

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- Complete field-determined local paths retain Lemma 6.2's marked
avoidance property with their entire ordered histories as marks. -/
theorem isHistoryAvoidanceLocal_fullHist {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ} {x : Fin k → ℂ}
    (hhm : Measurable h) (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i)
    (hm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, Sec6.IsEntranceHistoryLocal (η i) h P) :
    IsHistoryAvoidanceLocal (MeasurableSpace.comap (fullHist η) inferInstance)
      (fun ω => (⋃ i, range (η i ω)) ∩ H) h P := by
  have hmarked := Sec6.isHistoryAvoidanceLocal_explored (τ := fun _ _ => ⊤)
    (S := fun _ _ _ => ⊤) hhm hc h0 hm hdet hloc
    (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
  have he : Sec6.explored η (fun _ _ => ⊤) =
      fun ω => (⋃ i, range (η i ω)) ∩ H := funext (explored_top η)
  rw [he] at hmarked
  exact hmarked

/-- The two complete walls satisfy the marked criterion; no marked
locality premise needs to be supplied in the filled-pocket comparison. -/
theorem isHistoryAvoidanceLocal_wallUnion_fullHist {β α : Ω → ℝ≥0 → ℂ}
    (hhm : Measurable h)
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (h ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β h P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (h ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α h P) :
    IsHistoryAvoidanceLocal (MeasurableSpace.comap (fullHist ![β, α]) inferInstance)
      (wallUnion β α) h P := by
  have hc : ∀ i ω, Continuous ((![β, α] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := by
    intro i; fin_cases i <;> assumption
  have h0 : ∀ i ω, (![β, α] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = 0 := by
    intro i; fin_cases i <;> assumption
  have hm : ∀ i t, Measurable fun ω => (![β, α] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := by
    intro i; fin_cases i <;> assumption
  have hd : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![β, α] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (h ω) := by
    intro i; fin_cases i <;> assumption
  have hl : ∀ i, Sec6.IsEntranceHistoryLocal ((![β, α] : Fin 2 → Ω → ℝ≥0 → ℂ) i) h P := by
    intro i; fin_cases i <;> assumption
  have hmarked := isHistoryAvoidanceLocal_fullHist hhm hc h0 hm hd hl
  have he : (fun ω => (⋃ i, range ((![β, α] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω)) ∩ H) =
      wallUnion β α := by
    funext ω
    ext z
    simp only [wallUnion, mem_inter_iff, mem_iUnion, mem_union]
    constructor
    · rintro ⟨⟨i, hi⟩, hzH⟩
      fin_cases i
      · exact ⟨Or.inl hi, hzH⟩
      · exact ⟨Or.inr hi, hzH⟩
    · rintro ⟨hz | hz, hzH⟩
      · exact ⟨⟨0, hz⟩, hzH⟩
      · exact ⟨⟨1, hz⟩, hzH⟩
  rw [he] at hmarked
  exact hmarked

/-- The original filled-pocket mean agrees with the wall mean on a
labelled selected pocket, with all marking and local-set laws discharged. -/
theorem ae_representatives_filled_eq_wallMean {β α : Ω → ℝ≥0 → ℂ}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (h ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β h P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (h ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α h P)
    (htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (Bornology.cobounded ℂ) ∧
      Tendsto (α ω) atTop (Bornology.cobounded ℂ))
    {C : Ω → Set ℂ}
    (hCm : Measurable[PocketWordPerQ.wallsSigma P α β, hittingSigma]
      (fun ω => H \ C ω))
    (hCo : ∀ ω, IsOpen (C ω)) (hCs : ∀ ω, C ω ⊆ H \ wallUnion β α ω)
    (hCc : ∀ᵐ ω ∂P, ∀ z ∈ C ω, connectedComponentIn (H \ wallUnion β α ω) z ⊆ C ω)
    {gU gC : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) h P gU)
    (hgC : IsLocalSetMean (fun ω => H \ C ω) h P gC) :
    ∀ᵐ ω ∂P, ∀ vC vU : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vC (C ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω → gC ω φ = ∫ z, vC z * φ z) →
      InnerProductSpace.HarmonicOnNhd vU (H \ wallUnion β α ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion β α ω →
        gU ω φ = ∫ z, vU z * φ z) → EqOn vC vU (C ω) := by
  obtain ⟨hUm, hUloc, -⟩ := isLocalSet_wallUnion hh hβc hβ0 hβm hβdet hβloc
    hαc hα0 hαm hαdet hαloc htr
  have hmark := isHistoryAvoidanceLocal_wallUnion_fullHist hh.measurable
    hαc hα0 hαm hαdet hαloc hβc hβ0 hβm hβdet hβloc
  rw [wallUnion_comm α β] at hmark
  have hHist := PocketWordPerQ.wallsSigma_le (P := P) hαm hβm
  have hmark' := Lemma72E.isHistoryAvoidanceLocal_sup_nullSets hmark
  exact SideC13.ae_representatives_filled_eq_marked hh hUm (fun _ => inter_subset_right)
    hHist hUloc hmark' (hCm.mono le_sup_right le_rfl) hCo hCs hCc hgU hgC

end InteractingSLE.Sec7.SideC14

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLeafLaunch
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# Transferring SB4's height classification to a launch witness

Packet PROVE-T14-SBTAIL2. The launch clause permits arbitrary finite sets of jump candidates.
Equality off the union of two such sets does not directly give the classification at every
point outside the launch witness's own set. Local constancy and density remove the extra
exceptions. This transfers an established classification of the actual conditional word;
it does not establish that geometric classification or identify the actual relative walk.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.SB.Leaf

/-- A classification of boundary heights on an open set is independent of the chosen
piecewise-constant datum for the same GFF, with only the new datum's jump candidates excluded.
No closedness assumption on the allowed heights is needed. -/
theorem boundary_heights_mem_of_same_gff {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}
    (hb₁ : IsPiecewiseConstantBoundaryData b₁ J₁)
    (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂)
    (h₁ : IsGFFWithBoundaryData Q h b₁ J₁) (h₂ : IsGFFWithBoundaryData Q h b₂ J₂)
    {V T : Set ℝ} (hV : IsOpen V) (hT : ∀ x ∈ V, x ∉ J₂ → b₂ x ∈ T) :
    ∀ x ∈ V, x ∉ J₁ → b₁ x ∈ T := by
  intro x hx hxJ
  have hd : Dense ((↑(J₁ ∪ J₂) : Set ℝ)ᶜ) := by
    rw [compl_eq_univ_sdiff]
    exact dense_univ.sdiff_finset (J₁ ∪ J₂)
  obtain ⟨y, hyJ, hyV, hyb⟩ := hd.inter_nhds_nonempty
    (inter_mem (hV.mem_nhds hx) (hb₁ x hxJ))
  have he := Exist.StagedLaw.eq_of_isGFFWithBoundaryData hb₁ hb₂ h₁ h₂ y hyJ
  rw [← hyb, he]
  exact hT y hyV (fun hy => hyJ (Finset.mem_union_right _ hy))

/-- SB4's middle-word classification for a known datum of the translated conditional field
holds for every witness of the staged launch clause. The canonical datum may have additional
jump candidates, even inside the middle interval. -/
theorem launch_height_classification {κ : ℝ} (hκ : 0 < κ) {Ω : Type*}
    [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hl : Ω → DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') {θ : ℝ} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b' J' θ Q hl W ζ) (m : ℝ)
    {bc : ℝ → ℝ} {jc : Finset ℝ} (hbc : IsPiecewiseConstantBoundaryData bc jc)
    (hG : IsGFFWithBoundaryData Q (fun ω => FlowDilate.affField m one_pos (hl ω)) bc jc)
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ}
    (hclass : ∀ x ∈ Ioo m 0, x ∉ jc →
      (∃ p ∈ l, bc x = sleLambda κ - p.1 * chiC κ ∨ bc x = -sleLambda κ - p.1 * chiC κ) ∨
        bc x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨ bc x ∈ original) :
    ∀ x ∈ Ioo m 0, x ∉ FlowDilate.affJumps 1 m J' →
      (∃ p ∈ l, FlowDilate.affData 1 m b' x = sleLambda κ - p.1 * chiC κ ∨
        FlowDilate.affData 1 m b' x = -sleLambda κ - p.1 * chiC κ) ∨
        FlowDilate.affData 1 m b' x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨
        FlowDilate.affData 1 m b' x ∈ original := by
  have hG' := (GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl).affine_finset
    (m := m) one_pos
  exact boundary_heights_mem_of_same_gff
    (V := Ioo m 0)
    (T := {H | (∃ p ∈ l, H = sleLambda κ - p.1 * chiC κ ∨
        H = -sleLambda κ - p.1 * chiC κ) ∨
      H ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨ H ∈ original})
    (FlowDilate.isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb') hbc hG' hG
    isOpen_Ioo hclass

end InteractingSLE.Theorem14.SB.Leaf

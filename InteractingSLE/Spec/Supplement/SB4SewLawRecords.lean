/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewAssembly
import InteractingSLE.Spec.Supplement.StagedDet
import InteractingSLE.Spec.Supplement.WalkPastDet
import InteractingSLE.Spec.Supplement.KernelTower

/-!
# Joint retained records for the SB4 sewing construction

Two staged histories of the same field have one joint Borel record. The same
record identity holds under almost every retained conditional kernel, and its
joint law with the field is the graph pushforward of the conditional field law.
Theorems 1.2--1.3 enter only through the landed staged determination theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.SewLaw

open Exist.Staged

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {s₁ s₂ : ExplSpec}
  {E₁ E₂ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k₁ k₂ : ℕ}

/-- The two retained pasts, with their labels and their own instruction counts. -/
def jointRecord (ω : Ω) : PastData k₁ × PastData k₂ :=
  (pastMap κ b jumps s₁ E₁ k₁ ω, pastMap κ b jumps s₂ E₂ k₂ ω)

/-- The joined retained sigma-algebra; no exterior projection is included yet. -/
@[instance_reducible]
def jointMarks : MeasurableSpace Ω :=
  pastSigma κ b jumps s₁ E₁ k₁ ⊔ pastSigma κ b jumps s₂ E₂ k₂

omit mΩ [StandardBorelSpace Ω] in
theorem jointMarks_eq_comap :
    jointMarks (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
      (E₁ := E₁) (E₂ := E₂) (k₁ := k₁) (k₂ := k₂) =
      MeasurableSpace.comap (jointRecord (κ := κ) (b := b) (jumps := jumps)
        (s₁ := s₁) (s₂ := s₂) (E₁ := E₁) (E₂ := E₂) (k₁ := k₁) (k₂ := k₂))
        inferInstance :=
  (MeasurableSpace.comap_prodMk _ _).symm

/-- The joint record is a Borel function of the same ambient field. -/
theorem exists_jointRecord_eq_comp_field
    (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE₁ : IsStagedHistory κ b jumps P h s₁ E₁)
    (hE₂ : IsStagedHistory κ b jumps P h s₂ E₂)
    (hR₁ : StagedPiecesRegular κ b jumps P s₁ E₁)
    (hR₂ : StagedPiecesRegular κ b jumps P s₂ E₂) (k₁ k₂ : ℕ) :
    ∃ f : DistOn upperHalfPlaneOpens → PastData k₁ × PastData k₂,
      Measurable f ∧
      jointRecord (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
        (E₁ := E₁) (E₂ := E₂) =ᵐ[P] f ∘ h := by
  obtain ⟨f₁, hm₁, he₁⟩ :=
    StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hE₁ hR₁ k₁
  obtain ⟨f₂, hm₂, he₂⟩ :=
    StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hE₂ hR₂ k₂
  refine ⟨fun X => (f₁ X, f₂ X), hm₁.prodMk hm₂, ?_⟩
  filter_upwards [he₁, he₂] with ω h₁ h₂
  exact Prod.ext h₁ h₂

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Both retained sigma-algebras are determined by the centred field. -/
theorem jointMarks_le_aeSigma_centred
    {f : DistOn upperHalfPlaneOpens → PastData k₁ × PastData k₂} (hf : Measurable f)
    (he : jointRecord (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
      (E₁ := E₁) (E₂ := E₂) =ᵐ[P] f ∘ h) (u₀ : ℂ → ℝ) :
    jointMarks (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
      (E₁ := E₁) (E₂ := E₂) (k₁ := k₁) (k₂ := k₂) ≤
      LocalSets.aeSigma
        (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P := by
  apply sup_le
  · exact WalkLaw.pastSigma_le_aeSigma_centred (measurable_fst.comp hf)
      (he.mono fun _ hω => congrArg Prod.fst hω) u₀
  · exact WalkLaw.pastSigma_le_aeSigma_centred (measurable_snd.comp hf)
      (he.mono fun _ hω => congrArg Prod.snd hω) u₀

/-- A field-determined joint record has the graph law under almost every
retained conditional measure. All pushforwards have measurable field/graph maps. -/
theorem ae_conditional_jointRecord_law (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hhm : Measurable h)
    {f : DistOn upperHalfPlaneOpens → PastData k₁ × PastData k₂} (hf : Measurable f)
    (he : jointRecord (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
      (E₁ := E₁) (E₂ := E₂) =ᵐ[P] f ∘ h) :
    ∀ᵐ ω₀ ∂P,
      (condExpKernel P 𝒢.1 ω₀).map (fun ω => (h ω,
        jointRecord (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
          (E₁ := E₁) (E₂ := E₂) (k₁ := k₁) (k₂ := k₂) ω)) =
        ((condExpKernel P 𝒢.1 ω₀).map h).map (fun X => (X, f X)) := by
  have hk := KernelTower.ae_ae_condExpKernel_of_ae 𝒢.2 he
  filter_upwards [hk] with ω₀ hω₀
  rw [Measure.map_map (g := fun X => (X, f X)) (measurable_id.prodMk hf) hhm]
  apply Measure.map_congr
  exact hω₀.mono fun ω hω => Prod.ext rfl hω

end InteractingSLE.Theorem14.SB.SewLaw

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewLawRecords
import InteractingSLE.Spec.Supplement.WalkStageLocalAE
import InteractingSLE.Spec.Sec5.CrossCondLaw
import InteractingSLE.Spec.Restart.R1Flow

/-!
# The joined Gaussian kernel for two retained staged histories

The R58 measurable-version argument and the determined marked-union theorem
apply to arbitrary staged prefixes. They produce the joint germ/history
Gaussian law. The conditional mean is not identified with an active force word
here; that additional identification remains explicit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.SewLaw

open LocalSets Exist.Staged

section Union

variable {Ω : Type u} {ℋ₁ ℋ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens}
  {A₁ A₂ : Ω → Set ℂ}

/-- Two field-determined marked local sets with avoidance measurable up to null
sets have a measurable union version and the full joined Gaussian germ law. -/
theorem exists_joined_gaussian_version
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hℋ₁ : ℋ₁ ≤ mΩ) (hℋ₂ : ℋ₂ ≤ mΩ)
    (hAH₁ : ∀ ω, A₁ ω ⊆ H) (hAH₂ : ∀ ω, A₂ ω ⊆ H)
    (hAo₁ : ∀ᵐ ω ∂P, IsOpen (H \ A₁ ω))
    (hAo₂ : ∀ᵐ ω ∂P, IsOpen (H \ A₂ ω))
    (hA₁ : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma ℋ₁ P] {ω | Disjoint (A₁ ω) U})
    (hA₂ : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma ℋ₂ P] {ω | Disjoint (A₂ ω) U})
    (hd₁ : ℋ₁ ≤ aeSigma (MeasurableSpace.comap X inferInstance) P)
    (hd₂ : ℋ₂ ≤ aeSigma (MeasurableSpace.comap X inferInstance) P)
    (hl₁ : WholeField.IsHistoryAvoidanceLocal ℋ₁ A₁ X P)
    (hl₂ : WholeField.IsHistoryAvoidanceLocal ℋ₂ A₂ X P) :
    ∃ A : Ω → Set ℂ, Measurable[ℋ₁ ⊔ ℋ₂, hittingSigma] A ∧
      (∀ᵐ ω ∂P, A ω = A₁ ω ∪ A₂ ω) ∧
      WholeField.IsHistoryAvoidanceLocal (ℋ₁ ⊔ ℋ₂) A X P ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∃ M : Ω → ℝ, Measurable[germSigma A X] M ∧
        M =ᵐ[P] P[fun ω => X ω φ | germSigma A X ⊔ (ℋ₁ ⊔ ℋ₂)] ∧
        (fun ω => Complex.exp (Complex.I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov
            (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ)) =ᵐ[P]
          P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) |
            germSigma A X ⊔ (ℋ₁ ⊔ ℋ₂)] := by
  obtain ⟨B₁, hBH₁, hBe₁, hBm₁⟩ := WalkLaw.exists_version_of_aeSigma hAH₁ hAo₁ hA₁
  obtain ⟨B₂, hBH₂, hBe₂, hBm₂⟩ := WalkLaw.exists_version_of_aeSigma hAH₂ hAo₂ hA₂
  have hloc := WalkLaw.isHistoryAvoidanceLocal_union_of_det hX.measurable hBm₁ hBm₂
    hd₁ hd₂ (WalkLaw.isHistoryAvoidanceLocal_congr_ae (hBe₁.mono fun _ he => he.symm) hl₁)
      (WalkLaw.isHistoryAvoidanceLocal_congr_ae (hBe₂.mono fun _ he => he.symm) hl₂)
  have hAm : Measurable[ℋ₁ ⊔ ℋ₂, hittingSigma] (fun ω => B₁ ω ∪ B₂ ω) := by
    apply WalkLaw.measurable_hitting_of_avoid (mΩ := ℋ₁ ⊔ ℋ₂) le_rfl
    intro U hUH
    have he : {ω | Disjoint (B₁ ω ∪ B₂ ω) U} =
        {ω | Disjoint (B₁ ω) U} ∩ {ω | Disjoint (B₂ ω) U} := by
      ext ω
      exact disjoint_union_left
    rw [he]
    exact ((le_sup_left : ℋ₁ ≤ ℋ₁ ⊔ ℋ₂) _ (hBm₁ U hUH)).inter
      ((le_sup_right : ℋ₂ ≤ ℋ₁ ⊔ ℋ₂) _ (hBm₂ U hUH))
  have hAc : ∀ᵐ ω ∂P, (B₁ ω ∪ B₂ ω) ⊆ H ∧ IsOpen (H \ (B₁ ω ∪ B₂ ω)) := by
    filter_upwards [hBe₁, hBe₂, hAo₁, hAo₂] with ω he₁ he₂ ho₁ ho₂
    refine ⟨union_subset (hBH₁ ω) (hBH₂ ω), ?_⟩
    rw [he₁, he₂]
    have he : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
      tauto
    rw [he]
    exact ho₁.inter ho₂
  refine ⟨fun ω => B₁ ω ∪ B₂ ω, hAm, ?_, hloc,
    fun φ => WholeField.exists_condExp_germSigma_history
      hX (hAm.mono (sup_le hℋ₁ hℋ₂) le_rfl) (sup_le hℋ₁ hℋ₂) hloc hAc φ⟩
  filter_upwards [hBe₁, hBe₂] with ω he₁ he₂
  rw [he₁, he₂]

end Union

section Stages

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {s₁ s₂ : ExplSpec}
  {E₁ E₂ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k₁ k₂ : ℕ} {u₀ : ℂ → ℝ}

/-- The joint Gaussian law for two staged prefixes, from their individual
marked localities. Determination, avoidance measurability and relative
closedness follow from the landed staged tools. The mean stays unidentified. -/
theorem exists_joint_stage_gaussian
    (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE₁ : IsStagedHistory κ b jumps P h s₁ E₁)
    (hE₂ : IsStagedHistory κ b jumps P h s₂ E₂)
    (hR₁ : StagedPiecesRegular κ b jumps P s₁ E₁)
    (hR₂ : StagedPiecesRegular κ b jumps P s₂ E₂)
    (hr₁ : ∀ j ω, IsRegularDriver (E₁ j ω))
    (hr₂ : ∀ j ω, IsRegularDriver (E₂ j ω))
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hl₁ : WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps s₁ E₁ k₁)
      (WalkLaw.stageSet κ b jumps s₁ E₁ k₁) (WholeField.centredField h u₀) P)
    (hl₂ : WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps s₂ E₂ k₂)
      (WalkLaw.stageSet κ b jumps s₂ E₂ k₂) (WholeField.centredField h u₀) P) :
    ∃ A : Ω → Set ℂ,
      Measurable[jointMarks (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
        (E₁ := E₁) (E₂ := E₂) (k₁ := k₁) (k₂ := k₂), hittingSigma] A ∧
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps s₁ E₁ k₁ ω ∪
        WalkLaw.stageSet κ b jumps s₂ E₂ k₂ ω) ∧
      WholeField.IsHistoryAvoidanceLocal
        (jointMarks (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
          (E₁ := E₁) (E₂ := E₂) (k₁ := k₁) (k₂ := k₂))
        A (WholeField.centredField h u₀) P ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∃ M : Ω → ℝ,
        Measurable[germSigma A (WholeField.centredField h u₀)] M ∧
        M =ᵐ[P] P[fun ω => WholeField.centredField h u₀ ω φ |
          germSigma A (WholeField.centredField h u₀) ⊔
            jointMarks (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
              (E₁ := E₁) (E₂ := E₂) (k₁ := k₁) (k₂ := k₂)] ∧
        (fun ω => Complex.exp (Complex.I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov
            (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ)) =ᵐ[P]
          P[fun ω => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω φ : ℂ)) |
            germSigma A (WholeField.centredField h u₀) ⊔
              jointMarks (κ := κ) (b := b) (jumps := jumps) (s₁ := s₁) (s₂ := s₂)
                (E₁ := E₁) (E₂ := E₂) (k₁ := k₁) (k₂ := k₂)] := by
  obtain ⟨f, hfm, hfe⟩ := exists_jointRecord_eq_comp_field h12p h13 hκ hκ4 hb hh
    hE₁ hE₂ hR₁ hR₂ k₁ k₂
  have hd := jointMarks_le_aeSigma_centred hfm hfe u₀
  exact exists_joined_gaussian_version
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀)
    (hE₁.2.1 k₁) (hE₂.2.1 k₂) (fun _ => inter_subset_right) (fun _ => inter_subset_right)
    (WalkLaw.ae_isOpen_H_diff_stageSet hR₁ k₁) (WalkLaw.ae_isOpen_H_diff_stageSet hR₂ k₂)
    (fun U hUH => WalkLaw.measurableSet_aeSigma_stageSet_avoid hb hE₁.1 hr₁ hR₁
      hE₁.2.1 k₁ U.isOpen hUH)
    (fun U hUH => WalkLaw.measurableSet_aeSigma_stageSet_avoid hb hE₂.1 hr₂ hR₂
      hE₂.2.1 k₂ U.isOpen hUH)
    (le_sup_left.trans hd) (le_sup_right.trans hd) hl₁ hl₂

end Stages

end InteractingSLE.Theorem14.SB.SewLaw

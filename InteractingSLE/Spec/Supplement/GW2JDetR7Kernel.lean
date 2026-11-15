/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR7Union
import InteractingSLE.Spec.Sec7.R5EnlLocal

/-!
# The actual physical union kernel with both own germs retained

The retained-history locality proved from the original couplings gives the
Gaussian kernel of their union. The landed R.5 mean comparison identifies its
retained mean with the local-set mean as a whole distribution.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open QuantumZipper (H chiC fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR7

open Restart Exist Exist.StagedLaw WholeField LocalSets
open Supp8.GB6 Supp8.GB6LineL Supp8.Q3Chain GW2TipSystem

/-- Both stopped histories, both individual field germs, and the union germ. -/
@[instance_reducible]
def unionMarks {Ω : Type*} (ℋ : MeasurableSpace Ω) (A₁ A₂ : Ω → Set ℂ)
    (X : Ω → DistOn upperHalfPlaneOpens) : MeasurableSpace Ω :=
  germSigma (fun ω => A₁ ω ∪ A₂ ω) X ⊔
    (ℋ ⊔ (germSigma A₁ X ⊔ germSigma A₂ X))

/-- Retaining both individual germs preserves the union kernel. Its mean is
an actual local-set mean, not a new conditional mean hypothesis. -/
theorem exists_union_kernel_with_own_germs
    {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) (hℋ : ℋ ≤ mΩ)
    {A₁ A₂ : Ω → Set ℂ} (hA₁ : Measurable[ℋ, hittingSigma] A₁)
    (hA₂ : Measurable[ℋ, hittingSigma] A₂)
    (hc₁ : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω))
    (hc₂ : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hloc : IsHistoryAvoidanceLocal ℋ (fun ω => A₁ ω ∪ A₂ ω) X P) :
    unionMarks ℋ A₁ A₂ X ≤ mΩ ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) X P g ∧
        IsCondZeroBoundaryGFF P (unionMarks ℋ A₁ A₂ X)
          (fun ω => H \ (A₁ ω ∪ A₂ ω)) (fun ω => X ω - g ω) ∧
        ∀ φ : TestOn upperHalfPlaneOpens,
          P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) |
              unionMarks ℋ A₁ A₂ X] =ᵐ[P]
            fun ω => rangeKerCF (g ω) (H \ (A₁ ω ∪ A₂ ω)) φ := by
  let A : Ω → Set ℂ := fun ω => A₁ ω ∪ A₂ ω
  have hA : Measurable[ℋ, hittingSigma] A := by
    let : MeasurableSpace Ω := ℋ
    exact measurable_union_hitting hA₁ hA₂
  have hAm := hA.mono hℋ le_rfl
  have hg₁ := germSigma_le (hA₁.mono hℋ le_rfl) hX.measurable
  have hg₂ := germSigma_le (hA₂.mono hℋ le_rfl) hX.measurable
  have hmarks : ℋ ⊔ (germSigma A₁ X ⊔ germSigma A₂ X) ≤ mΩ :=
    sup_le hℋ (sup_le hg₁ hg₂)
  have hΓ : unionMarks ℋ A₁ A₂ X ≤ mΩ :=
    sup_le (germSigma_le hAm hX.measurable) hmarks
  have hreg : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hc₁, hc₂] with ω h₁ h₂
    refine ⟨union_subset h₁.1 h₂.1, ?_⟩
    change IsOpen (H \ (A₁ ω ∪ A₂ ω))
    have he : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, not_or]
      tauto
    rw [he]
    exact h₁.2.inter h₂.2
  have hl₁ := WFS.isHistoryAvoidanceLocal_sup_germSigma_of_ae_subset
    hX hℋ hAm hloc hA₁ (Eventually.of_forall fun _ => subset_union_left)
  have hl₂ := WFS.isHistoryAvoidanceLocal_sup_germSigma_of_ae_subset hX
    (sup_le hℋ hg₁) hAm hl₁ (hA₂.mono le_sup_left le_rfl)
    (Eventually.of_forall fun _ => subset_union_right)
  have hl : IsHistoryAvoidanceLocal
      (ℋ ⊔ (germSigma A₁ X ⊔ germSigma A₂ X)) A X P := by
    simpa only [sup_assoc] using hl₂
  obtain ⟨g', hg'm, hg'h, hg'k⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hX hAm hmarks hl hreg
  have hg'Γ : Measurable[unionMarks ℋ A₁ A₂ X] g' := hg'm.mono le_sup_left le_rfl
  have hAΓ : Measurable[unionMarks ℋ A₁ A₂ X, hittingSigma] A :=
    hA.mono (le_sup_left.trans le_sup_right) le_rfl
  obtain ⟨g, hg, he⟩ := Sec7.R5Enl.exists_localSetMean_eq_of_retained_kernel_noGerm
    hΓ hX hAΓ hg'Γ hreg hg'h hg'k
  have hk : IsCondZeroBoundaryGFF P (unionMarks ℋ A₁ A₂ X)
      (fun ω => H \ A ω) (fun ω => X ω - g ω) := by
    intro φ
    exact (condExp_congr_ae (he.mono fun ω hω => by
      dsimp only
      rw [hω])).trans (hg'k φ)
  refine ⟨hΓ, g, hg, hk, ?_⟩
  exact Sec7.R5Enl.condExp_exp_eq_rangeKerCF hΓ hX.measurable
    (hg.1.mono le_sup_left le_rfl) hk

end InteractingSLE.Theorem14.GW2JDetR7

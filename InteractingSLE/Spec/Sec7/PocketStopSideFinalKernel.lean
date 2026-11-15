/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsLaw
import InteractingSLE.GFF.LocalSets.Prop38

/-!
# Retaining both germs in a history-marked union

PROVE-STRIPSYS38. The Gaussian cover argument depends on marked avoidance, not on
field determination. Here it is reused with the pair of sets as retained marks.
Both individual germs are retained through the existing subset-to-cover lemma.
This is the kernel needed for the nested boundary comparison of Aux. 35, pp. 193–194;
it assumes no conditional independence of the two sets given the field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets LQGMetric

variable {Ω : Type*} {ℳ 𝒦 : MeasurableSpace Ω} {𝒮 : Set ℂ → MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- The existing cover proof of the conditional Gaussian law, with an arbitrary
valid marking. This factors out the conditional-independence producer of that
marking from the union theorem; all its analytic inputs are reused. -/
theorem exists_condLaw_of_coverMarking (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsAvoidanceLocal A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hmk : IsCoverMarking A h P ℳ 𝒮)
    (h𝒦A : germSigma A h ≤ 𝒦) (h𝒦le : 𝒦 ≤ mΩ)
    (h𝒦tr : ∀ j, 𝒦 ≤ aeSigma (coverSigmaM ℳ j A h) P) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens,
      Measurable[germSigma A h] g ∧
      (∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A ω)) ∧
      IsCondZeroBoundaryGFF P 𝒦 (fun ω => H \ A ω) (fun ω => h ω - g ω) := by
  have hhm := hh.measurable
  obtain ⟨M, g, hM, hMlim, hgm, hge⟩ := exists_germVersion hh hA hloc hAc
  refine ⟨g, hgm, ae_isHarmonicDistOn_germVersion hh hA hloc hAc hM hMlim hge, fun φ => ?_⟩
  obtain ⟨M₂, hM₂m, -, hM₂c, hM₂e⟩ := exists_condExp_germSigmaK hh hA hmk hAc h𝒦A h𝒦le h𝒦tr φ
  have hgle := germSigma_le hA hhm
  have hhi : Integrable (fun ω => h ω φ) P :=
    (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
  -- the two conditional means agree
  have hM₂M : M₂ =ᵐ[P] M φ := by
    have hM₂i : Integrable M₂ P := integrable_condExp.congr hM₂c.symm
    have e1 : P[M₂ | germSigma A h] = M₂ :=
      condExp_of_stronglyMeasurable hgle hM₂m.stronglyMeasurable hM₂i
    have e2 : P[M₂ | germSigma A h] =ᵐ[P] P[fun ω => h ω φ | germSigma A h] :=
      (condExp_congr_ae hM₂c).trans (condExp_condExp_of_le h𝒦A h𝒦le)
    rw [e1] at e2
    exact e2.trans (hM φ).2.1.symm
  have hgφ : Measurable[𝒦] fun ω => g ω φ :=
    (measurable_distOn_apply φ).comp (hgm.mono h𝒦A le_rfl)
  set W : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((-(g ω φ) : ℝ) : ℂ))
  have hWm : StronglyMeasurable[𝒦] W :=
    (@GFF.measurable_exp_I_mul Ω 𝒦 _ hgφ.neg).stronglyMeasurable
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := fun ω => (Complex.norm_exp_I_mul_ofReal _).le
  have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hhm)
  have hWF : Integrable (fun ω => W ω * Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    hF.bdd_mul (hWm.mono h𝒦le).aestronglyMeasurable (Eventually.of_forall hWb)
  have hpull := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hWm
    (by simpa [ContinuousLinearMap.mul_apply'] using hWF) hF
  have e : (fun ω => Complex.exp (Complex.I * (((h ω - g ω) φ : ℝ) : ℂ))) =
      fun ω => (ContinuousLinearMap.mul ℝ ℂ) (W ω) (Complex.exp (Complex.I * (h ω φ : ℂ))) := by
    funext ω
    simp only [W, ContinuousLinearMap.mul_apply', sub_apply, Complex.ofReal_sub,
      Complex.ofReal_neg, ← Complex.exp_add]
    congr 1; ring
  rw [e]
  filter_upwards [hpull, hM₂e, hge φ, hM₂M, hAc] with ω h1 h2 h3 h4 ⟨hsub, hopen⟩
  rw [h1, ContinuousLinearMap.mul_apply', ← h2]
  have hrc : relClosureH (A ω) = A ω := relClosureH_eq hsub hopen
  simp only [W, h3, ← h4, hrc, Complex.ofReal_neg, ← mul_assoc, ← Complex.exp_add, mul_neg,
    neg_add_cancel, Complex.exp_zero, one_mul]


/-- A marked union retains the pair and both individual germs in its Gaussian
kernel, without determination or conditional independence of either set. -/
theorem exists_condLaw_marked_union_germs (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A₁ A₂ : Ω → Set ℂ}
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hA₁c : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω))
    (hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hmarked : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma)
      (fun ω => A₁ ω ∪ A₂ ω) h P) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens,
      Measurable[germSigma (fun ω => A₁ ω ∪ A₂ ω) h] g ∧
      (∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ (A₁ ω ∪ A₂ ω))) ∧
      IsCondZeroBoundaryGFF P (germSigma (fun ω => A₁ ω ∪ A₂ ω) h ⊔
          (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
            (germSigma A₁ h ⊔ germSigma A₂ h))
        (fun ω => H \ (A₁ ω ∪ A₂ ω)) (fun ω => h ω - g ω) := by
  have hhm := hh.measurable
  have hA := measurable_union_hitting hA₁ hA₂
  have hAc : ∀ᵐ ω ∂P, (A₁ ω ∪ A₂ ω) ⊆ H ∧ IsOpen (H \ (A₁ ω ∪ A₂ ω)) := by
    filter_upwards [hA₁c, hA₂c] with ω ⟨hs₁, ho₁⟩ ⟨hs₂, ho₂⟩
    refine ⟨union_subset hs₁ hs₂, ?_⟩
    have he : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff]
      tauto
    rw [he]
    exact ho₁.inter ho₂
  have hmk := WholeField.isCoverMarking_history hh hA (sup_le hA₁.comap_le hA₂.comap_le) hmarked
  refine exists_condLaw_of_coverMarking hh hA hmarked.isAvoidanceLocal hAc hmk
    (le_sup_left.trans le_sup_left)
    (sup_le (sup_le (germSigma_le hA hhm) (sup_le hA₁.comap_le hA₂.comap_le))
      (sup_le (germSigma_le hA₁ hhm) (germSigma_le hA₂ hhm))) fun j => ?_
  refine sup_le (sup_le (fun G hG => germSigmaAt_le_aeSigmaM hh hmk.comap_le j G
    (measurableSet_germSigmaAt_coverRad hG j))
    ((le_sup_right.trans le_sup_left : _ ≤ coverSigmaM _ j _ h).trans (le_aeSigma _ P)))
    (sup_le ?_ ?_)
  · exact germSigma_le_aeSigma_of_subset hh hmk.comap_le
      (le_sup_left.trans le_sup_right) (fun ω => subset_union_left) j
  · exact germSigma_le_aeSigma_of_subset hh hmk.comap_le
      (le_sup_right.trans le_sup_right) (fun ω => subset_union_right) j

end InteractingSLE.Sec7.PocketStopSide

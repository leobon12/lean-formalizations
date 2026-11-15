/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxLoc
import InteractingSLE.Spec.Supplement.GW2SfMeanVersions
import InteractingSLE.Spec.Sec7.Lemma72EHit

/-!
# GW2's open lines: localization of local-set means between two mark systems

Packet PROVE-GW2-STAGEMEAN, R120 round. Under the conditional law of the earlier pieces two local sets of the launch
field are compared: the instance's union `L` (marked local for RELDET's marks `𝓜`, deterministic stage time `t`) and
the kernel union `U` (marked local for its own field-determined stopped marks `𝓝`, stage time `min t (T n)`). On a
mark event `I` of `𝓜` the kernel union lies in `L`, and on a mark event `G ⊆ I` of `𝓝` the two sets agree.

* `isHistoryAvoidanceLocal_cutoff`, `measurable_cutoff`: the cut-off `L` on `I`, `ℍ` off `I`, keeps the marked
  locality and the measurability for marks containing `I`;
* **`ae_localSetMean_eq_of_cutoff`**: then the local-set means of `L` and of `U` agree almost surely on `G`
  (the cut-off agrees with `L` on `I` — `GW2Sf.ae_mean_eq_on_marked_event` for `𝓜 ⊔ nulls`; it contains `U`, so it is
  marked local for `𝓝` — `GW2Omx.isHistoryAvoidanceLocal_of_subset`; it agrees with `U` on `G` —
  `GW2Sf.ae_mean_eq_on_marked_event` for `𝓝 ⊔ nulls`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open WholeField LocalSets

open Classical in
/-- **A cut-off of a marked local set on a mark event is marked local.** -/
theorem isHistoryAvoidanceLocal_cutoff {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {B : Ω → Set ℂ} {I : Set Ω}
    (hI : MeasurableSet[ℋ] I) (hloc : IsHistoryAvoidanceLocal ℋ B h P) :
    IsHistoryAvoidanceLocal ℋ (fun ω => if ω ∈ I then B ω else H) h P := by
  classical
  intro U G hUH hG hd F hF
  by_cases hU : (U : Set ℂ).Nonempty
  · have hHU : ¬ Disjoint H (U : Set ℂ) := by
      obtain ⟨z, hz⟩ := hU
      exact fun hdis => Set.disjoint_left.1 hdis (hUH hz) hz
    have e : {ω | Disjoint ((fun ω => if ω ∈ I then B ω else H) ω) (U : Set ℂ)} ∩ F =
        {ω | Disjoint (B ω) (U : Set ℂ)} ∩ (I ∩ F) := by
      ext ω
      by_cases hω : ω ∈ I
      · simp only [hω, ↓reduceIte, mem_inter_iff, mem_ofPred_eq, true_and]
      · simp only [hω, ↓reduceIte, mem_inter_iff, mem_ofPred_eq, hHU, false_and, and_false]
    rw [e]
    exact hloc U G hUH hG hd (I ∩ F) (hI.inter hF)
  · have hU0 : (U : Set ℂ) = ∅ := not_nonempty_iff_eq_empty.1 hU
    have e : {ω | Disjoint ((fun ω => if ω ∈ I then B ω else H) ω) (U : Set ℂ)} ∩ F =
        {ω | Disjoint (B ω) (U : Set ℂ)} ∩ F := by
      ext ω
      simp only [hU0, disjoint_empty, mem_inter_iff, mem_ofPred_eq, true_and]
    rw [e]
    exact hloc U G hUH hG hd F hF

open Classical in
/-- The cut-off is hitting-measurable for marks containing the cut-off event. -/
theorem measurable_cutoff {Ω : Type*} {ℋ : MeasurableSpace Ω} {B : Ω → Set ℂ} {I : Set Ω}
    (hI : MeasurableSet[ℋ] I) (hB : Measurable[ℋ, hittingSigma] B) :
    Measurable[ℋ, hittingSigma] (fun ω => if ω ∈ I then B ω else H) := by
  intro S hS
  have e : (fun ω => if ω ∈ I then B ω else H) ⁻¹' S = (I ∩ B ⁻¹' S) ∪ (Iᶜ ∩ {_ω | H ∈ S}) := by
    ext ω
    by_cases hω : ω ∈ I
    · simp [hω]
    · simp [hω]
  rw [e]
  refine (hI.inter (hB hS)).union (hI.compl.inter ?_)
  by_cases hHS : H ∈ S
  · simp only [hHS, ofPred_true]
    exact @MeasurableSet.univ _ ℋ
  · simp only [hHS, ofPred_false]
    exact @MeasurableSet.empty _ ℋ

/-- **Localization of local-set means between two mark systems.** -/
theorem ae_localSetMean_eq_of_cutoff {Ω : Type u} {𝓜 𝓝 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₀ ν) (h𝓜 : 𝓜 ≤ mΩ) (h𝓝 : 𝓝 ≤ mΩ)
    {L U : Ω → Set ℂ} (hLm : Measurable[𝓜, hittingSigma] L) (hLc : ∀ ω, L ω ⊆ H ∧ IsOpen (H \ L ω))
    (hLl : IsHistoryAvoidanceLocal 𝓜 L h₀ ν)
    (hUm : Measurable[𝓝, hittingSigma] U) (hUc : ∀ᵐ ω ∂ν, U ω ⊆ H ∧ IsOpen (H \ U ω))
    (hUl : IsHistoryAvoidanceLocal 𝓝 U h₀ ν)
    (hdet : 𝓝 ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) ν)
    {I : Set Ω} (hI : MeasurableSet[𝓜 ⊔ Ito.nullSets ν] I) (hsub : ∀ᵐ ω ∂ν, ω ∈ I → U ω ⊆ L ω)
    {G : Set Ω} (hG : MeasurableSet[𝓝] G) (heq : ∀ᵐ ω ∂ν, ω ∈ G → ω ∈ I ∧ U ω = L ω)
    {gL gU : Ω → DistOn upperHalfPlaneOpens} (hgL : IsLocalSetMean L h₀ ν gL)
    (hgU : IsLocalSetMean U h₀ ν gU) :
    ∀ᵐ ω ∂ν, ω ∈ G → gL ω = gU ω := by
  classical
  have hℋ : 𝓜 ⊔ Ito.nullSets ν ≤ mΩ := sup_le h𝓜 (Ito.nullSets_le ν)
  set L₂ : Ω → Set ℂ := fun ω => if ω ∈ I then L ω else H with hL₂
  have hLm' : Measurable[mΩ, hittingSigma] L := hLm.mono h𝓜 le_rfl
  have hL₂m : Measurable[𝓜 ⊔ Ito.nullSets ν, hittingSigma] L₂ := measurable_cutoff hI (hLm.mono le_sup_left le_rfl)
  have hL₂m' : Measurable[mΩ, hittingSigma] L₂ := hL₂m.mono hℋ le_rfl
  have hLlℋ : IsHistoryAvoidanceLocal (𝓜 ⊔ Ito.nullSets ν) L h₀ ν :=
    Sec7.Lemma72E.isHistoryAvoidanceLocal_sup_nullSets hLl
  have hL₂l : IsHistoryAvoidanceLocal (𝓜 ⊔ Ito.nullSets ν) L₂ h₀ ν := isHistoryAvoidanceLocal_cutoff hI hLlℋ
  have hL₂c : ∀ ω, L₂ ω ⊆ H ∧ IsOpen (H \ L₂ ω) := fun ω => by
    by_cases hω : ω ∈ I
    · simp only [hL₂, hω, ↓reduceIte]
      exact hLc ω
    · simp only [hL₂, hω, ↓reduceIte]
      exact ⟨subset_rfl, by rw [Set.sdiff_self]; exact isOpen_empty⟩
  have hL₂loc : IsLocalSet L₂ h₀ ν :=
    ((isLocalSet_tfae hh hL₂m' (Eventually.of_forall hL₂c)).out 4 1).2 hL₂l.isAvoidanceLocal
  obtain ⟨g₂, hg₂⟩ := IsLocalSet.exists_isLocalSetMean hh hL₂m' hL₂loc
  -- the cut-off has the mean of `L` on `I`
  have h1 := GW2Sf.ae_mean_eq_on_marked_event hh hℋ le_sup_right hLm' hL₂m'
    (Eventually.of_forall hLc) (Eventually.of_forall hL₂c) hLlℋ hL₂l hI
    (Eventually.of_forall fun ω hω => by simp only [hL₂, hω, ↓reduceIte]) hgL hg₂
  -- the cut-off contains `U`, hence is marked local for `𝓝`
  have hUL₂ : ∀ᵐ ω ∂ν, U ω ⊆ L₂ ω := by
    filter_upwards [hsub, hUc] with ω h1 h2
    by_cases hω : ω ∈ I
    · simp only [hL₂, hω, ↓reduceIte]
      exact h1 hω
    · simp only [hL₂, hω, ↓reduceIte]
      exact h2.1
  have hL₂𝓝 : IsHistoryAvoidanceLocal 𝓝 L₂ h₀ ν :=
    isHistoryAvoidanceLocal_of_subset hh.measurable hL₂m' hL₂l.isAvoidanceLocal
      (fun V hVH => hUm (measurableSet_avoid V.isOpen hVH)) hdet hUl hUL₂
  have hUm' : Measurable[mΩ, hittingSigma] U := hUm.mono h𝓝 le_rfl
  have h2 := GW2Sf.ae_mean_eq_on_marked_event hh (sup_le h𝓝 (Ito.nullSets_le ν)) le_sup_right hUm' hL₂m'
    hUc (Eventually.of_forall hL₂c) (Sec7.Lemma72E.isHistoryAvoidanceLocal_sup_nullSets hUl)
    (Sec7.Lemma72E.isHistoryAvoidanceLocal_sup_nullSets hL₂𝓝) (le_sup_left (a := 𝓝) G hG)
    (by
      filter_upwards [heq] with ω hω hωG
      obtain ⟨hωI, hUL⟩ := hω hωG
      simp only [hL₂, hωI, ↓reduceIte]
      exact hUL) hgU hg₂
  filter_upwards [h1, h2, heq] with ω h1ω h2ω hω hωG
  rw [h1ω (hω hωG).1, h2ω hωG]

end InteractingSLE.Theorem14.GW2Omx

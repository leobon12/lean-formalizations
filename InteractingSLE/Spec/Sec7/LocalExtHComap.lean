/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.Assembly11BCoord

/-!
# Pulling an evolution, its stops and its stopped σ-algebras back along a measure-preserving map

Packet PROVE-LOCEXT-H (Aux. lemma 54). The extension of Aux. lemma 54 lives on `Ω × C`, and its driving process is the
reference driving process read from the **second** factor. `Coupling.CompactTransfer` pulls an evolution back along
`Prod.fst` only; here the same statements are proved along an arbitrary measurable map `π : Ω' → Ω₀` with
`P'.map π = P₀` (`Coupling.filtrationComap`, `Coupling.IsIntegratedSLEEvolution.comap`):

* `ae_eq_of_preimage_comap`, `preimage_comap_ae_eq`: almost sure equality of events descends and pulls back;
* `measurableSet_usualAugmentation_comap`, `isStoppingTime_comap`: events of the usual augmentation and its stopping times
  pull back;
* `exists_comap_ae_eq_of_measurableSet_usualAugmentation`, `exists_comap_ae_eq_of_measurableSet_stopped`: every event of
  the usual augmentation of the pulled-back filtration (resp. of the stopped σ-algebra of a pulled-back stop) is almost
  surely the preimage of an event on `Ω₀`;
* `isSampledAt_comap`: the protected-kernel constraint `Coupling.IsSampledAt` on `Ω'` at a pulled-back stop follows from
  the constraint tested against preimages of events of `Ω₀` (the field on `Ω'` is arbitrary).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Coupling Ito

variable {Ω₀ Ω' : Type*} {mΩ₀ : MeasurableSpace Ω₀} [mΩ' : MeasurableSpace Ω'] {π : Ω' → Ω₀}
  {P₀ : Measure Ω₀} {μ : Measure Ω'}

/-- Almost sure equality of preimages descends along a map carrying `μ` to `P₀`. -/
theorem ae_eq_of_preimage_comap (hπ : Measurable π) (hμ : μ.map π = P₀) {C D : Set Ω₀}
    (hC : MeasurableSet C) (hD : MeasurableSet D) (h : π ⁻¹' C =ᵐ[μ] π ⁻¹' D) : C =ᵐ[P₀] D := by
  have hm : MeasurableSet {ω : Ω₀ | (ω ∈ C) = (ω ∈ D)} := by
    have : {ω : Ω₀ | (ω ∈ C) = (ω ∈ D)} = (C ∩ D) ∪ (Cᶜ ∩ Dᶜ) := by
      ext ω; by_cases h1 : ω ∈ C <;> by_cases h2 : ω ∈ D <;> simp [h1, h2]
    rw [this]; exact (hC.inter hD).union (hC.compl.inter hD.compl)
  rw [← hμ]
  exact (ae_map_iff hπ.aemeasurable hm).2 h

/-- Almost sure equality on `Ω₀` pulls back. -/
theorem preimage_comap_ae_eq (hπ : Measurable π) (hμ : μ.map π = P₀) {C D : Set Ω₀} (h : C =ᵐ[P₀] D) :
    π ⁻¹' C =ᵐ[μ] π ⁻¹' D := by
  rw [← hμ] at h
  exact ae_of_ae_map hπ.aemeasurable h

/-- **Pulled-back events of the usual augmentation.** -/
theorem measurableSet_usualAugmentation_comap (hπ : Measurable π) (hμ : μ.map π = P₀)
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {t : ℝ≥0} {E : Set Ω₀}
    (hE : MeasurableSet[usualAugmentation 𝓕₀ P₀ t] E) :
    MeasurableSet[usualAugmentation (filtrationComap 𝓕₀ hπ) μ t] (π ⁻¹' E) := by
  have hEm : MeasurableSet E := (usualAugmentation 𝓕₀ P₀).le t _ hE
  rw [usualAugmentation_apply] at hE ⊢
  simp only [MeasurableSpace.measurableSet_iInf] at hE ⊢
  intro u hu
  obtain ⟨C, hC, hEC⟩ := exists_ae_eq_of_measurableSet_nullAugmented (hE u hu)
  exact measurableSet_nullAugmented_of_ae_eq (hπ hEm)
    (MeasurableSpace.measurableSet_comap.2 ⟨C, hC, rfl⟩) (preimage_comap_ae_eq hπ hμ hEC)

/-- **Stopping times of the usual augmentation pull back.** -/
theorem isStoppingTime_comap (hπ : Measurable π) (hμ : μ.map π = P₀) {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {s : Ω₀ → WithTop ℝ≥0} (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) s) :
    IsStoppingTime (usualAugmentation (filtrationComap 𝓕₀ hπ) μ) fun p => s (π p) := fun t =>
  measurableSet_usualAugmentation_comap hπ hμ (hs t)

/-- **Events of the usual augmentation of the pulled-back filtration are a.s. pulled back.** -/
theorem exists_comap_ae_eq_of_measurableSet_usualAugmentation (hπ : Measurable π) (hμ : μ.map π = P₀)
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {t : ℝ≥0} {A : Set Ω'}
    (hA : MeasurableSet[usualAugmentation (filtrationComap 𝓕₀ hπ) μ t] A) :
    ∃ A₀ : Set Ω₀, MeasurableSet[usualAugmentation 𝓕₀ P₀ t] A₀ ∧ A =ᵐ[μ] π ⁻¹' A₀ := by
  set u : ℕ → ℝ≥0 := fun n => t + 1 / ((n : ℝ≥0) + 1) with hu
  have htu : ∀ n, t < u n := fun n => lt_add_of_pos_right _ (by positivity)
  have hC : ∀ n, ∃ C : Set Ω₀, MeasurableSet[𝓕₀ (u n)] C ∧ A =ᵐ[μ] π ⁻¹' C := fun n => by
    obtain ⟨A', hA', hAA'⟩ := exists_ae_eq_of_measurableSet_usualAugmentation (htu n) hA
    obtain ⟨C, hCm, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA'
    exact ⟨C, hCm, hAA'⟩
  choose C hCm hAC using hC
  have hCm' : ∀ n, MeasurableSet (C n) := fun n => 𝓕₀.le _ _ (hCm n)
  have hCC : ∀ n m, C n =ᵐ[P₀] C m := fun n m =>
    ae_eq_of_preimage_comap hπ hμ (hCm' n) (hCm' m) ((hAC n).symm.trans (hAC m))
  set A₀ := ⋂ n, C n with hA₀
  have hA₀m : MeasurableSet A₀ := MeasurableSet.iInter hCm'
  have hA₀C : ∀ m, A₀ =ᵐ[P₀] C m := fun m => by
    have := Filter.EventuallyEqSet.countable_iInter (fun n => hCC n m)
    simpa only [iInter_const] using this
  refine ⟨A₀, ?_, (hAC 0).trans (preimage_comap_ae_eq hπ hμ (hA₀C 0).symm)⟩
  rw [usualAugmentation_apply]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro v hv
  obtain ⟨m, hm⟩ : ∃ m : ℕ, u m ≤ v := by
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 (show (t : ℝ) < v from hv))
    refine ⟨m, ?_⟩
    rw [hu, ← NNReal.coe_le_coe, NNReal.coe_add]
    push_cast
    linarith
  exact measurableSet_nullAugmented_of_ae_eq hA₀m (𝓕₀.mono hm _ (hCm m)) (hA₀C m)

/-- **Events of the stopped σ-algebra of a pulled-back real stop are a.s. pulled back.** -/
theorem exists_comap_ae_eq_of_measurableSet_stopped (hπ : Measurable π) (hμ : μ.map π = P₀)
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0)) {A : Set Ω'}
    (hA : MeasurableSet[(isStoppingTime_comap hπ hμ hs).measurableSpace] A) :
    ∃ A₀ : Set Ω₀, MeasurableSet[hs.measurableSpace] A₀ ∧ A =ᵐ[μ] π ⁻¹' A₀ := by
  set 𝓖₀ := usualAugmentation 𝓕₀ P₀ with h𝓖₀
  rw [IsStoppingTime.measurableSet] at hA
  have hB : ∀ r : ℝ≥0, ∃ B : Set Ω₀, MeasurableSet[𝓖₀ r] B ∧
      A ∩ {p : Ω' | (s (π p) : WithTop ℝ≥0) ≤ r} =ᵐ[μ] π ⁻¹' (B ∩ {ω | s ω ≤ r}) :=
    fun r => by
      obtain ⟨B, hBm, hAB⟩ := exists_comap_ae_eq_of_measurableSet_usualAugmentation hπ hμ (hA.2 r)
      refine ⟨B, hBm, ?_⟩
      have e1 : A ∩ {p : Ω' | (s (π p) : WithTop ℝ≥0) ≤ r} =
          (A ∩ {p : Ω' | (s (π p) : WithTop ℝ≥0) ≤ r}) ∩ (π ⁻¹' {ω | s ω ≤ r}) := by
        ext p; simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, WithTop.coe_le_coe]; tauto
      rw [e1, preimage_inter]
      exact hAB.inter (EventuallyEq.refl _ _)
  choose B hBm hAB using hB
  have hsle : ∀ r : ℝ≥0, MeasurableSet[𝓖₀ r] {ω | s ω ≤ r} := fun r => by
    have := hs r
    simpa only [WithTop.coe_le_coe] using this
  set A₀ := ⋃ n : ℕ, (B n ∩ {ω | s ω ≤ n}) with hA₀
  have hA₀m : MeasurableSet A₀ :=
    MeasurableSet.iUnion fun n => 𝓖₀.le _ _ ((hBm n).inter (hsle n))
  have hAeq : A =ᵐ[μ] π ⁻¹' A₀ := by
    have e : A = ⋃ n : ℕ, (A ∩ {p : Ω' | (s (π p) : WithTop ℝ≥0) ≤ (n : ℝ≥0)}) := by
      ext p
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_ge (s (π p))
        exact ⟨n, h, hn⟩
      · rintro ⟨_, h, -⟩; exact h
    rw [e, hA₀, preimage_iUnion]
    exact Filter.EventuallyEqSet.countable_iUnion fun n => hAB n
  refine ⟨A₀, ?_, hAeq⟩
  rw [IsStoppingTime.measurableSet]
  refine ⟨?_, fun r => ?_⟩
  · exact MeasurableSet.iUnion fun n =>
      (le_iSup (fun t => 𝓖₀ t) (n : ℝ≥0)) _ ((hBm n).inter (hsle n))
  · have hsr : MeasurableSet {ω | s ω ≤ r} := 𝓖₀.le _ _ (hsle r)
    have hm : MeasurableSet (A₀ ∩ {ω | (s ω : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)}) := by
      simpa only [WithTop.coe_le_coe] using hA₀m.inter hsr
    have hBr : MeasurableSet (B r ∩ {ω | s ω ≤ r}) := 𝓖₀.le _ _ ((hBm r).inter (hsle r))
    have hae : A₀ ∩ {ω | (s ω : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)} =ᵐ[P₀] B r ∩ {ω | s ω ≤ r} := by
      refine ae_eq_of_preimage_comap hπ hμ hm hBr ?_
      have e : π ⁻¹' (A₀ ∩ {ω | (s ω : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)}) =
          π ⁻¹' A₀ ∩ {p : Ω' | (s (π p) : WithTop ℝ≥0) ≤ r} := rfl
      rw [e]
      exact (hAeq.symm.inter (EventuallyEq.refl _ _)).trans (hAB r)
    have h := measurableSet_nullAugmented_of_ae_eq (𝓕 := 𝓖₀) (P := P₀) hm
      ((hBm r).inter (hsle r)) hae
    rwa [nullAugmented_usualAugmentation] at h

/-- **The protected-kernel constraint at a pulled-back stop**, from the constraint tested against preimages of the
events of the stopped σ-algebra on `Ω₀`. The field `h` on `Ω'` is arbitrary. -/
theorem isSampledAt_comap (hπ : Measurable π) (hμ : μ.map π = P₀) {𝓕₀ : Filtration ℝ≥0 mΩ₀} {κ : ℝ}
    {W : ℝ≥0 → Ω₀ → ℝ} {u : Ω₀ → ℝ≥0 → ℂ → ℝ} {U : Set ℂ} {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    {h : Ω' → LQGMetric.DistOn upperHalfPlaneOpens}
    (hsamp : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U → ∀ A₀ : Set Ω₀,
      MeasurableSet[hs.measurableSpace] A₀ →
        ∫ p in π ⁻¹' A₀, Complex.exp (Complex.I * (h p ψ : ℂ)) ∂μ =
          ∫ p in π ⁻¹' A₀, cfAt κ W u ψ 1 s (π p) ∂μ) :
    IsSampledAt κ (fun t p => W t (π p)) (fun p => u (π p)) μ h U (isStoppingTime_comap hπ hμ hs) := by
  intro ψ hψ A hA
  obtain ⟨A₀, hA₀, hAA₀⟩ := exists_comap_ae_eq_of_measurableSet_stopped hπ hμ hs hA
  rw [setIntegral_congr_set hAA₀, setIntegral_congr_set hAA₀]
  exact hsamp ψ hψ A₀ hA₀

end LocalExt

end InteractingSLE

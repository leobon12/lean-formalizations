import InteractingSLE.Spec.Coupling.Assembly11
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# Transferring an evolution and its stopped σ-algebras to a coupling space `Ω₀ × X`

Packet PROVE-T11-ASM (Theorem 1.1, compactness step, Astra §1 p. 6). The limit coupling of the compactness step is a
probability measure `μ` on `Ω₀ × X` whose first marginal is the law `P₀` of the driving evolution on `Ω₀`. This file
pulls the evolution back along `Prod.fst`:

* `filtrationFst`: the filtration `𝓕₀ ∘ fst` on `Ω₀ × X`;
* `IsIntegratedSLEEvolution.fst`: the pulled-back processes form an integrated evolution under `μ`;
* `isStoppingTime_fst`: stopping times of the usual augmentation pull back to stopping times of the usual
  augmentation;
* `exists_fst_ae_eq_of_measurableSet_stopped`: every event of the stopped σ-algebra of a pulled-back stopping time
  (for the usual augmentation under `μ`) is `μ`-almost surely equal to the preimage of an event of the stopped
  σ-algebra on `Ω₀`;
* `isSampledAt_fst`: the protected-kernel constraint on `Ω₀ × X` follows from the constraint tested against preimages
  of events of `Ω₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω₀ X : Type*} {mΩ₀ : MeasurableSpace Ω₀} [mX : MeasurableSpace X]

/-- The filtration `𝓕₀ ∘ fst` on `Ω₀ × X`. -/
def filtrationFst (𝓕₀ : Filtration ℝ≥0 mΩ₀) (X : Type*) [MeasurableSpace X] :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω₀ × X)) where
  seq t := (𝓕₀ t).comap Prod.fst
  mono' _ _ hst := MeasurableSpace.comap_mono (𝓕₀.mono hst)
  le' t := (MeasurableSpace.comap_mono (𝓕₀.le t)).trans measurable_fst.comap_le

theorem filtrationFst_apply (𝓕₀ : Filtration ℝ≥0 mΩ₀) (t : ℝ≥0) :
    filtrationFst 𝓕₀ X t = (𝓕₀ t).comap Prod.fst := rfl

variable {P₀ : Measure Ω₀} {μ : Measure (Ω₀ × X)}

/-- Almost sure equality of preimages descends to the first marginal. -/
theorem ae_eq_of_preimage_fst (hμ : μ.map Prod.fst = P₀) {C D : Set Ω₀} (hC : MeasurableSet C)
    (hD : MeasurableSet D) (h : Prod.fst ⁻¹' C =ᵐ[μ] Prod.fst ⁻¹' D) : C =ᵐ[P₀] D := by
  have hm : MeasurableSet {ω : Ω₀ | (ω ∈ C) = (ω ∈ D)} := by
    have : {ω : Ω₀ | (ω ∈ C) = (ω ∈ D)} = (C ∩ D) ∪ (Cᶜ ∩ Dᶜ) := by
      ext ω; by_cases h1 : ω ∈ C <;> by_cases h2 : ω ∈ D <;> simp [h1, h2]
    rw [this]; exact (hC.inter hD).union (hC.compl.inter hD.compl)
  rw [← hμ]
  exact (ae_map_iff measurable_fst.aemeasurable hm).2 h

/-- Almost sure equality on `Ω₀` pulls back. -/
theorem preimage_fst_ae_eq (hμ : μ.map Prod.fst = P₀) {C D : Set Ω₀} (h : C =ᵐ[P₀] D) :
    Prod.fst ⁻¹' C =ᵐ[μ] Prod.fst ⁻¹' D := by
  rw [← hμ] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- A measurable set almost surely equal to an `𝓕_u`-set belongs to the null augmentation at `u`. -/
theorem measurableSet_nullAugmented_of_ae_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {u : ℝ≥0} {A C : Set Ω} (hA : MeasurableSet A)
    (hC : MeasurableSet[𝓕 u] C) (h : A =ᵐ[P] C) : MeasurableSet[nullAugmented 𝓕 P u] A := by
  have hCm : MeasurableSet C := 𝓕.le u _ hC
  have h1 : P (C \ A) = 0 := (ae_eq_set.1 h).2
  have h2 : P (A \ C) = 0 := (ae_eq_set.1 h).1
  have e : A = (C \ (C \ A)) ∪ (A \ C) := by
    ext ω; by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ C <;> simp [h1, h2]
  rw [e]
  exact ((le_nullAugmented 𝓕 P u _ hC).diff (measurableSet_nullAugmented_of_null
    (hCm.diff hA) h1 u)).union (measurableSet_nullAugmented_of_null (hA.diff hCm) h2 u)

/-- **Pulled-back events of the usual augmentation.** -/
theorem measurableSet_usualAugmentation_fst (hμ : μ.map Prod.fst = P₀) {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {t : ℝ≥0} {E : Set Ω₀} (hE : MeasurableSet[usualAugmentation 𝓕₀ P₀ t] E) :
    MeasurableSet[usualAugmentation (filtrationFst 𝓕₀ X) μ t] (Prod.fst ⁻¹' E) := by
  have hEm : MeasurableSet E := (usualAugmentation 𝓕₀ P₀).le t _ hE
  rw [usualAugmentation_apply] at hE ⊢
  simp only [MeasurableSpace.measurableSet_iInf] at hE ⊢
  intro u hu
  obtain ⟨C, hC, hEC⟩ := exists_ae_eq_of_measurableSet_nullAugmented (hE u hu)
  exact measurableSet_nullAugmented_of_ae_eq (measurable_fst hEm)
    (MeasurableSpace.measurableSet_comap.2 ⟨C, hC, rfl⟩) (preimage_fst_ae_eq hμ hEC)

/-- **Stopping times pull back.** -/
theorem isStoppingTime_fst (hμ : μ.map Prod.fst = P₀) {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {s : Ω₀ → ℝ≥0} (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0)) :
    IsStoppingTime (usualAugmentation (filtrationFst 𝓕₀ X) μ)
      fun p : Ω₀ × X => (s p.1 : WithTop ℝ≥0) := fun t =>
  measurableSet_usualAugmentation_fst hμ (hs t)

/-- **Events of the usual augmentation on `Ω₀ × X` are a.s. pulled back from `Ω₀`.** -/
theorem exists_fst_ae_eq_of_measurableSet_usualAugmentation (hμ : μ.map Prod.fst = P₀)
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {t : ℝ≥0} {A : Set (Ω₀ × X)}
    (hA : MeasurableSet[usualAugmentation (filtrationFst 𝓕₀ X) μ t] A) :
    ∃ A₀ : Set Ω₀, MeasurableSet[usualAugmentation 𝓕₀ P₀ t] A₀ ∧ A =ᵐ[μ] Prod.fst ⁻¹' A₀ := by
  set u : ℕ → ℝ≥0 := fun n => t + 1 / ((n : ℝ≥0) + 1) with hu
  have htu : ∀ n, t < u n := fun n => lt_add_of_pos_right _ (by positivity)
  have hC : ∀ n, ∃ C : Set Ω₀, MeasurableSet[𝓕₀ (u n)] C ∧ A =ᵐ[μ] Prod.fst ⁻¹' C := fun n => by
    obtain ⟨A', hA', hAA'⟩ := exists_ae_eq_of_measurableSet_usualAugmentation (htu n) hA
    obtain ⟨C, hCm, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA'
    exact ⟨C, hCm, hAA'⟩
  choose C hCm hAC using hC
  have hCm' : ∀ n, MeasurableSet (C n) := fun n => 𝓕₀.le _ _ (hCm n)
  have hCC : ∀ n m, C n =ᵐ[P₀] C m := fun n m =>
    ae_eq_of_preimage_fst hμ (hCm' n) (hCm' m) ((hAC n).symm.trans (hAC m))
  set A₀ := ⋂ n, C n with hA₀
  have hA₀m : MeasurableSet A₀ := MeasurableSet.iInter hCm'
  have hA₀C : ∀ m, A₀ =ᵐ[P₀] C m := fun m => by
    have := Filter.EventuallyEqSet.countable_iInter (fun n => hCC n m)
    simpa only [iInter_const] using this
  refine ⟨A₀, ?_, (hAC 0).trans (preimage_fst_ae_eq hμ (hA₀C 0).symm)⟩
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

/-- **Events of the stopped σ-algebra of a pulled-back stopping time are a.s. pulled back.** -/
theorem exists_fst_ae_eq_of_measurableSet_stopped (hμ : μ.map Prod.fst = P₀)
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0)) {A : Set (Ω₀ × X)}
    (hA : MeasurableSet[(isStoppingTime_fst (X := X) hμ hs).measurableSpace] A) :
    ∃ A₀ : Set Ω₀, MeasurableSet[hs.measurableSpace] A₀ ∧ A =ᵐ[μ] Prod.fst ⁻¹' A₀ := by
  set 𝓖₀ := usualAugmentation 𝓕₀ P₀ with h𝓖₀
  rw [IsStoppingTime.measurableSet] at hA
  have hB : ∀ r : ℝ≥0, ∃ B : Set Ω₀, MeasurableSet[𝓖₀ r] B ∧
      A ∩ {p : Ω₀ × X | (s p.1 : WithTop ℝ≥0) ≤ r} =ᵐ[μ] Prod.fst ⁻¹' (B ∩ {ω | s ω ≤ r}) :=
    fun r => by
      obtain ⟨B, hBm, hAB⟩ := exists_fst_ae_eq_of_measurableSet_usualAugmentation hμ (hA.2 r)
      refine ⟨B, hBm, ?_⟩
      have e1 : A ∩ {p : Ω₀ × X | (s p.1 : WithTop ℝ≥0) ≤ r} =
          (A ∩ {p : Ω₀ × X | (s p.1 : WithTop ℝ≥0) ≤ r}) ∩ (Prod.fst ⁻¹' {ω | s ω ≤ r}) := by
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
  have hAeq : A =ᵐ[μ] Prod.fst ⁻¹' A₀ := by
    have e : A = ⋃ n : ℕ, (A ∩ {p : Ω₀ × X | (s p.1 : WithTop ℝ≥0) ≤ (n : ℝ≥0)}) := by
      ext p
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_ge (s p.1)
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
      refine ae_eq_of_preimage_fst hμ hm hBr ?_
      have e : Prod.fst ⁻¹' (A₀ ∩ {ω | (s ω : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)}) =
          Prod.fst ⁻¹' A₀ ∩ {p : Ω₀ × X | (s p.1 : WithTop ℝ≥0) ≤ r} := rfl
      rw [e]
      exact (hAeq.symm.inter (EventuallyEq.refl _ _)).trans (hAB r)
    have h := measurableSet_nullAugmented_of_ae_eq (𝓕 := 𝓖₀) (P := P₀) hm
      ((hBm r).inter (hsle r)) hae
    rwa [nullAugmented_usualAugmentation] at h

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}

/-- **The evolution pulls back** to any coupling whose first marginal is its law. -/
theorem IsIntegratedSLEEvolution.fst (hμ : μ.map Prod.fst = P₀) {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR μ (filtrationFst 𝓕₀ X) (fun t p => W t p.1)
      (fun i t p => VL i t p.1) (fun i t p => VR i t p.1) (fun t p => B t p.1)
      (fun p => ζ p.1) := by
  obtain ⟨⟨hBB, hBa, hBi⟩, hWa, hVLa, hVRa, hpath⟩ := hE
  have hlaw : HasLaw Prod.fst P₀ μ := ⟨measurable_fst.aemeasurable, hμ⟩
  have hBm : ∀ t, Measurable (B t) := fun t => (hBa t).mono (𝓕₀.le t) le_rfl
  refine ⟨⟨⟨⟨fun I => (hBB.hasLaw I).comp hlaw⟩, ?_⟩, fun t => ?_, fun s t hst => ?_⟩,
    fun t A hA => ?_, fun i t A hA => ?_, fun i t A hA => ?_, ?_⟩
  · rw [← hμ] at hBB
    exact ae_of_ae_map measurable_fst.aemeasurable hBB.cont
  · exact @Measurable.comp _ _ _ ((𝓕₀ t).comap Prod.fst) (𝓕₀ t) _ _ _ (hBa t)
      (comap_measurable Prod.fst)
  · rw [Indep_iff]
    intro t1 t2 ht1 ht2
    obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht1
    obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht2
    have hS' : MeasurableSet ((fun ω => B t ω - B s ω) ⁻¹' S) := ((hBm t).sub (hBm s)) hS
    have hT' : MeasurableSet T := 𝓕₀.le s _ hT
    have hind := (Indep_iff _ _ _).1 (hBi s t hst) _ T
      (MeasurableSpace.measurableSet_comap.2 ⟨S, hS, rfl⟩) hT
    have e : (fun p : Ω₀ × X => B t p.1 - B s p.1) ⁻¹' S =
        Prod.fst ⁻¹' ((fun ω => B t ω - B s ω) ⁻¹' S) := rfl
    rw [e, ← preimage_inter, ← Measure.map_apply measurable_fst (hS'.inter hT'),
      ← Measure.map_apply measurable_fst hS', ← Measure.map_apply measurable_fst hT', hμ]
    exact hind
  · exact MeasurableSpace.measurableSet_comap.2 ⟨_, hWa t A hA, rfl⟩
  · exact MeasurableSpace.measurableSet_comap.2 ⟨_, hVLa i t A hA, rfl⟩
  · exact MeasurableSpace.measurableSet_comap.2 ⟨_, hVRa i t A hA, rfl⟩
  · rw [← hμ] at hpath
    exact ae_of_ae_map measurable_fst.aemeasurable hpath

/-- **The protected-kernel constraint on `Ω₀ × X`**, from the constraint tested against preimages of the events of
the stopped σ-algebra on `Ω₀`. -/
theorem isSampledAt_fst (hμ : μ.map Prod.fst = P₀) {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {u : Ω₀ → ℝ≥0 → ℂ → ℝ} {U : Set ℂ} {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    {h : Ω₀ × X → LQGMetric.DistOn upperHalfPlaneOpens}
    (hsamp : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U → ∀ A₀ : Set Ω₀,
      MeasurableSet[hs.measurableSpace] A₀ →
        ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (h p ψ : ℂ)) ∂μ =
          ∫ p in Prod.fst ⁻¹' A₀, cfAt κ W u ψ 1 s p.1 ∂μ) :
    IsSampledAt κ (fun t p => W t p.1) (fun p => u p.1) μ h U (isStoppingTime_fst (X := X) hμ hs) := by
  intro ψ hψ A hA
  obtain ⟨A₀, hA₀, hAA₀⟩ := exists_fst_ae_eq_of_measurableSet_stopped hμ hs hA
  rw [setIntegral_congr_set hAA₀, setIntegral_congr_set hAA₀]
  exact hsamp ψ hψ A₀ hA₀

end Coupling

end InteractingSLE

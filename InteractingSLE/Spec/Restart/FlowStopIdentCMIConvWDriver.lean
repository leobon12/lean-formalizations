/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWThreshold
import InteractingSLE.Spec.Restart.RetPlumbProofResidualDriver

/-! # A continuous adapted driver from an announced measurable exit version -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- Regularize the landed pathwise stopped driver on a measurable conull event,
then use the existing adapted stopped reader. No completion of the ambient space is assumed. -/
theorem exists_adapted_driver_of_announced_exit {e : S → ℝ≥0∞}
    (he : e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω))
    (hest : IsStoppingTime D.driving fun ω => (e ω : WithTop ℝ≥0))
    {T : ℕ → S → ℝ≥0} (hT : Coupling.IsAnnouncingSeq D.driving D.Q₀ e T) :
    ∃ W : ℝ≥0 → S → ℝ, (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous (W · ω)) ∧
      StronglyAdapted D.driving W ∧
      ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω := by
  classical
  let _ := D.Q₀_prob
  obtain ⟨W₁, hp⟩ := cmiStopDataStatement D.κ D.κ_pos D.b D.J D.b_pc D.N D.N_open D.V D.V_open
    D.V_bounded D.closureV_subset D.a D.c D.closureV_real D.hull_subset D.y D.θ D.Q₀ D.Γ D.U
    D.h' D.filt D.W₀ D.VL₀ D.VR₀ D.B₀ D.coupling D.trace D.killed
  have hn := fun n => hp (fun ω => (T n ω : WithTop ℝ≥0)) (hT.1 n) (by
    filter_upwards [hT.2.2.1 n, he] with ω ht heω
    exact heω ▸ ht)
  let good : S → Prop := fun ω => Continuous (W₁ · ω) ∧ W₁ 0 ω = 0 ∧ e ω ≤ D.U ω ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W₁ t ω = D.W₀ t ω
  have hgood : ∀ᵐ ω ∂D.Q₀, good ω := by
    filter_upwards [ae_all_iff.2 hn, hT.2.2.2, he] with ω hω hcover heω
    refine ⟨(hω 0).1, (hω 0).2.1, heω ▸ min_le_left _ _, fun t ht => ?_⟩
    obtain ⟨n, htn⟩ := hcover t ht
    obtain ⟨t₂, ht₂, hag⟩ := (hω n).2.2.1
    simpa only [Ito.rpath, Real.toNNReal_coe] using
      hag t ⟨t.coe_nonneg, (NNReal.coe_le_coe.2 htn).trans ht₂.le⟩
  let G : Set S := (toMeasurable D.Q₀ {ω | ¬ good ω})ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGnull : D.Q₀ Gᶜ = 0 := by
    change D.Q₀ ((toMeasurable D.Q₀ {ω | ¬ good ω})ᶜ)ᶜ = 0
    rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hGgood : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[D.driving 0] G :=
    LocalExt.measurableSet_drivingFiltration_zero_of_null_compl D.killed hGm hGnull
  have hGae : ∀ᵐ ω ∂D.Q₀, ω ∈ G := ae_iff.2 hGnull
  let Y : ℝ≥0 → S → ℝ := fun t ω => if ω ∈ G then W₁ t ω else 0
  have hYc : ∀ ω, Continuous (Y · ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [Y, hω, ↓reduceIte] using (hGgood ω hω).1
    · simpa only [Y, hω, ↓reduceIte] using (continuous_const : Continuous fun _ : ℝ≥0 => (0 : ℝ))
  have hY0 : ∀ ω, Y 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [Y, hω, ↓reduceIte] using (hGgood ω hω).2.1
    · simp only [Y, hω, ↓reduceIte]
  have hWa : AdaptedBefore D.driving D.U D.W₀ := Ito.adaptedBefore_mono
    (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W D.killed)
  have hYa : AdaptedBefore D.driving e Y := by
    intro t A hA
    have hGt : MeasurableSet[D.driving t] G := D.driving.mono (show 0 ≤ t from bot_le) _ hG0
    have het : MeasurableSet[D.driving t] {ω | (t : ℝ≥0∞) < e ω} := by
      have ha : AdaptedBefore D.driving e (fun _ _ => (0 : ℝ)) :=
        MartChar.adaptedBefore_of_stronglyAdapted hest (fun _ => stronglyMeasurable_const)
      simpa only [mem_univ, and_true] using ha t univ MeasurableSet.univ
    have hsets : {ω | (t : ℝ≥0∞) < e ω ∧ Y t ω ∈ A} =
        (G ∩ {ω | (t : ℝ≥0∞) < e ω} ∩ {ω | (t : ℝ≥0∞) < D.U ω ∧ D.W₀ t ω ∈ A}) ∪
        (Gᶜ ∩ {ω | (t : ℝ≥0∞) < e ω} ∩ {ω | (0 : ℝ) ∈ A}) := by
      ext ω
      by_cases hω : ω ∈ G
      · have hg := hGgood ω hω
        simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, hω, not_true_eq_false,
          true_and, false_and, or_false, Y, ↓reduceIte]
        constructor
        · rintro ⟨ht, hAω⟩
          exact ⟨ht, ht.trans_le hg.2.2.1, hg.2.2.2 t ht ▸ hAω⟩
        · rintro ⟨ht, -, hAω⟩
          exact ⟨ht, (hg.2.2.2 t ht).symm ▸ hAω⟩
      · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, hω, not_false_eq_true,
          false_and, true_and, false_or, Y, ↓reduceIte]
    rw [hsets]
    exact ((hGt.inter het).inter (hWa t A hA)).union
      ((hGt.compl.inter het).inter (MeasurableSet.const _))
  obtain ⟨W, hW0, hWc, hWad, hWY⟩ := RetAux79.exists_continuous_adapted_stopped hYc hY0 hYa
  refine ⟨W, hW0, hWc, hWad, ?_⟩
  filter_upwards [hGae] with ω hω t ht
  rw [hWY ω t ht]
  exact (ite_eq_left hω).trans ((hGgood ω hω).2.2.2 t ht)

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI

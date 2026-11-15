/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45ClockSource
import InteractingSLE.Spec.Restart.FlowStopIdentLLCont

/-! # A continuous adapted driver through the general window exit -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open Restart Sec7
namespace ClockSource
variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- Extend the actual driver through a positive stopped window.
`hU_leftLimit` is the exact remaining deterministic endpoint input: only the
actual source lifetime needs a new limit theorem; interior window exits use
ordinary continuity. It is independent of any reference force word. -/
theorem exists_adapted_driver {e : S → ℝ≥0∞}
    (heU : ∀ ω, e ω ≤ D.U ω)
    (hest : IsStoppingTime D.driving fun ω => (e ω : WithTop ℝ≥0))
    (hpos : ∀ᵐ ω ∂D.P, 0 < e ω)
    (hU_leftLimit : ∀ᵐ ω ∂D.P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = D.U ω →
      ∃ c : ℝ, Tendsto (D.W₀ · ω) (𝓝[<] T) (𝓝 c)) :
    ∃ W : ℝ≥0 → S → ℝ, (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous (W · ω)) ∧
      StronglyAdapted D.driving W ∧
      ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω := by
  classical
  let W₁ : ℝ≥0 → S → ℝ := LocalExt.stopVal D.W₀ (fun ω => (e ω : WithTop ℝ≥0))
  let good : S → Prop := fun ω => Continuous (W₁ · ω) ∧ W₁ 0 ω = 0 ∧ e ω ≤ D.U ω ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W₁ t ω = D.W₀ t ω
  have hgood : ∀ᵐ ω ∂D.P, good ω := by
    filter_upwards [D.regular, hU_leftLimit, hpos] with ω hp hlim hepos
    have hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W₁ t ω = D.W₀ t ω :=
      fun t ht => FlowStopIdentLL.stopVal_of_lt (ζ := e) ht
    refine ⟨?_, (hag 0 hepos).trans hp.2, heU ω, hag⟩
    rcases eq_top_or_lt_top (e ω) with htop | hfin
    · have hU : D.U ω = ⊤ := top_le_iff.1 (htop ▸ heU ω)
      have heq : (W₁ · ω) = (D.W₀ · ω) := funext fun t => hag t (by
        rw [htop]; exact ENNReal.coe_lt_top)
      rw [heq]
      exact continuousOn_univ.1 (hp.1.mono fun t _ => by
        show (t : ℝ≥0∞) < D.U ω
        rw [hU]; exact ENNReal.coe_lt_top)
    · let T : ℝ≥0 := (e ω).toNNReal
      have hT : (T : ℝ≥0∞) = e ω := ENNReal.coe_toNNReal hfin.ne
      have hT0 : 0 < T := ENNReal.coe_pos.1 (hT.symm ▸ hepos)
      have hc : ContinuousOn (D.W₀ · ω) (Iio T) := hp.1.mono fun s hs =>
        (by rw [← hT]; exact ENNReal.coe_lt_coe.2 hs : (s : ℝ≥0∞) < e ω).trans_le (heU ω)
      obtain ⟨c, hlimT⟩ : ∃ c : ℝ, Tendsto (D.W₀ · ω) (𝓝[<] T) (𝓝 c) := by
        rcases (heU ω).lt_or_eq with hlt | heq
        · have hTU : (T : ℝ≥0∞) < D.U ω := hT ▸ hlt
          refine ⟨D.W₀ T ω, ?_⟩
          have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < D.U ω} :=
            isOpen_lt ENNReal.continuous_coe continuous_const
          exact ((hp.1 T hTU).continuousAt (hopen.mem_nhds hTU)).tendsto.mono_left nhdsWithin_le_nhds
        · exact hlim T hT0 (hT.trans heq)
      exact FlowStopIdentLL.continuous_stopVal_of_tendsto hT0 hT.symm hc hlimT
  let G : Set S := (toMeasurable D.P {ω | ¬ good ω})ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGnull : D.P Gᶜ = 0 := by
    change D.P ((toMeasurable D.P {ω | ¬ good ω})ᶜ)ᶜ = 0
    rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hgood
  have hGgood : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[D.driving 0] G :=
    LocalExt.measurableSet_drivingFiltration_zero_of_null_compl D.killed hGm hGnull
  have hGae : ∀ᵐ ω ∂D.P, ω ∈ G := ae_iff.2 hGnull
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

end ClockSource
end InteractingSLE.Sec5.Aux61R45

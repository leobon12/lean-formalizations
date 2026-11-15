/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ImgChartConstFwd
import InteractingSLE.Spec.Sec7.Lemma71MMeas

/-!
# The fixed-image-time chart clause, step R5's measurability: the candidate is known at the image time

Packet PROVE-WW-B19, step R5 of PROVE-WW-B18's plan. At a fixed image time `r`, the validity event of the chart
clause (`r < imgT`, `supp φ ⊆ Ψ⁻¹(ℍ \ K̃_r)`) is in the **raw** filtration `imgRaw r` of the image word, and so are the
chart mean and the chart variance on it (Lemma 7.1's `measurable_chartAvoid` with `𝓐 = imgRaw`, `𝓐₀ = imgRaw 0`):

* raw versions of PROVE-WW-B18's chart measurability (`measurableSet_mem_dom_imgChart_raw`,
  `measurable_indicator_fwd_imgChart_raw`, `measurable_indicator_lift_imgChart_raw`) and the closed-ball domain events
  `measurableSet_closedBall_subset_dom_imgChart_raw`;
* `adaptedBefore_imgW_raw`, `adaptedBefore_imgVL_raw`, `adaptedBefore_imgVR_raw`: the killed image word is adapted to
  `imgRaw` before `imgT` (its values are generators);
* **`measurable_imgChartAvoid_raw`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique

section Raw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℚ} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

/-- The reverse history stopped at `s` is known at time `0` of the raw filtration. -/
theorem measurable_revStop_imgRaw (r : ℝ≥0) :
    Measurable[imgRaw s ζ W E r] fun p : Ω × HistorySpace 1 1 => revStop s p.2 := fun B hB =>
  measurableSet_imgRaw_of_gen ⟨0, zero_le, Or.inr (Or.inr (Or.inr ⟨B, hB, rfl⟩))⟩
    ((measurable_revStop s).comp measurable_snd hB)

theorem measurable_revProc_imgRaw (t : ℝ≥0) :
    Measurable[imgRaw s ζ W E 0] (revProc s t : Ω × HistorySpace 1 1 → ℝ) := by
  have hF : Measurable fun y' : HistorySpace 1 1 =>
      Ito.rpath (Sec4.regPath y') (t : ℝ) - Ito.rpath (Sec4.regPath y') 0 :=
    (Sec4.measurable_regPath_apply _).sub (Sec4.measurable_regPath_apply _)
  exact hF.comp (measurable_revStop_imgRaw (s := s) (ζ := ζ) (W := W) (E := E) 0)

/-- The constant filtration at the time-zero σ-algebra of `imgRaw`. -/
abbrev imgRaw0 (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 1 1)) :=
  Filtration.const ℝ≥0 (imgRaw s ζ W E 0) ((imgRaw s ζ W E).le 0)

theorem adapted_revProc_imgRaw0 : Adapted (imgRaw0 s ζ W E) (revProc s : ℝ≥0 → Ω × HistorySpace 1 1 → ℝ) :=
  fun t => measurable_revProc_imgRaw t

/-- **The domain events of the chart are known at time `0` of `imgRaw`.** -/
theorem measurableSet_mem_dom_imgChart_raw (hs : 0 < s) (z : ℂ) :
    MeasurableSet[imgRaw s ζ W E 0] {p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom} := by
  by_cases hz : z ∈ H
  · rw [setOf_mem_dom_imgChart hs hz]
    exact Chart.measurableSet_mem_dom_loewnerChartAt (𝓖 := imgRaw0 s ζ W E) adapted_revProc_imgRaw0
      continuous_revProc revProc_zero _ _
  · rw [setOf_mem_dom_imgChart_of_notMem hs hz]
    exact @MeasurableSet.empty _ (imgRaw s ζ W E 0)

/-- **The forward map of the chart is known at time `0` of `imgRaw`** (on its domain). -/
theorem measurable_indicator_fwd_imgChart_raw (hs : 0 < s) (z : ℂ) :
    Measurable[imgRaw s ζ W E 0]
      ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).1 z) := by
  classical
  by_cases hz : z ∈ H
  · have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
    have h := Chart.measurable_indicator_fwd_loewnerChartAt (𝓖 := imgRaw0 s ζ W E) adapted_revProc_imgRaw0
      continuous_revProc revProc_zero (s : ℝ).toNNReal (negInv z)
    have e : ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).1 z) =
        negInv ∘ ({p | negInv z ∈ (Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p).dom}.indicator
          fun p => (Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p).1 (negInv z)) := by
      rw [setOf_mem_dom_imgChart hs hz]
      funext p
      by_cases hp : p ∈ {p | negInv z ∈ (Chart.loewnerChartAt (revProc s) (s : ℝ).toNNReal p).dom}
      · rw [indicator_of_mem hp, Function.comp_apply, indicator_of_mem hp]
        simp only [imgChart, revChart, Chart.loewnerChartAt, Chart.loewner, Chart.id, rpath_revProc,
          Real.coe_toNNReal _ hs']
      · rw [indicator_of_notMem hp, Function.comp_apply, indicator_of_notMem hp]
        simp [negInv]
    rw [e]
    exact measurable_negInv.comp h
  · rw [setOf_mem_dom_imgChart_of_notMem hs hz, indicator_empty]
    exact measurable_const

/-- The lift of the chart (`0`) is known at time `0` of `imgRaw`. -/
theorem measurable_indicator_lift_imgChart_raw (z : ℂ) :
    Measurable[imgRaw s ζ W E 0]
      ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).2.2 z) := by
  have e : ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).2.2 z) =
      fun _ => 0 := by
    funext p
    simp [imgChart]
  rw [e]
  exact measurable_const

/-- **The closed-ball domain events of the chart are known at time `0` of `imgRaw`.** -/
theorem measurableSet_closedBall_subset_dom_imgChart_raw (hs : 0 < s) (z : ℂ) (ρ : ℝ) :
    MeasurableSet[imgRaw s ζ W E 0]
      {p : Ω × HistorySpace 1 1 | closedBall z ρ ⊆ ((imgChart s p.2).dom : Set ℂ)} := by
  classical
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  by_cases hB : closedBall z ρ ⊆ H
  · have hQ : IsCompact (negInv '' closedBall z ρ) := by
      refine (isCompact_closedBall z ρ).image_of_continuousOn fun w hw => ?_
      exact (continuousAt_negInv (ne_zero_of_mem_H (hB hw))).continuousWithinAt
    have hWa : AdaptedBefore (imgRaw0 s ζ W E) (fun _ => (⊤ : ℝ≥0∞)) (revProc s) := by
      intro t A hA
      have e : {p : Ω × HistorySpace 1 1 | (t : ℝ≥0∞) < ⊤ ∧ revProc s t p ∈ A} = revProc s t ⁻¹' A := by
        ext p
        simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_lt_top, true_and]
      rw [e]
      exact measurable_revProc_imgRaw t hA
    have hc : ∀ p : Ω × HistorySpace 1 1, ContinuousOn (fun t => revProc s t p)
        {t : ℝ≥0 | (t : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) p} := fun p => (continuous_revProc p).continuousOn
    have h := Sec7.Lemma71M.measurableSet_lt_subset_H_diff_fwdHull hWa hc (s : ℝ).toNNReal hQ
    have e : {p : Ω × HistorySpace 1 1 | closedBall z ρ ⊆ ((imgChart s p.2).dom : Set ℂ)} =
        {p | ((s : ℝ).toNNReal : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) p ∧ negInv '' closedBall z ρ ⊆
          H \ fwdHull (fun t : ℝ => revProc s t.toNNReal p) ((s : ℝ).toNNReal : ℝ)} := by
      ext p
      have hrp : (fun t : ℝ => revProc s t.toNNReal p) = revDrv0 s p.2 := rpath_revProc p
      simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, hrp, Real.coe_toNNReal _ hs']
      constructor
      · rintro hsub _ ⟨w, hw, rfl⟩
        obtain ⟨hwH, hwK⟩ := (mem_dom_imgChart_iff hs p.2).1 (hsub hw)
        exact ⟨negInv_mem_H hwH, hwK⟩
      · intro hsub w hw
        refine (mem_dom_imgChart_iff hs p.2).2 ⟨hB hw, (hsub ⟨w, hw, rfl⟩).2⟩
    rw [e]
    exact h
  · have e : {p : Ω × HistorySpace 1 1 | closedBall z ρ ⊆ ((imgChart s p.2).dom : Set ℂ)} = ∅ := by
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hsub
      exact hB fun w hw => ((mem_dom_imgChart_iff hs p.2).1 (hsub hw)).1
    rw [e]
    exact @MeasurableSet.empty _ (imgRaw s ζ W E 0)

/-! ### The image word is adapted to `imgRaw` before `imgT` -/

theorem adaptedBefore_imgW_raw (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) :
    AdaptedBefore (imgRaw s ζ W E) (fun p => (imgT s ζ W E p : ℝ≥0∞)) (imgW s ζ W E) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 1 1 | (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) ∧ imgW s ζ W E t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} ∩ imgW s ζ W E t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_imgT hs hW hE hEg t)).inter
    (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inl rfl⟩⟩ (measurable_imgW hs hW hE hEg t hA))

theorem adaptedBefore_imgVL_raw (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (i : Fin 2) :
    AdaptedBefore (imgRaw s ζ W E) (fun p => (imgT s ζ W E p : ℝ≥0∞)) (imgVL s ζ W E i) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 1 1 | (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) ∧ imgVL s ζ W E i t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} ∩ imgVL s ζ W E i t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_imgT hs hW hE hEg t)).inter
    (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩
      (measurable_imgVL hs hW hE hEg i t hA))

theorem adaptedBefore_imgVR_raw (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (j : Fin 2) :
    AdaptedBefore (imgRaw s ζ W E) (fun p => (imgT s ζ W E p : ℝ≥0∞)) (imgVR s ζ W E j) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 1 1 | (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) ∧ imgVR s ζ W E j t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} ∩ imgVR s ζ W E j t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_imgT hs hW hE hEg t)).inter
    (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inr (Or.inr ⟨j, rfl⟩)⟩⟩
      (measurable_imgVR hs hW hE hEg j t hA))

/-- **R5's measurability: the chart clause's validity event at a fixed image time is in `imgRaw r`, and so are the
chart mean and the chart variance on it.** -/
theorem measurable_imgChartAvoid_raw (rL rR : ℝ) (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[imgRaw s ζ W E r] {p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r} ∧
      Measurable[imgRaw s ζ W E r] ({p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r}.indicator fun p =>
          Sec7.Lemma71D.chartMean 4 (imgρ rL) (imgρ rR) (fun t => imgW s ζ W E t p)
            (fun i t => imgVL s ζ W E i t p) (fun j t => imgVR s ζ W E j t p) (imgChart s p.2) 0 0 φ r) ∧
      Measurable[imgRaw s ζ W E r] ({p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r}.indicator fun p =>
          Sec7.Lemma71D.chartVar (fun t => imgW s ζ W E t p) (imgChart s p.2) φ r) := by
  have hkw := isKilledWord_img (ζ := ζ) (W := W) hs hEg
  exact Sec7.Lemma71M.measurable_chartAvoid 4 (imgρ rL) (imgρ rR) 0 0 (adaptedBefore_imgW_raw hs hW hE hEg)
    (fun p => hkw.contW p) (adaptedBefore_imgVL_raw hs hW hE hEg) (adaptedBefore_imgVR_raw hs hW hE hEg) r
    ((imgRaw s ζ W E).mono (zero_le (a := r))) (fun p => (imgChart s p.2).dom.isOpen)
    (measurableSet_closedBall_subset_dom_imgChart_raw hs) (fun p => isConformal_imgChart hs p.2) (fun _ => rfl)
    (measurable_indicator_fwd_imgChart_raw hs) measurable_indicator_lift_imgChart_raw
    (fun p => continuousOn_lift_imgChart p.2) φ

end Raw

end InteractingSLE.WangWu

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkClock7Inverse

/-!
# The stopped inverse-clock filtration for a local evolution

Measurability of stopped original clocks gives inverse-clock stopping times.
Clock images of original stops are then stopping times of that filtration.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Clock7

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
  {a : ℝ} {G : Set Ω} {W V : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0}

variable (ha : 0 < a) (hG : MeasurableSet[𝓕 0] G)
  (hA : ∀ n, IsStoppingTime 𝓕 fun ω => (A n ω : WithTop ℝ≥0))
  (hs : ∀ ω ∈ G, SepUpTo (W · ω) (V · ω) (T ω))
  (hb : ∀ ω ∈ G, ∀ n, (A n ω : ℝ≥0∞) < T ω)
  (hc : ∀ ω ∈ G, ∀ s : ℝ≥0, (s : ℝ≥0∞) < T ω → ∃ n, s ≤ A n ω)
  (hm : ∀ n r, Measurable[𝓕 r] fun ω => if ω ∈ G then
    clk (rate a (W · ω) (V · ω)) (min r (A n ω)) else 0)

include ha hG hA hs hb hc hm

/-- The inverse clock is a stopping time from measurability of stopped original clocks. -/
theorem isStoppingTime_inverseTime (u : ℝ≥0) : IsStoppingTime 𝓕 (inverseTime G a W V T u) := by
  intro r
  have hGr := 𝓕.mono (show (0 : ℝ≥0) ≤ r from zero_le) _ hG
  have hAm : ∀ n, MeasurableSet[𝓕 r] {ω | A n ω ≤ r} := fun n => by
    simpa only [WithTop.coe_le_coe] using hA n r
  have he : {ω | inverseTime G a W V T u ω ≤ r} = Gᶜ ∪ (G ∩
      ((⋂ n, {ω | A n ω ≤ r}) ∪ ⋃ n, {ω | (u : ℝ) ≤
        if ω ∈ G then clk (rate a (W · ω) (V · ω)) (min r (A n ω)) else 0})) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_union, mem_compl_iff, hω, not_true_eq_false, false_or, mem_inter_iff,
        true_and, mem_iInter, mem_iUnion, mem_ofPred_eq, ↓reduceIte]
      rw [inverseTime_le_iff hω ha (hs ω hω) (hb ω hω) (hc ω hω),
        horizon_le_iff (hb ω hω) (hc ω hω)]
    · simp only [mem_ofPred_eq, inverseTime, hω, ↓reduceIte, mem_union, mem_compl_iff,
        not_false_eq_true, true_or, iff_true]
      exact zero_le
  rw [he]
  exact hGr.compl.union (hGr.inter ((MeasurableSet.iInter hAm).union
    (MeasurableSet.iUnion fun n => measurableSet_le measurable_const (hm n r))))

/-- The original filtration read at the stopped inverse capacity clock. -/
def imageFiltration : Filtration ℝ≥0 mΩ :=
  timeChangeFilt 𝓕 (isStoppingTime_inverseTime ha hG hA hs hb hc hm) (inverseTime_mono ha hs)

/-- Clock images of the original finite stops, set to zero off the good event. -/
def imageStop (n : ℕ) (ω : Ω) : ℝ≥0 :=
  if ω ∈ G then (clk (rate a (W · ω) (V · ω)) (A n ω)).toNNReal else 0

/-- Every image stop is a stopping time in the actual inverse-clock filtration. -/
theorem isStoppingTime_imageStop (n : ℕ) :
    IsStoppingTime (imageFiltration ha hG hA hs hb hc hm)
      fun ω => (imageStop (a := a) (G := G) (W := W) (V := V) (A := A) n ω : WithTop ℝ≥0) := by
  have hcut : IsStoppingTime 𝓕 fun ω => if ω ∈ G then (A n ω : WithTop ℝ≥0) else 0 := by
    intro r
    have hGr := 𝓕.mono (show (0 : ℝ≥0) ≤ r from zero_le) _ hG
    have he : {ω | (if ω ∈ G then (A n ω : WithTop ℝ≥0) else 0) ≤ r} =
        Gᶜ ∪ (G ∩ {ω | (A n ω : WithTop ℝ≥0) ≤ r}) := by
      ext ω
      by_cases hω : ω ∈ G <;> simp only [mem_ofPred_eq, mem_union, mem_compl_iff,
        mem_inter_iff, hω, ↓reduceIte, not_true_eq_false, false_or, true_and,
        not_false_eq_true, true_or, zero_le]
    rw [he]
    exact hGr.compl.union (hGr.inter (hA n r))
  intro u
  have h := hcut.measurableSet_stopping_time_le (isStoppingTime_inverseTime ha hG hA hs hb hc hm u)
  change MeasurableSet[(isStoppingTime_inverseTime ha hG hA hs hb hc hm u).measurableSpace] _
  have he : {ω | (imageStop (a := a) (G := G) (W := W) (V := V) (A := A) n ω : WithTop ℝ≥0) ≤ u} =
      {ω | (if ω ∈ G then (A n ω : WithTop ℝ≥0) else 0) ≤ inverseTime G a W V T u ω} := by
    ext ω
    by_cases hω : ω ∈ G
    · have hsep := hs ω hω
      have hn := hb ω hω n
      have hcl := clk_lt_newHorizon' hsep ha hn
      by_cases hu : (u : ℝ≥0∞) < newHorizon a (W · ω) (V · ω) (T ω)
      · simp only [imageStop, inverseTime, hω, hu, ↓reduceIte, mem_ofPred_eq,
          WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
        exact (le_invClk_iff hsep ha hu hn).symm
      · simp only [imageStop, inverseTime, hω, hu, ↓reduceIte, mem_ofPred_eq,
          WithTop.coe_le_coe]
        exact iff_of_true (ENNReal.coe_le_coe.1 (hcl.2.le.trans (not_lt.1 hu)))
          ((coe_le_toWT_iff _ _).2 hn.le)
    · simp only [imageStop, inverseTime, hω, ↓reduceIte, mem_ofPred_eq,
        WithTop.coe_zero, zero_le, le_refl]
  rw [he]
  exact h

/-- The clock images announce the image horizon in the constructed filtration. -/
theorem isAnnouncingSeq_imageStop {P : Measure Ω} (hGa : ∀ᵐ ω ∂P, ω ∈ G)
    (hAm : ∀ ω, Monotone (A · ω)) :
    Coupling.IsAnnouncingSeq (imageFiltration ha hG hA hs hb hc hm) P
      (fun ω => if ω ∈ G then newHorizon a (W · ω) (V · ω) (T ω) else 0)
      (imageStop (a := a) (G := G) (W := W) (V := V) (A := A)) := by
  refine ⟨isStoppingTime_imageStop ha hG hA hs hb hc hm, ?_, ?_, ?_⟩
  · intro ω m n hmn
    by_cases hω : ω ∈ G
    · simp only [imageStop, hω, ↓reduceIte]
      apply Real.toNNReal_mono
      have hr := ((hs ω hω).isSep_of_lt (hb ω hω n)).isRate ha
      exact (hr.clk_le_clk ⟨(A m ω).coe_nonneg, by exact_mod_cast hAm ω hmn⟩
        ⟨(A n ω).coe_nonneg, le_rfl⟩).2 (by exact_mod_cast hAm ω hmn)
    · simp only [imageStop, hω, ↓reduceIte, le_refl]
  · intro n
    filter_upwards [hGa] with ω hω
    simp only [imageStop, hω, ↓reduceIte]
    exact (clk_lt_newHorizon' (hs ω hω) ha (hb ω hω n)).2
  · filter_upwards [hGa] with ω hω u hu
    simp only [hω, ↓reduceIte] at hu
    obtain ⟨s, hse, hus⟩ := exists_lt_clk_of_lt_newHorizon hu
    obtain ⟨n, hn⟩ := hc ω hω s hse
    refine ⟨n, ?_⟩
    simp only [imageStop, hω, ↓reduceIte]
    have hr := ((hs ω hω).isSep_of_lt (hb ω hω n)).isRate ha
    have hle := (hr.clk_le_clk ⟨s.coe_nonneg, by exact_mod_cast hn⟩
      ⟨(A n ω).coe_nonneg, le_rfl⟩).2 (by exact_mod_cast hn)
    exact (Real.le_toNNReal_iff_coe_le (clk_lt_newHorizon' (hs ω hω) ha (hb ω hω n)).1).2
      (hus.le.trans hle)

end InteractingSLE.Sec5.TwoMark.Clock7

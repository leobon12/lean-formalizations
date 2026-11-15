/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverClock

/-!
# Capacity survival at an observed physical line

Packet PROVE-RETPLUMB. The clock is bounded by its capacity lifetime, including
after its boundary stop. Its strict capacity-survival cut can consequently be
tested from the current clock and physical survival at the current line.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7

/-- A path constant after `c` has the same prefix capacity at every later line. -/
theorem chartClock_eq_of_constant_after {Γ : ℝ≥0 → ℂ} {c t : ℝ≥0}
    (hc : ∀ s, c ≤ s → Γ s = Γ c) (ht : c ≤ t) :
    chartClock Γ t = chartClock Γ c := by
  have hi : Γ '' Icc 0 t = Γ '' Icc 0 c := by
    apply Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      by_cases hsc : s ≤ c
      · exact ⟨s, ⟨hs.1, hsc⟩, rfl⟩
      · exact ⟨c, ⟨zero_le, le_rfl⟩, (hc s (le_of_not_ge hsc)).symm⟩
    · exact image_mono (Icc_subset_Icc_right ht)
  unfold chartClock
  rw [hi]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {x₂ : ℝ}

/-- The boundary-stopped chart clock never exceeds the retained capacity life. -/
theorem retClock_le_retLife {ω : Ω}
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (t : ℝ≥0) :
    (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) ≤ retLife G η₁' η₂' ζ₂ u r ω := by
  rw [retClock_eq hd hG hp₂ hpair, retLife_eq]
  let L := retLifeP η₁' η₂' ζ₂ u r ω
  let Γ := retChartPath G η₁' η₂' ζ₂ u r ω
  have hC : IsClockOn (chartClock Γ) L := (retChartPath_clock hd hG hp₂ hpair).1
  by_cases ht : (t : ℝ≥0∞) ≤ L
  · exact hC.coe_toNNReal_le_capLife ht
  · have hLt : L ≤ (t : ℝ≥0∞) := (lt_of_not_ge ht).le
    have hfin : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hLt
    have he : (L.toNNReal : ℝ≥0∞) = L := ENNReal.coe_toNNReal hfin
    have hc : ∀ s, L.toNNReal ≤ s → Γ s = Γ L.toNNReal := by
      intro s hs
      change contPath _ _ _ _ L s = contPath _ _ _ _ L L.toNNReal
      rw [contPath_of_le (he ▸ ENNReal.coe_le_coe.2 hs), contPath_of_le he.symm.le]
    rw [chartClock_eq_of_constant_after hc (by
      exact ENNReal.coe_le_coe.1 (he.symm ▸ hLt))]
    exact hC.coe_toNNReal_le_capLife he.le

/-- Strict capacity survival through a reached capacity is observable at the
physical line, even when the physical path has already stopped there. -/
theorem RetPrefixObservations.measurableSet_capacityCut
    {𝓖 : Filtration ℝ≥0 mΩ} {F : Set Ω}
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) (q t : ℝ≥0) :
    MeasurableSet[𝓖 t]
      {ω | (q : ℝ≥0∞) < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω ∧
        q ≤ F.indicator (retClock G η₁' η₂' ζ₂ u r t) ω} := by
  classical
  let Q := F.indicator (retClock G η₁' η₂' ζ₂ u r t)
  have he : {ω | (q : ℝ≥0∞) < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω ∧ q ≤ Q ω} =
      {ω | q < Q ω} ∪ ({ω | q = Q ω} ∩
        (F ∩ {ω | (t : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω})) := by
    ext ω
    by_cases hω : ω ∈ F
    · have hQV := retClock_le_retLife hd (hG hω) (hp₂ ω hω) (hpair ω hω) t
      have hl := retClock_lt_retLife_iff hd (hG hω) (hp₂ ω hω) (hpair ω hω) (t := t)
      simp only [Q, indicator_of_mem hω, mem_ofPred_eq, mem_union, mem_inter_iff,
        hω, true_and]
      constructor
      · rintro ⟨hv, hq⟩
        rcases lt_or_eq_of_le hq with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr ⟨heq, hl.1 (heq ▸ hv)⟩
      · rintro (hlt | ⟨heq, ht⟩)
        · exact ⟨(ENNReal.coe_lt_coe.2 hlt).trans_le hQV, hlt.le⟩
        · exact ⟨heq.symm ▸ hl.2 ht, heq.le⟩
    · simp only [Q, indicator_of_notMem hω, mem_ofPred_eq,
        false_and, mem_union, not_lt_zero, mem_inter_iff, hω, or_self, and_false]
  rw [show {ω | (q : ℝ≥0∞) < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω ∧ q ≤ Q ω} =
    _ from he]
  have hQ := ho.measurable_clock hd hG hp₂ hpair t
  exact (measurableSet_lt measurable_const hQ).union
    ((measurableSet_eq_fun measurable_const hQ).inter (ho.survival t))

end InteractingSLE.Restart.RetAux79

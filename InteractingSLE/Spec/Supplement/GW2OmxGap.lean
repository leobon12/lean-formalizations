/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6SourceCContact

/-!
# GW2's open lines: the no-contact event from rational samples

Packet PROVE-GW2-STAGEMEAN, R120 round (localization of the stage mean). The physical no-contact event between the
counterflow trace `γ` (in the infinity-source chart) on `[0, T]` and the explored trace `α` on `[0, s]` — no
`γ t · α u + 1 = 0` — is read off rational samples, so it is measurable for any σ-algebra making the fixed-time trace
evaluations measurable; for continuous traces it is the event "no contact" of GB6
(`Supp8.GB6.SourceC.prefixGap_pos_iff`, `lt_firstContactTime_iff`).

* `gapEvent`, **`measurableSet_gapEvent`**, **`mem_gapEvent_iff`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Omx

/-- The sample condition at the rational pair `(q₁, q₂)` with gap `1/(n+1)`. -/
def gapAt {Ω : Type*} (γ α : Ω → ℝ≥0 → ℂ) (T s : ℝ≥0) (n : ℕ) (q₁ q₂ : ℚ) : Set Ω :=
  {ω | (0 ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ T ∧ 0 ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ s) →
    1 / ((n : ℝ) + 1) ≤ ‖γ ω (q₁ : ℝ).toNNReal * α ω (q₂ : ℝ).toNNReal + 1‖}

/-- **The rational-sample gap event**: some uniform gap `1/(n+1)` at all rational times of `[0, T] × [0, s]`. -/
def gapEvent {Ω : Type*} (γ α : Ω → ℝ≥0 → ℂ) (T s : ℝ≥0) : Set Ω :=
  ⋃ n : ℕ, ⋂ (q₁ : ℚ) (q₂ : ℚ), gapAt γ α T s n q₁ q₂

theorem measurableSet_gapEvent {Ω : Type*} {m : MeasurableSpace Ω} {γ α : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ q, Measurable[m] fun ω => γ ω q) (hα : ∀ q, Measurable[m] fun ω => α ω q) (T s : ℝ≥0) :
    MeasurableSet[m] (gapEvent γ α T s) := by
  refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q₁ => MeasurableSet.iInter fun q₂ => ?_
  unfold gapAt
  by_cases hq : 0 ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ T ∧ 0 ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ s
  · have e : {ω | (0 ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ T ∧ 0 ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ s) →
        1 / ((n : ℝ) + 1) ≤ ‖γ ω (q₁ : ℝ).toNNReal * α ω (q₂ : ℝ).toNNReal + 1‖} =
        {ω | 1 / ((n : ℝ) + 1) ≤ ‖γ ω (q₁ : ℝ).toNNReal * α ω (q₂ : ℝ).toNNReal + 1‖} := by
      ext ω
      simp only [mem_ofPred_eq, hq, and_self, true_implies]
    rw [e]
    exact measurableSet_le measurable_const ((((hγ _).mul (hα _))).add_const 1).norm
  · simp only [hq, false_implies, ofPred_true]
    exact MeasurableSet.univ

/-- Rational points approach any `t ∈ [0, b]` from inside `[0, b]`. -/
theorem exists_seq_rat_tendsto {t b : ℝ} (ht0 : 0 ≤ t) (htb : t ≤ b) :
    ∃ q : ℕ → ℚ, (∀ n, 0 ≤ (q n : ℝ) ∧ (q n : ℝ) ≤ b) ∧ Tendsto (fun n => (q n : ℝ)) atTop (𝓝 t) := by
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · refine ⟨fun _ => 0, fun _ => ⟨by simp, by rw [← h0] at htb; simpa using htb⟩, ?_⟩
    rw [← h0]
    simp
  · have hex : ∀ n : ℕ, ∃ r : ℚ, max 0 (t - 1 / ((n : ℝ) + 1)) < r ∧ (r : ℝ) < t := fun n => by
      have hlt : max 0 (t - 1 / ((n : ℝ) + 1)) < t := max_lt hpos (by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
      exact exists_rat_btwn hlt
    choose q hq using hex
    refine ⟨q, fun n => ⟨(le_max_left _ _).trans (hq n).1.le, (hq n).2.le.trans htb⟩, ?_⟩
    have hlo : Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have := (tendsto_const_nhds (x := t)).sub h0
      simpa only [sub_zero] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun n => ?_) (fun n => (hq n).2.le)
    exact (le_max_right _ _).trans (hq n).1.le

/-- **For continuous traces the gap event is the no-contact event.** -/
theorem mem_gapEvent_iff {Ω : Type*} {γ α : Ω → ℝ≥0 → ℂ} {T s : ℝ≥0} {ω : Ω} (hγ : Continuous (γ ω))
    (hα : Continuous (α ω)) :
    ω ∈ gapEvent γ α T s ↔ ∀ t ∈ Icc 0 T, ∀ u ∈ Icc 0 s, γ ω t * α ω u + 1 ≠ 0 := by
  constructor
  · intro hω t ht u hu
    obtain ⟨n, hn⟩ := mem_iUnion.1 hω
    obtain ⟨q₁, hq₁, hq₁t⟩ := exists_seq_rat_tendsto (t := (t : ℝ)) t.coe_nonneg (by exact_mod_cast ht.2)
    obtain ⟨q₂, hq₂, hq₂u⟩ := exists_seq_rat_tendsto (t := (u : ℝ)) u.coe_nonneg (by exact_mod_cast hu.2)
    have hbound : ∀ k, 1 / ((n : ℝ) + 1) ≤ ‖γ ω (q₁ k : ℝ).toNNReal * α ω (q₂ k : ℝ).toNNReal + 1‖ := fun k => by
      have h := mem_iInter.1 (mem_iInter.1 hn (q₁ k)) (q₂ k)
      exact h ⟨(hq₁ k).1, (hq₁ k).2, (hq₂ k).1, (hq₂ k).2⟩
    have h1 : Tendsto (fun k => (q₁ k : ℝ).toNNReal) atTop (𝓝 t) := by
      have := (continuous_real_toNNReal.tendsto _).comp hq₁t
      rwa [Real.toNNReal_coe] at this
    have h2 : Tendsto (fun k => (q₂ k : ℝ).toNNReal) atTop (𝓝 u) := by
      have := (continuous_real_toNNReal.tendsto _).comp hq₂u
      rwa [Real.toNNReal_coe] at this
    have hlim : Tendsto (fun k => ‖γ ω (q₁ k : ℝ).toNNReal * α ω (q₂ k : ℝ).toNNReal + 1‖) atTop
        (𝓝 ‖γ ω t * α ω u + 1‖) :=
      ((((hγ.tendsto t).comp h1).mul ((hα.tendsto u).comp h2)).add_const 1).norm
    have hge : 1 / ((n : ℝ) + 1) ≤ ‖γ ω t * α ω u + 1‖ := ge_of_tendsto' hlim hbound
    intro h0
    rw [h0, norm_zero] at hge
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro hsep
    have hpos := (Supp8.GB6.SourceC.prefixGap_pos_iff hγ hα T s).2 hsep
    have hfin : Supp8.GB6.SourceC.prefixGap (γ ω) (α ω) T s ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (iInf_le (fun p : (Icc 0 T) × (Icc 0 s) => ENNReal.ofReal ‖γ ω p.1.val * α ω p.2.val + 1‖)
          (⟨0, ⟨le_rfl, zero_le⟩⟩, ⟨0, ⟨le_rfl, zero_le⟩⟩))
    set δ := (Supp8.GB6.SourceC.prefixGap (γ ω) (α ω) T s).toReal with hδ
    have hδpos : 0 < δ := ENNReal.toReal_pos hpos.ne' hfin
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
    refine mem_iUnion.2 ⟨n, mem_iInter.2 fun q₁ => mem_iInter.2 fun q₂ => fun hq => ?_⟩
    have hle : Supp8.GB6.SourceC.prefixGap (γ ω) (α ω) T s ≤
        ENNReal.ofReal ‖γ ω (q₁ : ℝ).toNNReal * α ω (q₂ : ℝ).toNNReal + 1‖ :=
      iInf_le (fun p : (Icc 0 T) × (Icc 0 s) => ENNReal.ofReal ‖γ ω p.1.val * α ω p.2.val + 1‖)
        (⟨(q₁ : ℝ).toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hq.2.1⟩⟩,
          ⟨(q₂ : ℝ).toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hq.2.2.2⟩⟩)
    have hle' : δ ≤ ‖γ ω (q₁ : ℝ).toNNReal * α ω (q₂ : ℝ).toNNReal + 1‖ := by
      rw [hδ]
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at this
    exact hn.le.trans hle'

end InteractingSLE.Theorem14.GW2Omx

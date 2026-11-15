/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A clock with a positive continuous rate, its inverse, and the change of variables

Packet PROVE-SEC7-C8 (the process-level target change of §7.3 and Lemma LP9). The retargeting map
`M_t(z) = β_t + α_t/(V(t) − z)` carries the Loewner flow to the Loewner flow run at the clock
`ds = α²(V − W)^{-4} dt`. This file is the clock calculus, for an arbitrary rate `σ` that is continuous and positive on
`[0, S]`:

* `clk σ s = ∫₀ˢ σ` and its inverse `invClk σ t = inf {s ≥ 0 | t ≤ clk σ s}` (`IsRate σ S`: `σ` continuous and
  positive on `[0, S]`); `clk_invClk`, `invClk_clk`, `invClk_mem`, monotonicity, continuity, derivatives;
* **the change of variables** `∫₀^{clk σ S} g = ∫₀^S σ · (g ∘ clk σ)` for every `g` (`integral_clk_eq`), and the
  corresponding integrability equivalence (`intervalIntegrable_clk_iff`), from Mathlib's one-dimensional Jacobian
  formula (`integral_image_eq_integral_abs_deriv_smul`).

The pattern is that of `Strip.stripClock` (`Foundations/Strip/Chain.lean`) and `Sec2.TwoSeed.integral_Ioc_clock_eq`
(`Spec/Sec2/TwoSeedPath.lean`), for a general rate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-- The clock `C(s) = ∫₀ˢ σ`. -/
def clk (σ : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, σ u

/-- The inverse clock: the first `s ≥ 0` with `t ≤ C(s)`. -/
def invClk (σ : ℝ → ℝ) (t : ℝ) : ℝ := sInf {s | 0 ≤ s ∧ t ≤ clk σ s}

/-- `σ` is a clock rate on `[0, S]`: continuous and positive there. -/
structure IsRate (σ : ℝ → ℝ) (S : ℝ) : Prop where
  nonneg : 0 ≤ S
  cont : ContinuousOn σ (Icc 0 S)
  pos : ∀ s ∈ Icc 0 S, 0 < σ s

@[simp] theorem clk_zero (σ : ℝ → ℝ) : clk σ 0 = 0 := by simp [clk]

namespace IsRate

variable {σ : ℝ → ℝ} {S : ℝ}

theorem mono (h : IsRate σ S) {S' : ℝ} (h0 : 0 ≤ S') (hS : S' ≤ S) : IsRate σ S' :=
  ⟨h0, h.cont.mono (Icc_subset_Icc_right hS), fun s hs => h.pos s ⟨hs.1, hs.2.trans hS⟩⟩

theorem intervalIntegrable (h : IsRate σ S) {a b : ℝ} (ha : a ∈ Icc 0 S) (hb : b ∈ Icc 0 S) :
    IntervalIntegrable σ volume a b :=
  (h.cont.mono (uIcc_subset_Icc ha hb)).intervalIntegrable

theorem continuousOn_clk (h : IsRate σ S) : ContinuousOn (clk σ) (Icc 0 S) := by
  have hI := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := S) (f := σ)
    (by rw [uIcc_of_le h.nonneg]; exact h.cont.integrableOn_Icc)
  rwa [uIcc_of_le h.nonneg] at hI

theorem clk_sub (h : IsRate σ S) {a b : ℝ} (ha : a ∈ Icc 0 S) (hb : b ∈ Icc 0 S) :
    clk σ b - clk σ a = ∫ u in a..b, σ u := by
  rw [clk, clk, intervalIntegral.integral_interval_sub_left (h.intervalIntegrable ⟨le_rfl, h.nonneg⟩ hb)
    (h.intervalIntegrable ⟨le_rfl, h.nonneg⟩ ha)]

theorem clk_lt (h : IsRate σ S) {a b : ℝ} (ha : a ∈ Icc 0 S) (hb : b ∈ Icc 0 S) (hab : a < b) :
    clk σ a < clk σ b := by
  have hpos : 0 < ∫ u in a..b, σ u :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (h.intervalIntegrable ha hb)
      (fun u hu => h.pos u ⟨ha.1.trans hu.1.le, hu.2.le.trans hb.2⟩) hab
  linarith [h.clk_sub ha hb]

theorem strictMonoOn_clk (h : IsRate σ S) : StrictMonoOn (clk σ) (Icc 0 S) :=
  fun _ ha _ hb hab => h.clk_lt ha hb hab

theorem clk_nonneg (h : IsRate σ S) {s : ℝ} (hs : s ∈ Icc 0 S) : 0 ≤ clk σ s := by
  rcases hs.1.eq_or_lt with h0 | h0
  · rw [← h0, clk_zero]
  · exact (clk_zero σ ▸ h.clk_lt ⟨le_rfl, h.nonneg⟩ hs h0).le

theorem clk_le_clk (h : IsRate σ S) {a b : ℝ} (ha : a ∈ Icc 0 S) (hb : b ∈ Icc 0 S) :
    clk σ a ≤ clk σ b ↔ a ≤ b :=
  h.strictMonoOn_clk.le_iff_le ha hb

/-- The inverse clock at `t ∈ [0, C(S)]` is the unique `s ∈ [0, S]` with `C(s) = t`. -/
theorem isLeast_invClk (h : IsRate σ S) {t : ℝ} (ht : t ∈ Icc 0 (clk σ S)) :
    ∃ s ∈ Icc 0 S, clk σ s = t ∧ IsLeast {s | 0 ≤ s ∧ t ≤ clk σ s} s := by
  obtain ⟨s, hs, hst⟩ := intermediate_value_Icc h.nonneg h.continuousOn_clk (by rw [clk_zero]; exact ht)
  refine ⟨s, hs, hst, ⟨hs.1, hst.ge⟩, fun r hr => ?_⟩
  by_contra hlt
  have hlt := not_le.1 hlt
  have := h.clk_lt ⟨hr.1, hlt.le.trans hs.2⟩ hs hlt
  linarith [hr.2]

theorem invClk_mem (h : IsRate σ S) {t : ℝ} (ht : t ∈ Icc 0 (clk σ S)) : invClk σ t ∈ Icc 0 S := by
  obtain ⟨s, hs, -, hl⟩ := h.isLeast_invClk ht
  rw [invClk, hl.csInf_eq]; exact hs

theorem clk_invClk (h : IsRate σ S) {t : ℝ} (ht : t ∈ Icc 0 (clk σ S)) : clk σ (invClk σ t) = t := by
  obtain ⟨s, -, hst, hl⟩ := h.isLeast_invClk ht
  rw [invClk, hl.csInf_eq, hst]

theorem invClk_clk (h : IsRate σ S) {s : ℝ} (hs : s ∈ Icc 0 S) : invClk σ (clk σ s) = s := by
  have ht : clk σ s ∈ Icc 0 (clk σ S) :=
    ⟨h.clk_nonneg hs, h.strictMonoOn_clk.monotoneOn hs ⟨h.nonneg, le_rfl⟩ hs.2⟩
  exact h.strictMonoOn_clk.injOn (h.invClk_mem ht) hs (h.clk_invClk ht)

@[simp] theorem invClk_zero (h : IsRate σ S) : invClk σ 0 = 0 := by
  simpa using h.invClk_clk ⟨le_rfl, h.nonneg⟩

theorem strictMonoOn_invClk (h : IsRate σ S) : StrictMonoOn (invClk σ) (Icc 0 (clk σ S)) := by
  intro a ha b hb hab
  by_contra hle
  have hle := not_lt.1 hle
  have := h.strictMonoOn_clk.monotoneOn (h.invClk_mem hb) (h.invClk_mem ha) hle
  rw [h.clk_invClk ha, h.clk_invClk hb] at this
  linarith

/-- `C(s) ≤ t ↔ s ≤ C⁻¹(t)` for `s ∈ [0, S]`, `t ∈ [0, C(S)]`. -/
theorem clk_le_iff_le_invClk (h : IsRate σ S) {s t : ℝ} (hs : s ∈ Icc 0 S) (ht : t ∈ Icc 0 (clk σ S)) :
    clk σ s ≤ t ↔ s ≤ invClk σ t := by
  rw [← h.clk_le_clk hs (h.invClk_mem ht), h.clk_invClk ht]

/-- `C` has derivative `σ` at interior times. -/
theorem hasDerivAt_clk (h : IsRate σ S) {s : ℝ} (hs : s ∈ Ioo 0 S) : HasDerivAt (clk σ) (σ s) s := by
  have hc : ContinuousOn σ (Ioo 0 S) := h.cont.mono Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_right
    (h.intervalIntegrable ⟨le_rfl, h.nonneg⟩ ⟨hs.1.le, hs.2.le⟩)
    (hc.stronglyMeasurableAtFilter isOpen_Ioo s hs) (hc.continuousAt (isOpen_Ioo.mem_nhds hs))

theorem image_clk_Ioo (h : IsRate σ S) : clk σ '' Ioo 0 S = Ioo 0 (clk σ S) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : s ∈ Icc 0 S := Ioo_subset_Icc_self hs
    exact ⟨by simpa using h.clk_lt ⟨le_rfl, h.nonneg⟩ hs' hs.1, h.clk_lt hs' ⟨h.nonneg, le_rfl⟩ hs.2⟩
  · intro ht
    have ht' : t ∈ Icc 0 (clk σ S) := Ioo_subset_Icc_self ht
    have hm := h.invClk_mem ht'
    refine ⟨invClk σ t, ⟨hm.1.lt_of_ne fun h0 => ?_, hm.2.lt_of_ne fun hS => ?_⟩, h.clk_invClk ht'⟩
    · have := h.clk_invClk ht'
      rw [← h0, clk_zero] at this; linarith [ht.1]
    · have := h.clk_invClk ht'
      rw [hS] at this; linarith [ht.2]

theorem invClk_mem_Ioo (h : IsRate σ S) {t : ℝ} (ht : t ∈ Ioo 0 (clk σ S)) : invClk σ t ∈ Ioo 0 S := by
  rw [← h.image_clk_Ioo] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  rwa [h.invClk_clk (Ioo_subset_Icc_self hs)]

theorem invClk_lt (h : IsRate σ S) {t : ℝ} (ht : t ∈ Ico 0 (clk σ S)) : invClk σ t < S := by
  refine (h.invClk_mem (Ico_subset_Icc_self ht)).2.lt_of_ne fun hS => ?_
  have := h.clk_invClk (Ico_subset_Icc_self ht)
  rw [hS] at this; linarith [ht.2]

theorem invClk_pos (h : IsRate σ S) {t : ℝ} (ht : t ∈ Ioc 0 (clk σ S)) : 0 < invClk σ t := by
  refine (h.invClk_mem (Ioc_subset_Icc_self ht)).1.lt_of_ne fun h0 => ?_
  have := h.clk_invClk (Ioc_subset_Icc_self ht)
  rw [← h0, clk_zero] at this; linarith [ht.1]

theorem continuousOn_invClk (h : IsRate σ S) : ContinuousOn (invClk σ) (Icc 0 (clk σ S)) := by
  intro t ht
  have hmono := h.strictMonoOn_invClk
  have hR : ContinuousWithinAt (invClk σ) (Icc 0 (clk σ S) ∩ Ici t) t := by
    rcases ht.2.lt_or_eq with hlt | heq
    · refine (hmono.continuousWithinAt_right_of_exists_between (Icc_mem_nhdsGE_of_mem ⟨ht.1, hlt⟩)
        fun b hb => ?_).mono inter_subset_right
      have hlt' := h.invClk_lt ⟨ht.1, hlt⟩
      have hm : min b S ∈ Icc 0 S :=
        ⟨le_min ((h.invClk_mem ht).1.trans hb.le) h.nonneg, min_le_right _ _⟩
      refine ⟨clk σ (min b S), ⟨h.clk_nonneg hm, (h.clk_le_clk hm ⟨h.nonneg, le_rfl⟩).2 hm.2⟩, ?_⟩
      rw [h.invClk_clk hm]
      exact ⟨lt_min hb hlt', min_le_left _ _⟩
    · have e : Icc 0 (clk σ S) ∩ Ici t = {t} := by
        ext r
        simp only [mem_inter_iff, mem_Icc, mem_Ici, mem_singleton_iff]
        constructor
        · rintro ⟨⟨-, h2⟩, h3⟩; rw [← heq] at h2; exact le_antisymm h2 h3
        · rintro rfl; exact ⟨ht, le_rfl⟩
      rw [e]; exact continuousWithinAt_singleton
  have hL : ContinuousWithinAt (invClk σ) (Icc 0 (clk σ S) ∩ Iic t) t := by
    rcases ht.1.lt_or_eq with hlt | heq
    · refine (hmono.continuousWithinAt_left_of_exists_between (Icc_mem_nhdsLE_of_mem ⟨hlt, ht.2⟩)
        fun b hb => ?_).mono inter_subset_right
      have hpos := h.invClk_pos ⟨hlt, ht.2⟩
      have hm : max b 0 ∈ Icc 0 S :=
        ⟨le_max_right _ _, max_le (hb.le.trans (h.invClk_mem ht).2) h.nonneg⟩
      refine ⟨clk σ (max b 0), ⟨h.clk_nonneg hm, (h.clk_le_clk hm ⟨h.nonneg, le_rfl⟩).2 hm.2⟩, ?_⟩
      rw [h.invClk_clk hm]
      exact ⟨le_max_left _ _, max_lt hb hpos⟩
    · have e : Icc 0 (clk σ S) ∩ Iic t = {t} := by
        ext r
        simp only [mem_inter_iff, mem_Icc, mem_Iic, mem_singleton_iff]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩; rw [← heq] at h3 ⊢; exact le_antisymm h3 h1
        · rintro rfl; exact ⟨ht, le_rfl⟩
      rw [e]; exact continuousWithinAt_singleton
  refine (hL.union hR).mono fun r hr => ?_
  rcases le_total r t with hrt | htr
  · exact Or.inl ⟨hr, hrt⟩
  · exact Or.inr ⟨hr, htr⟩

/-- **Change of variables** `u = C(s)`: `∫₀^{C(S)} g = ∫₀^S σ · (g ∘ C)` for every `g`. -/
theorem integral_clk_eq (h : IsRate σ S) (g : ℝ → ℝ) :
    ∫ u in (0 : ℝ)..clk σ S, g u = ∫ s in (0 : ℝ)..S, σ s * g (clk σ s) := by
  have hC0 : 0 ≤ clk σ S := h.clk_nonneg ⟨h.nonneg, le_rfl⟩
  rw [intervalIntegral.integral_of_le hC0, intervalIntegral.integral_of_le h.nonneg,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, ← h.image_clk_Ioo,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun s hs => (h.hasDerivAt_clk hs).hasDerivWithinAt)
      (h.strictMonoOn_clk.injOn.mono Ioo_subset_Icc_self) g]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [abs_of_pos (h.pos s (Ioo_subset_Icc_self hs)), smul_eq_mul]

/-- Integrability transfers through the change of variables. -/
theorem intervalIntegrable_clk_iff (h : IsRate σ S) (g : ℝ → ℝ) :
    IntervalIntegrable g volume 0 (clk σ S) ↔
      IntervalIntegrable (fun s => σ s * g (clk σ s)) volume 0 S := by
  have hC0 : 0 ≤ clk σ S := h.clk_nonneg ⟨h.nonneg, le_rfl⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hC0, intervalIntegrable_iff_integrableOn_Ioc_of_le h.nonneg,
    ← integrableOn_Icc_iff_integrableOn_Ioc, ← integrableOn_Icc_iff_integrableOn_Ioc,
    integrableOn_Icc_iff_integrableOn_Ioo, integrableOn_Icc_iff_integrableOn_Ioo, ← h.image_clk_Ioo,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      (fun s hs => (h.hasDerivAt_clk hs).hasDerivWithinAt)
      (h.strictMonoOn_clk.injOn.mono Ioo_subset_Icc_self) g]
  refine integrableOn_congr_fun (fun s hs => ?_) measurableSet_Ioo
  rw [abs_of_pos (h.pos s (Ioo_subset_Icc_self hs)), smul_eq_mul]

end IsRate

end Retarget

end Zhan

end InteractingSLE

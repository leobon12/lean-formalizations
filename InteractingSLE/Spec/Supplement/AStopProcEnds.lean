/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdModelCode
import InteractingSLE.Spec.Supplement.RetChartWord
import InteractingSLE.Spec.Sec7.Lemma76GMain

/-!
# The chart image of the retained union: two real segments (item 3 of `AStopSourceInputs`, deterministic part)

Packet PROVE-T15-ASTOP-PROC. In the retained chart of an ordinary pair (second tip at `0`), the chart reals whose
inverse image lies on the retained union `A = α[0, a] ∪ β[0, b]` form the set `aStopSet (L₂, R₂, L₁, R₁)` of
`RLC.OrdModel` (two real segments):

* `mem_seg_iff`: `seg a b` is the real interval `[a, b]` for `a ≤ b`;
* **`aStopSet_zoneData`** (disjoint prefixes, Lemma 7.6's zone data, `Sec7.Lemma76G.IsSetting`): the second prefix
  occupies exactly `[L₂, R₂]` and the first exactly `[L₁, R₁]`;
* **`aStopSet_zoneDataT`** (touching prefixes, Aux. lemma 85's outer boundary `RLC.RetTouch.IsTouchZones`): the union
  occupies exactly `[L₂, R₁] = [L₂, J] ∪ [J, R₁]`, `J` the junction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Supp7 Sec7 Sec7.Lemma76G RetChart RetTouch OrdModel

/-! ### Real segments -/

theorem mem_seg_iff {a b : ℝ} (hab : a ≤ b) {z : ℂ} : z ∈ seg a b ↔ z.im = 0 ∧ a ≤ z.re ∧ z.re ≤ b := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [segPt, Complex.ofReal_im, Complex.ofReal_re, true_and]
    constructor <;> nlinarith [hx.1, hx.2]
  · rintro ⟨him, h1, h2⟩
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have hre : z.re = a := le_antisymm h2 h1
      rw [← ofReal_re_eq him, hre]
      simp [segPt]
    · refine ⟨(z.re - a) / (b - a), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
      have hb : b - a ≠ 0 := by linarith
      apply Complex.ext
      · simp only [segPt, Complex.ofReal_re]
        field_simp
        ring
      · simp only [segPt, Complex.ofReal_im, him]

/-! ### Disjoint prefixes -/

/-- **At a disjoint pair the chart reals over the retained union are `[L₂, R₂] ∪ [L₁, R₁]`.** -/
theorem aStopSet_zoneData {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
    (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) :
    aStopSet ((zoneData φ α a β b).L₂, (zoneData φ α a β b).R₂, (zoneData φ α a β b).L₁,
        (zoneData φ α a β b).R₁) = {w : ℂ | w.im = 0 ∧ ψ w ∈ α '' Icc 0 a ∪ β '' Icc 0 b} := by
  set z := zoneData φ α a β b with hzdef
  have hz := hs.zoneData_good
  have hRL := hs.R₂_lt_L₁
  have h2 : z.L₂ ≤ z.R₂ := hz.L₂_le.trans hz.M₂_le
  have h1 : z.L₁ ≤ z.R₁ := hz.L₁_le.trans hz.M₁_le
  ext w
  simp only [aStopSet, mem_union, mem_seg_iff h2, mem_seg_iff h1, mem_ofPred_eq]
  constructor
  · rintro (⟨him, hl, hr⟩ | ⟨him, hl, hr⟩)
    · refine ⟨him, ?_⟩
      rw [← ofReal_re_eq him]
      rcases hs.inv_cases w.re with hα | hβ | hu
      · exact Or.inl hα
      · exact Or.inr hβ
      · exfalso
        obtain ⟨-, hx, hT⟩ := hs.untouched_cases hu
        rcases (hs.isUntouched_iff _).1 hx with hx0 | hx1 | hx2
        · have := hz.T₀_lt _ hx0
          rw [hT] at this
          linarith
        · have := hz.lt_T₁ _ hx1
          rw [hT] at this
          linarith
        · have := hz.lt_T₂ _ hx2
          rw [hT] at this
          linarith
    · refine ⟨him, ?_⟩
      rw [← ofReal_re_eq him]
      rcases hs.inv_cases w.re with hα | hβ | hu
      · exact Or.inl hα
      · exact Or.inr hβ
      · exfalso
        obtain ⟨-, hx, hT⟩ := hs.untouched_cases hu
        rcases (hs.isUntouched_iff _).1 hx with hx0 | hx1 | hx2
        · have := hz.T₀_lt _ hx0
          rw [hT] at this
          linarith
        · have := hz.T₁_lt _ hx1
          rw [hT] at this
          linarith
        · have := hz.lt_T₂ _ hx2
          rw [hT] at this
          linarith
  · rintro ⟨him, hA⟩
    rw [← ofReal_re_eq him] at hA
    rcases hA with hα | hβ
    · exact Or.inr ⟨him, hs.L₁_le_of_mem₁ hα, hs.le_R₁_of_mem₁ hα⟩
    · exact Or.inl ⟨him, hs.L₂_le_of_mem₂ hβ, hs.le_R₂_of_mem₂ hβ⟩

/-! ### Touching prefixes -/

/-- **At a touching pair the chart reals over the retained union are `[L₂, R₁] = [L₂, J] ∪ [J, R₁]`.** -/
theorem aStopSet_zoneDataT {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {z : ZW} (ht : IsTouchZones α a β b ψ z) :
    aStopSet (z.L₂, z.R₂, z.L₁, z.R₁) = {w : ℂ | w.im = 0 ∧ ψ w ∈ α '' Icc 0 a ∪ β '' Icc 0 b} := by
  have hz := ht.good
  have hJ := ht.junction
  have h2 : z.L₂ ≤ z.R₂ := hz.L₂_le.trans hz.M₂_le
  have h1 : z.L₁ ≤ z.R₁ := hz.L₁_le.trans hz.M₁_le
  ext w
  simp only [aStopSet, mem_union, mem_seg_iff h2, mem_seg_iff h1, mem_ofPred_eq]
  constructor
  · rintro (⟨him, hl, hr⟩ | ⟨him, hl, hr⟩)
    · refine ⟨him, ?_⟩
      rw [← ofReal_re_eq him]
      by_contra hn
      rcases ht.lt_or_gt_of_notMem hn with h | h <;> linarith [hz.L₁_le, hz.M₁_le]
    · refine ⟨him, ?_⟩
      rw [← ofReal_re_eq him]
      by_contra hn
      rcases ht.lt_or_gt_of_notMem hn with h | h <;> linarith [hz.M₂_le, hz.L₂_le]
  · rintro ⟨him, hA⟩
    rw [← ofReal_re_eq him] at hA
    have hlo : z.L₂ ≤ w.re := by
      by_contra hlt
      obtain ⟨him', hx, -⟩ := ht.zone₀ w.re (lt_of_not_ge hlt)
      exact ht.notMem_zone _ (Or.inl hx) (by rw [ofReal_re_eq him']; exact hA)
    have hhi : w.re ≤ z.R₁ := by
      by_contra hlt
      obtain ⟨him', hx, -⟩ := ht.zone₂ w.re (lt_of_not_ge hlt)
      exact ht.notMem_zone _ (Or.inr hx) (by rw [ofReal_re_eq him']; exact hA)
    by_cases hw : w.re ≤ z.R₂
    · exact Or.inl ⟨him, hlo, hw⟩
    · exact Or.inr ⟨him, hJ ▸ (lt_of_not_ge hw).le, hhi⟩

end InteractingSLE.RLC.AStopProc

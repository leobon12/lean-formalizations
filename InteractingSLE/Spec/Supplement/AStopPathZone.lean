/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathHeight
import InteractingSLE.Spec.Supplement.Aux85Junction

/-!
# The chart-boundary facts of the A-stop at disjoint and touching ordinary pairs

Packet PROVE-T15-ASTOP-PATH. `AStopPath.IsAChart` for both continuations of an ordinary retained pair, read off the
zone data of the retained chart:

* disjoint prefixes (Lemma 7.6's setting `Sec7.Lemma76G.IsSetting`, zone data `zoneData`): **`zone_of_setting`** (an
  untouched chart point lies in one of the three untouched zones, with its real image left of the second base, between
  the bases, or right of the first base), **`isAChart_snd_of_setting`**, **`isAChart_fst_of_setting`** (the chart
  translated to the first tip `M₁`);
* touching prefixes (Aux. lemma 85's outer boundary `RLC.RetTouch.IsTouchZones`): **`isAChart_snd_of_touch`**,
  **`isAChart_fst_of_touch`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart Sec7.Lemma76G RetTouch

/-! ### Translated charts -/

theorem continuousOn_shift {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ Hbar) (τ : ℝ) :
    ContinuousOn (fun z : ℂ => ψ (z + (τ : ℂ))) Hbar :=
  hψ.comp (continuousOn_id.add continuousOn_const) fun z (hz : 0 ≤ z.im) => by
    show 0 ≤ (z + (τ : ℂ)).im
    rw [add_im, ofReal_im, add_zero]; exact hz

/-! ### Disjoint prefixes -/

section Setting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- **The three untouched zones of a disjoint pair.** -/
theorem zone_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {w : ℝ}
    (hw : ψ w ∉ α '' Icc 0 a ∪ β '' Icc 0 b) :
    (ψ w).im = 0 ∧ ((ψ w).re < x₂ ∧ w < 0 ∨
      x₂ < (ψ w).re ∧ (ψ w).re < x₁ ∧ 0 < w ∧ w < (zoneData φ α a β b).M₁ ∨
      x₁ < (ψ w).re ∧ (zoneData φ α a β b).M₁ < w) := by
  have hz := hs.zoneData_good
  have hRL := hs.R₂_lt_L₁
  have hM₂ : (zoneData φ α a β b).M₂ = 0 := rfl
  have hL₂x : baseL β b ≤ x₂ := baseL_le hs.hp₂ hs.hb (seed_mem_realSet hs.hp₂)
  have hR₂x : x₂ ≤ baseR β b := le_baseR hs.hp₂ hs.hb (seed_mem_realSet hs.hp₂)
  have hL₁x : baseL α a ≤ x₁ := baseL_le hs.hp₁ hs.ha (seed_mem_realSet hs.hp₁)
  have hR₁x : x₁ ≤ baseR α a := le_baseR hs.hp₁ hs.ha (seed_mem_realSet hs.hp₁)
  rcases hs.inv_cases w with h | h | h
  · exact absurd (Or.inl h) hw
  · exact absurd (Or.inr h) hw
  obtain ⟨-, hu, hT⟩ := hs.untouched_cases h
  refine ⟨h.1, ?_⟩
  rcases (hs.isUntouched_iff _).1 hu with h0 | h1 | h2
  · have := hz.T₀_lt _ h0
    rw [hT] at this
    exact Or.inl ⟨lt_of_lt_of_le h0 hL₂x, by linarith [hz.L₂_le]⟩
  · have h3 := hz.lt_T₁ _ h1
    have h4 := hz.T₁_lt _ h1
    rw [hT] at h3 h4
    exact Or.inr (Or.inl ⟨lt_of_le_of_lt hR₂x h1.1, lt_of_lt_of_le h1.2 hL₁x, by linarith [hz.M₂_le],
      by linarith [hz.L₁_le]⟩)
  · have := hz.lt_T₂ _ h2
    rw [hT] at this
    exact Or.inr (Or.inr ⟨lt_of_le_of_lt hR₁x h2, by linarith [hz.M₁_le]⟩)

theorem isClosed_union_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) :
    IsClosed (α '' Icc 0 a ∪ β '' Icc 0 b) :=
  ((Sec7.IsPathGood.isCompact_image hs.hp₁ hs.ha).union (Sec7.IsPathGood.isCompact_image hs.hp₂ hs.hb)).isClosed

theorem continuousOn_inv_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) : ContinuousOn ψ Hbar :=
  (IsRetChart.isDomChart hs.hC (by rw [Sec7.IsPathGood.zero hs.hp₂, ofReal_im])
    (isClosed_union_of_setting hs)).continuousOn_inv

theorem zero_lt_M₁_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) : 0 < (zoneData φ α a β b).M₁ := by
  have hz := hs.zoneData_good
  have hM₂ : (zoneData φ α a β b).M₂ = 0 := rfl
  linarith [hs.R₂_lt_L₁, hz.M₂_le, hz.L₁_le]

/-- **The second continuation's chart facts at a disjoint pair.** -/
theorem isAChart_snd_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) :
    IsAChart ψ (α '' Icc 0 a ∪ β '' Icc 0 b) x₂ where
  cont := continuousOn_inv_of_setting hs
  closed := isClosed_union_of_setting hs
  real := fun w hw => (zone_of_setting hs hw).1
  neg := fun w hw hw0 => by
    have hM := zero_lt_M₁_of_setting hs
    rcases (zone_of_setting hs hw).2 with h | h | h
    · exact h.1
    · linarith [h.2.2.1]
    · linarith [h.2]
  pos := fun w hw hw0 => by
    have hx := hs.hx
    rcases (zone_of_setting hs hw).2 with h | h | h
    · linarith [h.2]
    · exact h.1
    · linarith [h.1]

/-- **The first continuation's chart facts at a disjoint pair** (chart translated to the first tip). -/
theorem isAChart_fst_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) :
    IsAChart (fun z : ℂ => ψ (z + ((zoneData φ α a β b).M₁ : ℂ))) (α '' Icc 0 a ∪ β '' Icc 0 b) x₁ where
  cont := continuousOn_shift (continuousOn_inv_of_setting hs) _
  closed := isClosed_union_of_setting hs
  real := fun w hw => by
    rw [← ofReal_add] at hw ⊢
    exact (zone_of_setting hs hw).1
  neg := fun w hw hw0 => by
    rw [← ofReal_add] at hw ⊢
    have hx := hs.hx
    rcases (zone_of_setting hs hw).2 with h | h | h
    · linarith [h.1]
    · exact h.2.1
    · linarith [h.2]
  pos := fun w hw hw0 => by
    rw [← ofReal_add] at hw ⊢
    have hM := zero_lt_M₁_of_setting hs
    rcases (zone_of_setting hs hw).2 with h | h | h
    · linarith [h.2]
    · linarith [h.2.2.2]
    · exact h.1

end Setting

/-! ### Touching prefixes -/

section Touch

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {z : ZW}

/-- **The two untouched zones of a touching pair.** -/
theorem zone_of_touch (ht : IsTouchZones α a β b ψ z) (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (ha : (a : ℝ≥0∞) ≤ ζ₁) (hb : (b : ℝ≥0∞) ≤ ζ₂) (ha₂ : z.a₂ = baseL β b) (hb₁ : z.b₁ = baseR α a) {w : ℝ}
    (hw : ψ w ∉ α '' Icc 0 a ∪ β '' Icc 0 b) :
    (ψ w).im = 0 ∧ ((ψ w).re < x₂ ∧ w < z.L₂ ∨ x₁ < (ψ w).re ∧ z.R₁ < w) := by
  have hL₂x : baseL β b ≤ x₂ := baseL_le hp₂ hb (seed_mem_realSet hp₂)
  have hR₁x : x₁ ≤ baseR α a := le_baseR hp₁ ha (seed_mem_realSet hp₁)
  rcases ht.lt_or_gt_of_notMem hw with h | h
  · obtain ⟨him, hre, -⟩ := ht.zone₀ w h
    rw [ha₂] at hre
    exact ⟨him, Or.inl ⟨lt_of_lt_of_le hre hL₂x, h⟩⟩
  · obtain ⟨him, hre, -⟩ := ht.zone₂ w h
    rw [hb₁] at hre
    exact ⟨him, Or.inr ⟨lt_of_le_of_lt hR₁x hre, h⟩⟩

theorem M₁_le_R₁_of_touch (ht : IsTouchZones α a β b ψ z) : z.M₁ ≤ z.R₁ := ht.good.M₁_le

/-- **The second continuation's chart facts at a touching pair.** -/
theorem isAChart_snd_of_touch (ht : IsTouchZones α a β b ψ z) (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (ha : (a : ℝ≥0∞) ≤ ζ₁) (hb : (b : ℝ≥0∞) ≤ ζ₂) (hx : x₂ ≤ x₁) (ha₂ : z.a₂ = baseL β b)
    (hb₁ : z.b₁ = baseR α a) (hψ : ContinuousOn ψ Hbar) :
    IsAChart ψ (α '' Icc 0 a ∪ β '' Icc 0 b) x₂ where
  cont := hψ
  closed := ((Sec7.IsPathGood.isCompact_image hp₁ ha).union (Sec7.IsPathGood.isCompact_image hp₂ hb)).isClosed
  real := fun w hw => (zone_of_touch ht hp₁ hp₂ ha hb ha₂ hb₁ hw).1
  neg := fun w hw hw0 => by
    have hM := ht.zero_lt_M₁
    have hMR := M₁_le_R₁_of_touch ht
    rcases (zone_of_touch ht hp₁ hp₂ ha hb ha₂ hb₁ hw).2 with h | h
    · exact h.1
    · linarith [h.2]
  pos := fun w hw hw0 => by
    have hL := ht.L₂_le_zero
    rcases (zone_of_touch ht hp₁ hp₂ ha hb ha₂ hb₁ hw).2 with h | h
    · linarith [h.2]
    · linarith [h.1]

/-- **The first continuation's chart facts at a touching pair** (chart translated to the first tip). -/
theorem isAChart_fst_of_touch (ht : IsTouchZones α a β b ψ z) (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (ha : (a : ℝ≥0∞) ≤ ζ₁) (hb : (b : ℝ≥0∞) ≤ ζ₂) (hx : x₂ ≤ x₁) (ha₂ : z.a₂ = baseL β b)
    (hb₁ : z.b₁ = baseR α a) (hψ : ContinuousOn ψ Hbar) :
    IsAChart (fun w : ℂ => ψ (w + (z.M₁ : ℂ))) (α '' Icc 0 a ∪ β '' Icc 0 b) x₁ where
  cont := continuousOn_shift hψ _
  closed := ((Sec7.IsPathGood.isCompact_image hp₁ ha).union (Sec7.IsPathGood.isCompact_image hp₂ hb)).isClosed
  real := fun w hw => by
    rw [← ofReal_add] at hw ⊢
    exact (zone_of_touch ht hp₁ hp₂ ha hb ha₂ hb₁ hw).1
  neg := fun w hw hw0 => by
    rw [← ofReal_add] at hw ⊢
    have hMR := M₁_le_R₁_of_touch ht
    rcases (zone_of_touch ht hp₁ hp₂ ha hb ha₂ hb₁ hw).2 with h | h
    · linarith [h.1]
    · linarith [h.2]
  pos := fun w hw hw0 => by
    rw [← ofReal_add] at hw ⊢
    have hM := ht.zero_lt_M₁
    have hL := ht.L₂_le_zero
    rcases (zone_of_touch ht hp₁ hp₂ ha hb ha₂ hb₁ hw).2 with h | h
    · linarith [h.2]
    · exact h.1

end Touch

end InteractingSLE.RLC.AStopPath

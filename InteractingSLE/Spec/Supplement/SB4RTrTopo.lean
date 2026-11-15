/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrCf

/-!
# A proper curve through its initial arc

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). **`tail_range_of_arc`**: if a proper curve `β₀` from
`0` has range `[0, v] ∪ (X + v)` and `X` is the range of a proper curve from `0`, then `β₀` reaches `v` after
traversing `[0, v]` and its tail from there has range exactly `X + v` (so `X + v` misses `[0, v)`). A proper
(continuous, injective, norm-proper) curve is a closed embedding of `ℝ≥0`, the curve `β₀⁻¹ ∘ (β' + v)` is continuous
and injective from the end of the arc to `∞`, hence increasing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B

/-- A proper curve is a closed embedding. -/
theorem isClosedEmbedding_of_isProperCurve {β : ℝ≥0 → ℂ} (h : IsProperCurve β) : IsClosedEmbedding β := by
  have hT : Tendsto β (cocompact ℝ≥0) (cocompact ℂ) := by
    rw [cocompact_eq_atTop, ← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.1 h.2.2.2
  have hP : IsProperMap β := isProperMap_iff_tendsto_cocompact.2 ⟨h.1, hT⟩
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap h.1 h.2.1 hP.isClosedMap

/-- **The tail of a proper curve through its initial arc.** -/
theorem tail_range_of_arc {β₀ β' : ℝ≥0 → ℂ} (h₀ : IsProperCurve β₀) (h₀0 : β₀ 0 = 0) (h' : IsProperCurve β')
    (h'0 : β' 0 = 0) {v : ℝ} (hv : 0 < v)
    (hW : range β₀ = ((↑) : ℝ → ℂ) '' Icc 0 v ∪ (fun z => z + (v : ℂ)) '' range β') :
    ∃ tv : ℝ≥0, β₀ tv = v ∧ range (fun s => β₀ (tv + s) - v) = range β' := by
  have hemb := isClosedEmbedding_of_isProperCurve h₀
  set Iv : Set ℂ := ((↑) : ℝ → ℂ) '' Icc 0 v with hIv
  have hIvW : Iv ⊆ range β₀ := hW ▸ subset_union_left
  set S : Set ℝ≥0 := β₀ ⁻¹' Iv with hS
  have hSimg : β₀ '' S = Iv := image_preimage_eq_of_subset hIvW
  have hIvc : IsConnected Iv := (isConnected_Icc hv.le).image _ Complex.continuous_ofReal.continuousOn
  have hSpre : IsPreconnected S := hemb.isInducing.isPreconnected_image.1 (hSimg ▸ hIvc.isPreconnected)
  have hIvcpt : IsCompact Iv := isCompact_Icc.image Complex.continuous_ofReal
  have hScpt : IsCompact S := hemb.isProperMap.isCompact_preimage hIvcpt
  have hS0 : (0 : ℝ≥0) ∈ S := by
    show β₀ 0 ∈ Iv; rw [h₀0]; exact ⟨0, ⟨le_rfl, hv.le⟩, by simp⟩
  have hSne : S.Nonempty := ⟨0, hS0⟩
  set tv := sSup S with htv
  have htvS : tv ∈ S := hScpt.isClosed.csSup_mem hSne hScpt.bddAbove
  have hSeq : S = Icc 0 tv := by
    refine le_antisymm (fun t ht => ⟨bot_le, le_csSup hScpt.bddAbove ht⟩) (hSpre.Icc_subset hS0 htvS)
  -- along the arc the curve is real and increasing
  have hreal : ∀ t ∈ Icc (0 : ℝ≥0) tv, β₀ t = ((β₀ t).re : ℂ) := fun t ht => by
    obtain ⟨x, -, hx⟩ : β₀ t ∈ Iv := (hSeq ▸ ht : t ∈ S)
    rw [← hx, Complex.ofReal_re]
  have hg_c : ContinuousOn (fun t => (β₀ t).re) (Icc 0 tv) := (Complex.continuous_re.comp h₀.1).continuousOn
  have hg_i : InjOn (fun t => (β₀ t).re) (Icc 0 tv) := fun s hs t ht hst => h₀.2.1 (by
    rw [hreal s hs, hreal t ht]; exact congrArg _ hst)
  have hvS : ∃ t ∈ Icc (0 : ℝ≥0) tv, β₀ t = v := by
    have : (v : ℂ) ∈ β₀ '' S := hSimg ▸ ⟨v, ⟨hv.le, le_rfl⟩, rfl⟩
    obtain ⟨t, ht, hte⟩ := this
    exact ⟨t, hSeq ▸ ht, hte⟩
  obtain ⟨t₁, ht₁, ht₁v⟩ := hvS
  have hmem : ∀ t ∈ Icc (0 : ℝ≥0) tv, (β₀ t).re ∈ Icc 0 v := fun t ht => by
    obtain ⟨x, hx, hxe⟩ : β₀ t ∈ Iv := (hSeq ▸ ht : t ∈ S)
    rw [← hxe, Complex.ofReal_re]; exact hx
  have htvv : β₀ tv = v := by
    rcases hg_c.strictMonoOn_of_injOn_Icc' bot_le hg_i with hmono | hanti
    · have h1 : (β₀ t₁).re ≤ (β₀ tv).re := hmono.monotoneOn ht₁ ⟨bot_le, le_rfl⟩ ht₁.2
      rw [ht₁v, Complex.ofReal_re] at h1
      rw [hreal tv ⟨bot_le, le_rfl⟩, le_antisymm (hmem tv ⟨bot_le, le_rfl⟩).2 h1]
    · exfalso
      have h1 : (β₀ t₁).re ≤ (β₀ 0).re := hanti.antitoneOn ⟨le_rfl, bot_le⟩ ht₁ ht₁.1
      rw [ht₁v, h₀0, Complex.ofReal_re, Complex.zero_re] at h1
      linarith
  -- the restarted curve inside the range
  have hXW : ∀ s, β' s + v ∈ range β₀ := fun s => hW ▸ Or.inr ⟨β' s, ⟨s, rfl⟩, rfl⟩
  let e := hemb.isEmbedding.toHomeomorph
  let φ : ℝ≥0 → ℝ≥0 := fun s => e.symm ⟨β' s + v, hXW s⟩
  have hφe : ∀ s, β₀ (φ s) = β' s + v := fun s => by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨β' s + v, hXW s⟩)
    exact this
  have hφc : Continuous φ := e.symm.continuous.comp (Continuous.subtype_mk (h'.1.add continuous_const) _)
  have hφi : Function.Injective φ := fun s t hst => by
    have := congrArg β₀ hst
    rw [hφe, hφe] at this
    exact h'.2.1 (add_right_cancel this)
  have hφ0 : φ 0 = tv := h₀.2.1 (by rw [hφe, h'0, zero_add, htvv])
  have hφmono : StrictMono φ := by
    rcases hφc.strictMono_of_inj hφi with hm | ha
    · exact hm
    · exfalso
      -- an antitone `φ` keeps `β' + v` on the compact arc image
      have hbd : ∀ s, φ s ≤ tv := fun s => hφ0 ▸ ha.antitone (bot_le : (0 : ℝ≥0) ≤ s)
      have hK : IsCompact (β₀ '' Icc 0 tv) := isCompact_Icc.image h₀.1
      obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
      obtain ⟨s, hs⟩ := (h'.2.2.2.eventually_gt_atTop (R + |v|)).exists
      have h1 := hR _ ⟨φ s, ⟨bot_le, hbd s⟩, rfl⟩
      rw [hφe] at h1
      have h2 : ‖β' s‖ ≤ ‖β' s + v‖ + ‖(v : ℂ)‖ := by
        calc ‖β' s‖ = ‖(β' s + v) - v‖ := by ring_nf
          _ ≤ _ := norm_sub_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs] at h2
      linarith
  have hφge : ∀ s, tv ≤ φ s := fun s => hφ0 ▸ hφmono.monotone (bot_le : (0 : ℝ≥0) ≤ s)
  refine ⟨tv, htvv, ?_⟩
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    have hw : β₀ (tv + s) ∈ range β₀ := ⟨_, rfl⟩
    rw [hW] at hw
    rcases hw with hI | ⟨y, hy, hye⟩
    · have hts : tv + s ∈ S := hI
      rw [hSeq] at hts
      have hs0 : s = 0 := by
        have := hts.2
        exact le_antisymm (by simpa using this) bot_le
      subst hs0
      show β₀ (tv + 0) - v ∈ range β'
      rw [add_zero, htvv, sub_self]
      exact ⟨0, h'0⟩
    · show β₀ (tv + s) - v ∈ range β'
      rw [← hye, add_sub_cancel_right]
      exact hy
  · rintro ⟨s, rfl⟩
    refine ⟨φ s - tv, ?_⟩
    show β₀ (tv + (φ s - tv)) - v = β' s
    rw [add_tsub_cancel_of_le (hφge s), hφe, add_sub_cancel_right]

end InteractingSLE.Theorem14.SB.Lf

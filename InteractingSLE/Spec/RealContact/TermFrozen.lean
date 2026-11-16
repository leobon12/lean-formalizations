/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermSide
import InteractingSLE.Spec.Supplement.RLCFAvgSide
import InteractingSLE.Spec.Supplement.SB2GSide

/-!
# The side input of the configuration builder for a Loewner explorer (builder frame)

Packet PROVE-RC-TERM, second run (ruling R124). For an explorer `β` that is a generating trace and a completed
retained path with entry data (`Term.IsEntryData`), the side input S1 of SB2(1)'s configuration builder:

* **`exists_frozen_completion`**: a prefix `β([0, a])` strictly before the lifetime has a proper completion whose new
  part lies in `ℍ` off the prefix's filled hull (the prefix followed by the inverse Loewner image of the vertical ray
  above the driving point, `RLC.isProperCurve_rayCurve`);
* `IsEntryData.real_le_tip`: the real points of the completed path are weakly left of its (positive) tip;
* **`IsEntryData.isRetPath`**: the path `t ↦ ξ t + d` on `[0, T]` satisfies `Term.IsRetPath`;
* **`exists_side_completion`**: from W5 on strict prefixes, a proper completion `β'` of the explorer prefix with the
  retained path in its closed right side (`TermSide`'s early and late cases).

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.RealContact

namespace Term

open Supp9B HalfPlaneSep Theorem14 Theorem14.SB

/-! ### The frozen completion of a generating trace -/

/-- **The frozen completion.** A prefix of a generating trace strictly before its lifetime has a proper completion
whose new part lies in `ℍ` off the filled hull of the prefix. -/
theorem exists_frozen_completion {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ} (hβ : IsGeneratingTrace w ζ β)
    (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {a : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ)
    (hinj : InjOn β (Icc 0 a)) (hH : ∀ t ≤ a, 0 ≤ (β t).im) :
    ∃ βf, IsProperCompletion β a βf ∧ ∀ t, a < t → βf t ∈ H \ fillH (β '' Icc 0 a) := by
  obtain ⟨W, η', hW, hW0, hη', hagree, hK⟩ := FinRel.exists_globalTrace_of_isGeneratingTrace hβ hw hw0
    (t := (a : ℝ)) a.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact ha)
  rw [Real.toNNReal_coe] at hK
  have ha0 : (0 : ℝ) ≤ a := a.coe_nonneg
  set ψ : ℂ → ℂ := extendFrom H (fwdMapInv W a) with hψ
  have hψH : ∀ v ∈ H, ψ v = fwdMapInv W a v := fun v hv => ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 ha0 hv
  have hψc : ContinuousOn ψ Hbar := (hη'.hasBdryLimits hW hW0 ha0).continuousOn
  obtain ⟨M, hM⟩ := FinRel.exists_norm_extendFrom_sub_le hη' hW hW0 ha0
  have hmapD : ∀ v ∈ H, ψ v ∈ H \ fwdHull W a := fun v hv => by
    rw [hψH v hv, ← QuantumZipper.RS.image_fwdMapInv_H hW hW0 ha0]
    exact ⟨v, hv, rfl⟩
  have hψ0 : ψ ((0 : ℝ) : ℂ) = β a := by
    rw [ofReal_zero, hψ, ZhanGT4.extendFrom_zero_eq hη' hW hW0 ha0, (hagree a ⟨ha0, le_rfl⟩).2,
      Real.toNNReal_coe]
  have hc : ContinuousOn β (Icc 0 a) := hβ.2.1.mono fun t ht =>
    show (t : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 ht.2).trans ha.le
  have hP : IsProperCurve (RLC.rayCurve β a ψ 0) := by
    refine RLC.isProperCurve_rayCurve (D := H \ fwdHull W a) (M := M) hc hinj hH sdiff_subset ?_
      (fun v hv => hmapD v hv) ?_ hψc hM hψ0
    · rintro z hz ⟨t, ht, rfl⟩
      rw [hK] at hz
      exact hz.2 ⟨hz.1, Or.inl (subset_closure ⟨t, ht, rfl⟩)⟩
    · intro v hv v' hv' hvv'
      rw [hψH v hv, hψH v' hv'] at hvv'
      have h1 := QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ha0 hv
      have h2 := QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ha0 hv'
      rw [← h1, ← h2, hvv']
  refine ⟨RLC.rayCurve β a ψ 0, ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, fun t ht => RLC.rayCurve_of_le ht⟩,
    fun t ht => ?_⟩
  rw [RLC.rayCurve_of_lt ht, ← hK]
  exact hmapD _ (RLC.ray_mem_H ht)

/-! ### The completed path as a retained path -/

variable {V : ℝ → ℝ} {ξ : ℝ → ℂ} {p d : ℝ}

/-- The real points of a completed path are weakly left of its positive tip. -/
theorem IsEntryData.real_le_tip {T : ℝ} (h : IsEntryData V T ξ p d) (hp : 0 < p) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (him : (ξ s).im = 0) : (ξ s).re ≤ p := by
  by_contra hlt
  push Not at hlt
  have h0 : ξ 0 = 0 := h.tip.trace.1
  have hs0 : 0 < s := by
    rcases hs.1.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, h0, zero_re] at hlt
      linarith
  have hsT : s < T := by
    rcases hs.2.lt_or_eq with h1 | h1
    · exact h1
    · rw [h1, h.tip.tip, ofReal_re] at hlt
      exact absurd hlt (lt_irrefl _)
  have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
  have hpP : (p : ℂ) ∉ ξ '' Icc 0 s := by
    rintro ⟨t, ht, htp⟩
    have := h.inj (hsub ht) ⟨h.tip.pos.le, le_rfl⟩ (htp.trans h.tip.tip.symm)
    linarith [ht.2]
  have hmem := YuanCharacterisation.mem_closure_fillH_of_lt_of_lt (h.tip.traceCont.mono hsub)
    (h.hbar.mono_left hsub) (u₁ := 0) (u₂ := s) ⟨le_rfl, hs0.le⟩ ⟨hs0.le, le_rfl⟩ (by rw [h0, zero_im]) him
    (by rw [h0, zero_re]; exact hp) hlt hpP
  rw [← h.tip.trace.2.2 s hs0.le hsT] at hmem
  exact h.tip.fresh s hs0.le hsT hmem

/-- **The completed path, translated by `d`, is a retained path of the builder frame.** -/
theorem IsEntryData.isRetPath {T : ℝ≥0} (h : IsEntryData V (T : ℝ) ξ p d) (hp : 0 < p)
    (hne : ∀ s : ℝ, 0 < s → s ≤ T → ξ s + (d : ℂ) ≠ 0) :
    IsRetPath (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) T d (p + d) := by
  have hmem : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ Icc (0 : ℝ) T := fun t ht => ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  refine ⟨?_, ?_, fun t ht => ?_, ?_, h.seed, ?_, ?_, fun t ht him => ?_, fun t ht him => ?_,
    fun t ht ht0 => hne t (NNReal.coe_pos.2 ht0) (NNReal.coe_le_coe.2 ht)⟩
  · exact ContinuousOn.add (h.tip.traceCont.comp NNReal.continuous_coe.continuousOn fun t ht => hmem t ht.2)
      continuousOn_const
  · intro s hs t ht hst
    exact NNReal.coe_injective (h.inj (hmem s hs.2) (hmem t ht.2) (add_right_cancel hst))
  · have : 0 ≤ (ξ (t : ℝ)).im := h.hbar (hmem t ht)
    show 0 ≤ (ξ (t : ℝ) + (d : ℂ)).im
    simpa only [add_im, ofReal_im, add_zero] using this
  · show ξ ((0 : ℝ≥0) : ℝ) + (d : ℂ) = d
    rw [NNReal.coe_zero, h.tip.trace.1, zero_add]
  · show ξ (T : ℝ) + (d : ℂ) = ((p + d : ℝ) : ℂ)
    rw [h.tip.tip, ofReal_add]
  · exact NNReal.coe_pos.1 h.tip.pos
  · have him' : (ξ (t : ℝ)).im = 0 := by simpa only [add_im, ofReal_im, add_zero] using him
    have := h.real _ (hmem t ht) him'
    show 0 ≤ (ξ (t : ℝ) + (d : ℂ)).re
    rw [add_re, ofReal_re]
    linarith
  · have him' : (ξ (t : ℝ)).im = 0 := by simpa only [add_im, ofReal_im, add_zero] using him
    have := h.real_le_tip hp (hmem t ht) him'
    show (ξ (t : ℝ) + (d : ℂ)).re ≤ p + d
    rw [add_re, ofReal_re]
    linarith

/-- The builder's path and the retained path of the side argument have the same range. -/
theorem image_entryPath_eq {T : ℝ≥0} (hT : (0 : ℝ) < T) (ξ : ℝ → ℂ) (d : ℝ) :
    entryPath ξ (T : ℝ) d '' Icc 0 1 = (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) '' Icc 0 T := by
  rw [image_entryPath ξ hT d]
  ext z
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 ht.2⟩, ?_⟩
    simp only [Real.coe_toNNReal t ht.1]
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ξ (t : ℝ), ⟨(t : ℝ), ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht.2⟩, rfl⟩, rfl⟩

/-! ### The side input -/

/-- **The side input S1 from W5 on strict prefixes.** For a generating-trace explorer `β` and entry data of a
completed path with a positive tip: if the prefix `β([0, a])`, `a` before the lifetime, has no positive-time contact
with the translated path and W5 holds for every strict prefix of the path, the prefix has a proper completion with the
whole path in its closed right side. -/
theorem exists_side_completion {T : ℝ≥0} (hE : IsEntryData V (T : ℝ) ξ p d) (hp : 0 < p)
    (hne : ∀ s : ℝ, 0 < s → s ≤ T → ξ s + (d : ℂ) ≠ 0)
    {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ} (hβ : IsGeneratingTrace w ζ β)
    (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {a : ℝ≥0} (ha : (a : ℝ≥0∞) < ζ)
    (hinj : InjOn β (Icc 0 a)) (hH : ∀ t ≤ a, 0 ≤ (β t).im)
    (hoff : ∀ t ≤ a, 0 < t → β t ∉ (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) '' Icc 0 T)
    (hW : ∀ c : ℝ≥0, c < T → HasOrderedProperCompletions (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) c β a) :
    ∃ β', IsProperCompletion β a β' ∧ entryPath ξ (T : ℝ) d '' Icc 0 1 ⊆ closedRightSide β' := by
  have hQ := hE.isRetPath hp hne
  have hc : ContinuousOn β (Icc 0 a) := hβ.2.1.mono fun t ht =>
    show (t : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 ht.2).trans ha.le
  have hP : IsExpPrefix β a (fun t : ℝ≥0 => ξ (t : ℝ) + (d : ℂ)) T := ⟨hc, hH, hβ.1, hoff⟩
  rw [image_entryPath_eq hE.tip.pos]
  by_cases hearly : ∀ t ≤ a, ∀ y : ℝ, p + d ≤ y → β t ≠ y
  · obtain ⟨β', hβ', -, hsub⟩ := exists_completion_early hQ hP hW hearly
    exact ⟨β', hβ', hsub⟩
  · push Not at hearly
    obtain ⟨s, hs, y, hy, hsy⟩ := hearly
    have hs0 : 0 < s := by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
      · rw [← h0, hβ.1] at hsy
        have h1 : (0 : ℝ) = y := by exact_mod_cast hsy
        have := hQ.tip_pos
        linarith
      · exact h0
    have hyE : p + d < y := by
      rcases hy.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd ⟨T, ⟨zero_le, le_rfl⟩, by rw [hsy, ← heq]; exact hQ.tip⟩ (hoff s hs hs0)
    obtain ⟨βf, hβf, hfr⟩ := exists_frozen_completion hβ hw hw0 ha hinj hH
    exact ⟨βf, hβf, subset_closedRightSide_late hQ hP hW hs hyE hsy hβf hfr⟩

end Term

end InteractingSLE.RealContact

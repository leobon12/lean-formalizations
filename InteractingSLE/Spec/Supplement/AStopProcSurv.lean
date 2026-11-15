/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualSurvival

/-!
# Survival of the A-stopped continuation from its past

Packet PROVE-T15-ASTOP-PROC. RETPLUMB's contact measurability (`RetAux79.measurableSet_contact_Ioc`,
`measurableSet_lt_contStop_of_prefix`) includes the real line in the contact set (ruling R55). For the A-stopped
continuation of Theorem 1.5's leaf 3 the contact set is the retained union `A = f₁[0, u] ∪ f₂[0, r]` only (real
contacts are allowed, G7 p. 497). The proofs below repeat RETPLUMB's without the real line:

* `measurableSet_contactA_Ioc`, `measurableSet_noContactA_Ioc` (contacts with `A` on `(a, b]`);
* `measurableSet_noContactA_Ioc_of_prefix` (only supported coordinates through the cutoffs);
* **`measurableSet_lt_contStopA_of_prefix`**: strict survival `b < contStop η ζ a A` from the live record and the
  supported coordinates through `b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Restart.RetAux79 Supp7

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Contacts with the union of two compact prefixes on a closed time window are measurable. -/
theorem measurableSet_contactA_window {F : Set Ω} (hF : MeasurableSet F) {η f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t) (hf₁ : ∀ t, Measurable fun ω => f₁ ω t)
    (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) (q b u r : ℝ≥0) (hqb : q ≤ b)
    (hcη : ∀ ω ∈ F, ContinuousOn (η ω) (Iic b)) (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | ∃ s ≤ b - q, η ω (q + s) ∈ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r}) := by
  have hc : ∀ ω ∈ F, ContinuousOn (fun s => η ω (q + s)) (Iic (b - q)) := by
    intro ω hω
    refine (hcη ω hω).comp (continuous_const.add continuous_id).continuousOn fun s hs => ?_
    change q + s ≤ b
    calc q + s ≤ q + (b - q) := add_le_add le_rfl hs
      _ = b := add_tsub_cancel_of_le hqb
  have h₁ := measurableSet_inter_exists_eq hF (fun s => hη (q + s)) hf₁
    measurable_const measurable_const hc hc₁
  have h₂ := measurableSet_inter_exists_eq hF (fun s => hη (q + s)) hf₂
    measurable_const measurable_const hc hc₂
  convert h₁.union h₂ using 1
  ext ω
  constructor
  · rintro ⟨hω, s, hs, ⟨t, ht, he⟩ | ⟨t, ht, he⟩⟩
    · exact Or.inl ⟨hω, s, hs, t, ht.2, he.symm⟩
    · exact Or.inr ⟨hω, s, hs, t, ht.2, he.symm⟩
  · rintro (⟨hω, s, hs, t, ht, he⟩ | ⟨hω, s, hs, t, ht, he⟩)
    · exact ⟨hω, s, hs, Or.inl ⟨t, ⟨zero_le, ht⟩, he.symm⟩⟩
    · exact ⟨hω, s, hs, Or.inr ⟨t, ⟨zero_le, ht⟩, he.symm⟩⟩

/-- **New contacts with `A` on `(a, b]` are measurable.** -/
theorem measurableSet_contactA_Ioc {F : Set Ω} (hF : MeasurableSet F) {η f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t) (hf₁ : ∀ t, Measurable fun ω => f₁ ω t)
    (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) (a b u r : ℝ≥0)
    (hcη : ∀ ω ∈ F, ContinuousOn (η ω) (Iic b)) (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | ∃ s : ℝ≥0, a < s ∧ s ≤ b ∧ η ω s ∈ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r}) := by
  classical
  have heq : F ∩ {ω | ∃ s : ℝ≥0, a < s ∧ s ≤ b ∧ η ω s ∈ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r} =
      ⋃ q : ℚ, if a < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal ≤ b then
        F ∩ {ω | ∃ s ≤ b - (q : ℝ).toNNReal,
          η ω ((q : ℝ).toNNReal + s) ∈ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r}
      else ∅ := by
    ext ω
    constructor
    · rintro ⟨hω, s, has, hsb, hK⟩
      obtain ⟨q, haq, hqs⟩ := exists_rat_btwn (show (a : ℝ) < s from has)
      have hq0 : (0 : ℝ) ≤ q := a.2.trans haq.le
      have haq' : a < (q : ℝ).toNNReal := by
        change (a : ℝ) < ((q : ℝ).toNNReal : ℝ)
        rw [Real.coe_toNNReal _ hq0]
        exact haq
      have hqs' : (q : ℝ).toNNReal ≤ s := by
        change ((q : ℝ).toNNReal : ℝ) ≤ (s : ℝ)
        rw [Real.coe_toNNReal _ hq0]
        exact hqs.le
      apply mem_iUnion.2 ⟨q, ?_⟩
      rw [ite_eq_left ⟨haq', hqs'.trans hsb⟩]
      exact ⟨hω, s - (q : ℝ).toNNReal, tsub_le_tsub_right hsb _, by rwa [add_tsub_cancel_of_le hqs']⟩
    · intro hω
      obtain ⟨q, hq⟩ := mem_iUnion.1 hω
      split_ifs at hq with hvalid
      · obtain ⟨hω, s, hs, hK⟩ := hq
        refine ⟨hω, (q : ℝ).toNNReal + s, hvalid.1.trans_le le_self_add, ?_, hK⟩
        calc (q : ℝ).toNNReal + s ≤ (q : ℝ).toNNReal + (b - (q : ℝ).toNNReal) := add_le_add le_rfl hs
          _ = b := add_tsub_cancel_of_le hvalid.2
      · exact hq.elim
  rw [heq]
  refine MeasurableSet.iUnion fun q => ?_
  split_ifs with hvalid
  · exact measurableSet_contactA_window hF hη hf₁ hf₂ _ b u r hvalid.2 hcη hc₁ hc₂
  · exact MeasurableSet.empty

/-- **Avoidance of `A` on `(a, b]` is measurable.** -/
theorem measurableSet_noContactA_Ioc {F : Set Ω} (hF : MeasurableSet F) {η f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t) (hf₁ : ∀ t, Measurable fun ω => f₁ ω t)
    (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) (a b u r : ℝ≥0)
    (hcη : ∀ ω ∈ F, ContinuousOn (η ω) (Iic b)) (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | ∀ s : ℝ≥0, a < s → s ≤ b → η ω s ∉ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r}) := by
  convert hF.diff (measurableSet_contactA_Ioc hF hη hf₁ hf₂ a b u r hcη hc₁ hc₂) using 1
  ext ω
  simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨hω, hn⟩
    exact ⟨hω, fun ⟨_, s, has, hsb, hK⟩ => hn s has hsb hK⟩
  · rintro ⟨hω, hn⟩
    exact ⟨hω, fun s has hsb hK => hn ⟨hω, s, has, hsb, hK⟩⟩

/-- The A-contact test needs only supported coordinates up to each cutoff. -/
theorem measurableSet_noContactA_Ioc_of_prefix {F : Set Ω} (hF : MeasurableSet F) {η f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (a b u r : ℝ≥0) (hη : ∀ s ≤ b, Measurable (F.indicator fun ω => η ω s))
    (hf₁ : ∀ s ≤ u, Measurable (F.indicator fun ω => f₁ ω s))
    (hf₂ : ∀ s ≤ r, Measurable (F.indicator fun ω => f₂ ω s))
    (hcη : ∀ ω ∈ F, ContinuousOn (η ω) (Iic b)) (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | ∀ s : ℝ≥0, a < s → s ≤ b → η ω s ∉ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r}) := by
  classical
  let clip : (Ω → ℝ≥0 → ℂ) → ℝ≥0 → Ω → ℝ≥0 → ℂ := fun f c ω s => F.indicator (fun ω => f ω (min s c)) ω
  have he : ∀ (f : Ω → ℝ≥0 → ℂ) c ω, ω ∈ F → ∀ s ≤ c, clip f c ω s = f ω s := by
    intro f c ω hω s hs
    simp only [clip, indicator_of_mem hω, min_eq_left hs]
  have hi : ∀ (f : Ω → ℝ≥0 → ℂ) c ω, ω ∈ F → clip f c ω '' Icc 0 c = f ω '' Icc 0 c :=
    fun f c ω hω => image_congr fun s hs => he f c ω hω s hs.2
  have hcont : ∀ (f : Ω → ℝ≥0 → ℂ) c, (∀ ω ∈ F, ContinuousOn (f ω) (Iic c)) →
      ∀ ω ∈ F, ContinuousOn (clip f c ω) (Iic c) := by
    intro f c hc ω hω
    have h : ContinuousOn (fun s : ℝ≥0 => f ω (min s c)) (Iic c) :=
      (hc ω hω).comp (continuous_id.min continuous_const).continuousOn fun _ _ => min_le_right _ c
    simpa only [clip, indicator_of_mem hω] using h
  have hm := measurableSet_noContactA_Ioc (η := clip η b) (f₁ := clip f₁ u) (f₂ := clip f₂ r) hF
    (fun s => hη (min s b) (min_le_right _ _)) (fun s => hf₁ (min s u) (min_le_right _ _))
    (fun s => hf₂ (min s r) (min_le_right _ _)) a b u r (hcont η b hcη) (hcont f₁ u hc₁) (hcont f₂ r hc₂)
  convert hm using 1
  ext ω
  constructor
  · rintro ⟨hω, hn⟩
    refine ⟨hω, fun s has hsb => ?_⟩
    simpa only [hi f₁ u ω hω, hi f₂ r ω hω, he η b ω hω s hsb] using hn s has hsb
  · rintro ⟨hω, hn⟩
    refine ⟨hω, fun s has hsb => ?_⟩
    simpa only [hi f₁ u ω hω, hi f₂ r ω hω, he η b ω hω s hsb] using hn s has hsb

/-- **Strict survival of the A-stopped continuation** is measurable from the live record and the supported
coordinates through the current endpoint. -/
theorem measurableSet_lt_contStopA_of_prefix {F : Set Ω} {η f₁ f₂ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (a b u r : ℝ≥0) (hab : a < b) (hFb : MeasurableSet (F ∩ {ω | (b : ℝ≥0∞) < ζ ω}))
    (hη : ∀ s ≤ b, Measurable ((F ∩ {ω | (b : ℝ≥0∞) < ζ ω}).indicator fun ω => η ω s))
    (hf₁ : ∀ s ≤ u, Measurable ((F ∩ {ω | (b : ℝ≥0∞) < ζ ω}).indicator fun ω => f₁ ω s))
    (hf₂ : ∀ s ≤ r, Measurable ((F ∩ {ω | (b : ℝ≥0∞) < ζ ω}).indicator fun ω => f₂ ω s))
    (hcη : ∀ ω ∈ F, (b : ℝ≥0∞) < ζ ω → ContinuousOn (η ω) (Iic b))
    (haη : ∀ ω ∈ F, (b : ℝ≥0∞) < ζ ω → ContinuousAt (η ω) b)
    (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u)) (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | (b : ℝ≥0∞) < contStop (η ω) (ζ ω) a (f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r)}) := by
  have hm := measurableSet_noContactA_Ioc_of_prefix hFb a b u r hη hf₁ hf₂
    (fun ω hω => hcη ω hω.1 hω.2) (fun ω hω => hc₁ ω hω.1) (fun ω hω => hc₂ ω hω.1)
  have hK : ∀ ω ∈ F, IsClosed (f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r) :=
    fun ω hω => ((isCompact_Icc.image_of_continuousOn ((hc₁ ω hω).mono Icc_subset_Iic_self)).union
      (isCompact_Icc.image_of_continuousOn ((hc₂ ω hω).mono Icc_subset_Iic_self))).isClosed
  convert hm using 1
  ext ω
  constructor
  · rintro ⟨hω, ht⟩
    have hζ : (b : ℝ≥0∞) < ζ ω := ht.trans_le contStop_le
    exact ⟨⟨hω, hζ⟩, (lt_contStop_iff_noContact_Ioc hab (haη ω hω hζ) (hK ω hω)).1 ht |>.2⟩
  · rintro ⟨⟨hω, hζ⟩, hn⟩
    exact ⟨hω, (lt_contStop_iff_noContact_Ioc hab (haη ω hω hζ) (hK ω hω)).2 ⟨hζ, hn⟩⟩

end InteractingSLE.RLC.AStopProc

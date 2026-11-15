/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualContact

/-!
# Boundary survival from the currently available path coordinates

Packet PROVE-RETPLUMB. All coordinate measurability below is restricted to
the current line or the retained cutoffs. Clipping supplies unused later
coordinates without observing any future path value.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open Supp7

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The contact test needs only supported coordinates up to each cutoff. -/
theorem measurableSet_noContact_Ioc_of_prefix {F : Set Ω} (hF : MeasurableSet F)
    {η f₁ f₂ : Ω → ℝ≥0 → ℂ} (a b u r : ℝ≥0)
    (hη : ∀ s ≤ b, Measurable (F.indicator fun ω => η ω s))
    (hf₁ : ∀ s ≤ u, Measurable (F.indicator fun ω => f₁ ω s))
    (hf₂ : ∀ s ≤ r, Measurable (F.indicator fun ω => f₂ ω s))
    (hcη : ∀ ω ∈ F, ContinuousOn (η ω) (Iic b))
    (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | ∀ s : ℝ≥0, a < s → s ≤ b →
      η ω s ∉ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r ∪ realLine}) := by
  classical
  let clip : (Ω → ℝ≥0 → ℂ) → ℝ≥0 → Ω → ℝ≥0 → ℂ :=
    fun f c ω s => F.indicator (fun ω => f ω (min s c)) ω
  have he : ∀ (f : Ω → ℝ≥0 → ℂ) c ω, ω ∈ F → ∀ s ≤ c, clip f c ω s = f ω s := by
    intro f c ω hω s hs
    simp only [clip, indicator_of_mem hω, min_eq_left hs]
  have hi : ∀ (f : Ω → ℝ≥0 → ℂ) c ω, ω ∈ F →
      clip f c ω '' Icc 0 c = f ω '' Icc 0 c :=
    fun f c ω hω => image_congr fun s hs => he f c ω hω s hs.2
  have hcont : ∀ (f : Ω → ℝ≥0 → ℂ) c, (∀ ω ∈ F, ContinuousOn (f ω) (Iic c)) →
      ∀ ω ∈ F, ContinuousOn (clip f c ω) (Iic c) := by
    intro f c hc ω hω
    have h : ContinuousOn (fun s : ℝ≥0 => f ω (min s c)) (Iic c) :=
      (hc ω hω).comp (continuous_id.min continuous_const).continuousOn
      (fun _ _ => min_le_right _ c)
    simpa only [clip, indicator_of_mem hω] using h
  have hm := measurableSet_noContact_Ioc
    (η := clip η b) (f₁ := clip f₁ u) (f₂ := clip f₂ r) hF
    (fun s => hη (min s b) (min_le_right _ _))
    (fun s => hf₁ (min s u) (min_le_right _ _))
    (fun s => hf₂ (min s r) (min_le_right _ _)) a b u r
    (hcont η b hcη) (hcont f₁ u hc₁) (hcont f₂ r hc₂)
  convert hm using 1
  ext ω
  constructor
  · rintro ⟨hω, hn⟩
    refine ⟨hω, fun s has hsb => ?_⟩
    simpa only [hi f₁ u ω hω, hi f₂ r ω hω, he η b ω hω s hsb] using hn s has hsb
  · rintro ⟨hω, hn⟩
    refine ⟨hω, fun s has hsb => ?_⟩
    simpa only [hi f₁ u ω hω, hi f₂ r ω hω, he η b ω hω s hsb] using hn s has hsb

/-- Survival is measurable from the live record and the supported coordinates
through the current endpoint. The contact set includes the real line. -/
theorem measurableSet_lt_contStop_of_prefix {F : Set Ω} {η f₁ f₂ : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (a b u r : ℝ≥0) (hab : a < b)
    (hFb : MeasurableSet (F ∩ {ω | (b : ℝ≥0∞) < ζ ω}))
    (hη : ∀ s ≤ b, Measurable
      ((F ∩ {ω | (b : ℝ≥0∞) < ζ ω}).indicator fun ω => η ω s))
    (hf₁ : ∀ s ≤ u, Measurable
      ((F ∩ {ω | (b : ℝ≥0∞) < ζ ω}).indicator fun ω => f₁ ω s))
    (hf₂ : ∀ s ≤ r, Measurable
      ((F ∩ {ω | (b : ℝ≥0∞) < ζ ω}).indicator fun ω => f₂ ω s))
    (hcη : ∀ ω ∈ F, (b : ℝ≥0∞) < ζ ω → ContinuousOn (η ω) (Iic b))
    (haη : ∀ ω ∈ F, (b : ℝ≥0∞) < ζ ω → ContinuousAt (η ω) b)
    (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | (b : ℝ≥0∞) <
      contStop (η ω) (ζ ω) a (f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r ∪ realLine)}) := by
  have hm := measurableSet_noContact_Ioc_of_prefix hFb a b u r hη hf₁ hf₂
    (fun ω hω => hcη ω hω.1 hω.2) (fun ω hω => hc₁ ω hω.1) (fun ω hω => hc₂ ω hω.1)
  have hK : ∀ ω ∈ F, IsClosed (f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r ∪ realLine) :=
    fun ω hω => (((isCompact_Icc.image_of_continuousOn
      ((hc₁ ω hω).mono Icc_subset_Iic_self)).union
      (isCompact_Icc.image_of_continuousOn ((hc₂ ω hω).mono Icc_subset_Iic_self))).isClosed).union
      isClosed_realLine
  convert hm using 1
  ext ω
  constructor
  · rintro ⟨hω, ht⟩
    have hζ : (b : ℝ≥0∞) < ζ ω := ht.trans_le contStop_le
    exact ⟨⟨hω, hζ⟩, (lt_contStop_iff_noContact_Ioc hab (haη ω hω hζ) (hK ω hω)).1 ht |>.2⟩
  · rintro ⟨⟨hω, hζ⟩, hn⟩
    exact ⟨hω, (lt_contStop_iff_noContact_Ioc hab (haη ω hω hζ) (hK ω hω)).2 ⟨hζ, hn⟩⟩

end InteractingSLE.Restart.RetAux79

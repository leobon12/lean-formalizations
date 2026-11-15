/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop419Proof
import InteractingSLE.WangWu.ReverseContactMartFilt

/-!
# Reverse-tail heights and descent from the glued probability space

Packet PROVE-WW-B27. A decreasing parametrization of the reverse line gives the
tail identity and a dense set of tail heights at positive rational reverse times.
Descent to the original space uses the composition-product almost-everywhere
theorem, which requires no measurability of the property being descended.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedTail

/-- A property depending only on the first coordinate descends from the glued space,
even when the property is not known to be measurable. -/
theorem ae_of_ae_glue_fst {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → A}
    (k : Kernel A B) [IsMarkovKernel k] (hX : Measurable X) {Q : Ω → Prop}
    (hQ : ∀ᵐ p ∂(glueMeasure P k X hX), Q p.1) : ∀ᵐ ω ∂P, Q ω := by
  have h := Measure.ae_ae_of_ae_compProd hQ
  filter_upwards [h] with ω hω
  exact hω.exists.choose_spec

/-- A reverse parametrization indexed by positive times, with all positive forward
heights attained. This records orientation as well as equality of ranges. -/
structure IsTailReversal (β γ : ℝ → ℂ) (a : ℝ → ℝ) : Prop where
  continuous : ContinuousOn a (Ioi 0)
  anti : StrictAntiOn a (Ioi 0)
  positive : ∀ s, 0 < s → 0 < a s
  surj : SurjOn a (Ioi 0) (Ioi 0)
  eq : ∀ s, 0 < s → β (a s) = negInv (γ s)

/-- A reverse prefix is exactly the closed forward tail above its tip height. -/
theorem IsTailReversal.image_Ioc {β γ : ℝ → ℂ} {a : ℝ → ℝ}
    (ha : IsTailReversal β γ a) {s : ℝ} (hs : 0 < s) :
    negInv '' (γ '' Ioc 0 s) = β '' Ici (a s) := by
  ext z
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨a t, ha.anti.antitoneOn ht.1 hs ht.2, ha.eq t ht.1⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨t, ht, he⟩ := ha.surj (lt_of_lt_of_le (ha.positive s hs) hb)
    have hts : t ≤ s := by
      by_contra hn
      have hlt := ha.anti hs ht (lt_of_not_ge hn)
      rw [he] at hlt
      exact (not_lt_of_ge hb) hlt
    refine ⟨γ t, ⟨t, ⟨ht, hts⟩, rfl⟩, ?_⟩
    rw [← ha.eq t ht, he]

/-- Positive rational reverse times give a set of forward heights dense above zero. -/
theorem IsTailReversal.isDenseAbove {β γ : ℝ → ℂ} {a : ℝ → ℝ}
    (ha : IsTailReversal β γ a) : Descent.IsDenseAbove (a '' {s : ℝ | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = s}) := by
  intro x y hx hxy
  obtain ⟨t, ht, hat⟩ := ha.surj (show 0 < (x + y) / 2 by linarith)
  have hc : ContinuousAt a t := (ha.continuous t ht).continuousAt (isOpen_Ioi.mem_nhds ht)
  have hnear : {r | 0 < r ∧ a r ∈ Ioo x y} ∈ 𝓝 t := by
    exact inter_mem (Ioi_mem_nhds ht) (hc.preimage_mem_nhds (Ioo_mem_nhds (by rw [hat]; linarith)
      (by rw [hat]; linarith)))
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hnear
  obtain ⟨q, hlq, hqu⟩ := exists_rat_btwn (hl.trans hu)
  have hq := hsub ⟨hlq, hqu⟩
  refine ⟨a q, ⟨q, ⟨q, ?_, rfl⟩, rfl⟩, hq.2⟩
  exact_mod_cast hq.1

/-- Transfer the rational reverse-time conclusions into the two tail conditions on
the original space. The geometric tail identity is supplied pointwise by `a`. -/
theorem ae_tail_conditions_of_glue {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → A}
    (k : Kernel A B) [IsMarkovKernel k] (hX : Measurable X)
    {α β : Ω → ℝ → ℂ} {γ : B → ℝ → ℂ}
    (ha : ∀ᵐ p ∂(glueMeasure P k X hX), ∃ a : ℝ → ℝ, IsTailReversal (β p.1) (γ p.2) a ∧
      ∀ s : ℚ, 0 < s → Descent.NoRightFirstContact (α p.1) (β p.1) (a s) ∧
        Descent.NoRightEscape (α p.1) (β p.1) (a s)) :
    ∀ᵐ ω ∂P, ∃ D : Set ℝ, Descent.IsDenseAbove D ∧ ∀ b ∈ D,
      Descent.NoRightFirstContact (α ω) (β ω) b ∧ Descent.NoRightEscape (α ω) (β ω) b := by
  apply ae_of_ae_glue_fst k hX
  filter_upwards [ha] with p hp
  obtain ⟨a, har, has⟩ := hp
  refine ⟨_, har.isDenseAbove, ?_⟩
  rintro b ⟨s, ⟨q, hq, rfl⟩, rfl⟩
  exact has q hq

end InteractingSLE.WangWu.SeedTail

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCMain
import InteractingSLE.Spec.Supplement.RLCG3Source

/-!
# W5's interior case from Lemma G3 in the source's form (ruling R60, rewiring)

Packet PROVE-G3SRC, the rewiring of G3's consumers. Sources: Lemma G3, hypothesis 4 (supplement p. 493: "The closure of
`U` meets the real line only in two disjoint intervals on which the respective canonical seed germs just stated hold"),
W5's proof (p. 535: "In the old joint chart the entire selected fresh portions therefore fit in a bounded buffer of the
relevant comparison theorem").

The interior case of W5 compares chart prefixes which stay in `ℍ` after their seeds. Such a prefix from the seed `y`
lies in a **per-seed buffer** `{‖z‖ < R ∧ (ε' < Im z ∨ ‖z − y‖ < ε)}`, whose closure meets `ℝ` only in `[y − ε, y + ε]`
(inside the seed collar). So the source-form G3 (`RLC.G3SourceStatement`) suffices there; the single buffer of
PROVE-RLC-B (`RLC.bufferSet`, around both seeds) is not needed.

* `ae_isChartCompletable_of_buffers_src`: `RLC.ae_isChartCompletable_of_buffer` with per-seed buffers and the
  source-form G3;
* `seedBufferSet`, `ae_chartInteriorCompletion_of_hasSeedGerms_src`: PROVE-RLC-B's buffer selection
  (`RLC.ae_chartInteriorCompletion_of_hasSeedGerms`) with per-seed buffers;
* `retainedChartCompletionStatement_of_restart_src`, `retainedChartCompletionStatement_of_param_src`: the retained chart
  completion (`RLC.RetainedChartCompletionStatement`) from G2, the source-form G3 and the retained-pair restart (the
  proof of `RLC.retainedChartCompletionStatement_of_restart`, with the buffer selection above);
* `retainedLocalCompletionLocStatement_of_param_src`, **`w5Statement_of_realLoc_param_src`**,
  **`w5Statement_of_chartReal_param_src`**: Theorem W5 with `RLC.G3ChartComparisonStatement` replaced by
  `RLC.G3SourceStatement` (the real-contact case stays a separate input, as in `RLC.w5Statement_of_chartReal_param`).

R43/R48: this serves Theorem 1.5 only.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Restart

/-! ### The single-space transfer with per-seed buffers -/

/-- **Completability of the stopped chart pair from G2, G2b and the source-form G3** (`ae_isChartCompletable_of_buffer`
with per-seed buffers). Chart datum `c` (jumps `J`) which agrees, with its jumps, with the four-height data
`g2Data κ θ₁ θ₂ 0 m w` on an open set `O`; buffers `V₁` (for the flow from `w`) and `V₂` (for the flow from `0`) whose
closures meet `ℝ` only in closed intervals inside `O`. Almost surely every pair of prefixes within the exit times from
the respective buffers is completable. -/
theorem ae_isChartCompletable_of_buffers_src (hG2 : G2ReferenceStatement.{u}) (hG3 : G3SourceStatement.{u})
    {κ θ₁ θ₂ m w : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (h0m : 0 < m) (hmw : m < w)
    {c : ℝ → ℝ} {J : Finset ℝ} (hc : IsPiecewiseConstantBoundaryData c J) {O : Set ℝ} (hO : IsOpen O)
    (hcO : ∀ x ∈ O, c x = g2Data κ θ₁ θ₂ 0 m w x) (hJO : ∀ x ∈ O, x ∈ J ↔ x ∈ ({0, m, w} : Finset ℝ))
    {V₁ V₂ : Set ℂ} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hV₁b : Bornology.IsBounded V₁)
    (hV₂b : Bornology.IsBounded V₂) {a₁ c₁ a₂ c₂ : ℝ} (hI₁ : Icc a₁ c₁ ⊆ O) (hI₂ : Icc a₂ c₂ ⊆ O)
    (hV₁I : ∀ z ∈ closure V₁, z.im = 0 → z.re ∈ Icc a₁ c₁) (hV₂I : ∀ z ∈ closure V₂, z.im = 0 → z.re ∈ Icc a₂ c₂)
    {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
    (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (hH : IsGFFWithBoundaryData Q₀ H₀ c J)
    (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (h₁ : IsFlowLine κ c J w θ₁ Q₀ H₀ Γ₁ U₁)
    (h₂ : IsFlowLine κ c J 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ exitTime V₁ (Γ₁ x) (U₁ x) →
      (s₂ : ℝ≥0∞) ≤ exitTime V₂ (Γ₂ x) (U₂ x) → IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
  obtain ⟨Z, Ĥ, α₁, α₂, ζ₁, ζ₂, hZm, hZpos, hZ1, hĤ, hα₁, hα₂, hagree⟩ :=
    hG3 κ hκ hκ4 c (g2Data κ θ₁ θ₂ 0 m w) J {0, m, w} hc (isPiecewiseConstant_g2Data κ θ₁ θ₂ 0 m w) O hO hcO hJO
      V₁ V₂ hV₁ hV₂ hV₁b hV₂b a₁ c₁ a₂ c₂ hI₁ hI₂ hV₁I hV₂I w 0 θ₁ θ₂ Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  set Q := Q₀.withDensity fun x => ENNReal.ofReal (Z x) with hQ
  have hQprob : IsProbabilityMeasure Q := by
    constructor
    have hint : Integrable Z Q₀ := Integrable.of_integral_ne_zero (by rw [hZ1]; exact one_ne_zero)
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (hZpos.mono fun x hx => hx.le), hZ1, ENNReal.ofReal_one]
  have hPQ : Q₀ ≪ Q := by
    refine withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp_aemeasurable hZm) ?_
    filter_upwards [hZpos] with x hx
    exact (ENNReal.ofReal_pos.2 hx).ne'
  have hRef := hG2 κ hκ hκ4 θ₁ θ₂ 0 m w hθ h0m hmw Q Ĥ hĤ α₁ α₂ ζ₁ ζ₂ hα₁ hα₂
  have hRef₀ : ∀ᵐ x ∂Q₀, _ := hPQ.ae_le hRef
  have hz₁ : ∀ᵐ x ∂Q₀, α₁ x 0 = w := hPQ.ae_le (Supp9.ae_apply_zero_of_isFlowLine hα₁)
  have hz₂ : ∀ᵐ x ∂Q₀, α₂ x 0 = 0 := hPQ.ae_le (Supp9.ae_apply_zero_of_isFlowLine hα₂)
  filter_upwards [hRef₀, hagree, hz₁, hz₂] with x hRx hAx hz hz' s₁ s₂ hs₁ hs₂
  obtain ⟨-, -, hc₁, hc₂, hord, hv₁, hv₂⟩ := hRx
  obtain ⟨⟨-, ha₁⟩, ⟨-, ha₂⟩⟩ := hAx
  refine ⟨α₁ x, α₂ x, ⟨hc₁.1, hc₁.2.1, hc₁.2.2.1, hc₁.2.2.2.1, fun t ht => (ha₁ t ?_).symm⟩,
    ⟨hc₂.1, hc₂.2.1, hc₂.2.2.1, hc₂.2.2.2.1, fun t ht => (ha₂ t ?_).symm⟩, hord, ?_, ?_⟩
  · exact (ENNReal.coe_le_coe.2 ht).trans hs₁
  · exact (ENNReal.coe_le_coe.2 ht).trans hs₂
  · have h0 : Γ₁ x 0 = α₁ x 0 := ha₁ 0 (by simp)
    rw [h0, hz]; exact hv₂
  · have h0 : Γ₂ x 0 = α₂ x 0 := ha₂ 0 (by simp)
    rw [h0, hz']; exact_mod_cast hv₁

/-! ### Per-seed buffers -/

/-- The per-seed buffer `{‖z‖ < R ∧ (ε' < Im z ∨ ‖z − y‖ < ε)}` around a chart prefix from the seed `y`. -/
def seedBufferSet (y ε' ε R : ℝ) : Set ℂ := {z | ‖z‖ < R ∧ (ε' < z.im ∨ ‖z - y‖ < ε)}

theorem isOpen_seedBufferSet (y ε' ε R : ℝ) : IsOpen (seedBufferSet y ε' ε R) :=
  (isOpen_lt continuous_norm continuous_const).inter ((isOpen_lt continuous_const Complex.continuous_im).union
    (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const))

theorem isBounded_seedBufferSet (y ε' ε R : ℝ) : Bornology.IsBounded (seedBufferSet y ε' ε R) :=
  (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset fun z hz => by
    rw [mem_ball, dist_zero_right]; exact hz.1

/-- The real points of the closure of a per-seed buffer lie within `ε` of the seed. -/
theorem re_mem_of_mem_closure_seedBufferSet {y ε' ε R : ℝ} (hε' : 0 < ε') {z : ℂ}
    (hz : z ∈ closure (seedBufferSet y ε' ε R)) (hz0 : z.im = 0) : z.re ∈ Icc (y - ε) (y + ε) := by
  have hF : IsClosed {z : ℂ | ε' ≤ z.im ∨ ‖z - y‖ ≤ ε} :=
    (isClosed_le continuous_const Complex.continuous_im).union
      (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
  have hsub : seedBufferSet y ε' ε R ⊆ {z : ℂ | ε' ≤ z.im ∨ ‖z - y‖ ≤ ε} := by
    rintro z ⟨-, h | h⟩
    · exact Or.inl h.le
    · exact Or.inr h.le
  rcases closure_minimal hsub hF hz with h | h
  · linarith
  · have h' := Complex.abs_re_le_norm (z - y)
    simp only [Complex.sub_re, Complex.ofReal_re] at h'
    have h'' := (abs_le.1 (h'.trans h))
    exact ⟨by linarith [h''.1], by linarith [h''.2]⟩

/-! ### The chart interior completion property at one datum, per-seed buffers -/

/-- **The chart interior completion property at a datum with canonical seed germs, from the source-form G3**
(`RLC.ae_chartInteriorCompletion_of_hasSeedGerms` with per-seed buffers): for the GFF with the datum's word and its
angle-`θ₁` flow from `w > 0` and angle-`θ₂` flow from `0`, almost surely every pair of available prefixes which stay in
`ℍ` after their seeds is completable. Each prefix lies in a rational per-seed buffer around its own seed, whose closure
meets `ℝ` only inside the seed collar. -/
theorem ae_chartInteriorCompletion_of_hasSeedGerms_src (hG2 : G2ReferenceStatement.{u})
    (hG3 : G3SourceStatement.{u}) {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    {c : BoundaryWord × ℝ} (hc : c ∈ HasSeedGerms κ θ₁ θ₂) {S : Type u} [MeasurableSpace S] (Q₀ : Measure S)
    [IsProbabilityMeasure Q₀] (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens)
    (hH : IsGFFWithBoundaryData Q₀ H₀ c.1.fn c.1.jumps) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞)
    (h₁ : IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ Q₀ H₀ Γ₁ U₁) (h₂ : IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, ChartInteriorCompletion (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x) := by
  obtain ⟨q, q₁, q₂, hS⟩ := hc
  set w : ℝ := c.2 with hwdef
  have hw : 0 < w := hS.w_pos
  have hq : (0 : ℝ) < q := hS.1
  have hqq₁ : (q : ℝ) < q₁ := hS.2.1
  have hq₁w : (q₁ : ℝ) < w := hS.2.2.1
  have hwq₂ : w < (q₂ : ℝ) := hS.2.2.2.1
  have hlam := Sec4.sleLambda_pos hκ
  set ε₀ : ℝ := min (min (q : ℝ) (w - q₁)) (min ((q₂ : ℝ) - w) (w / 4)) with hε₀
  have hε₀q : ε₀ ≤ q := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀1 : ε₀ ≤ w - q₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀2 : ε₀ ≤ q₂ - w := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀4 : ε₀ ≤ w / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hε₀pos : 0 < ε₀ := lt_min (lt_min hq (by linarith)) (lt_min (by linarith) (by linarith))
  set O : Set ℝ := {x | |x| < ε₀ ∨ |x - w| < ε₀} with hOdef
  have hO : IsOpen O := (isOpen_lt (continuous_abs.comp continuous_id) continuous_const).union
    (isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const)
  have hOmem : ∀ x ∈ O, (-(q : ℝ) < x ∧ x < q) ∨ ((q₁ : ℝ) < x ∧ x < q₂) := by
    rintro x (hx | hx) <;> rw [abs_lt] at hx
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  set J : Finset ℝ := c.1.jumps with hJ
  have h0J : (0 : ℝ) ∈ J := (hS.mem_jumps_iff hκ (Or.inl ⟨by linarith, hq⟩)).2 (Or.inl rfl)
  have hwJ : w ∈ J := (hS.mem_jumps_iff hκ (Or.inr ⟨hq₁w, hwq₂⟩)).2 (Or.inr rfl)
  -- the datum with the reference values at the two seeds (values at jump points are immaterial)
  set c' : ℝ → ℝ := fun x => if x = 0 ∨ x = w then g2Data κ θ₁ θ₂ 0 (w / 2) w x else c.1.fn x with hc'
  have hoff : ∀ y ∉ J, c' y = c.1.fn y := fun y hy => by
    have : ¬ (y = 0 ∨ y = w) := by rintro (rfl | rfl) <;> contradiction
    simp only [hc', this, ite_false]
  have hoff' : ∀ y ∉ (J : Set ℝ), c' y = c.1.fn y := fun y hy => hoff y hy
  have hpc : IsPiecewiseConstantBoundaryData c' J := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => hy (h ▸ h0J)
    have hyw : y ≠ w := fun h => hy (h ▸ hwJ)
    filter_upwards [c.1.isPiecewiseConstantBoundaryData y hy, eventually_ne_nhds hy0, eventually_ne_nhds hyw]
      with z hz hz0 hzw
    have : ¬ (z = 0 ∨ z = w) := by rintro (h | h) <;> contradiction
    rw [hoff y hy]
    simp only [hc', this, ite_false]
    exact hz
  have hcO : ∀ x ∈ O, c' x = g2Data κ θ₁ θ₂ 0 (w / 2) w x := by
    intro x hx
    by_cases hx0w : x = 0 ∨ x = w
    · simp only [hc', hx0w, ite_true]
    simp only [hc', hx0w, ite_false]
    push Not at hx0w
    rcases hx with hx | hx <;> rw [abs_lt] at hx
    · rcases lt_or_gt_of_ne hx0w.1 with hneg | hpos
      · rw [hS.fn_neg (by linarith) hneg]; simp [g2Data, hneg]
      · rw [hS.fn_pos hpos (by linarith)]
        have h1 : ¬ x < 0 := not_lt.2 hpos.le
        have h2 : x < w / 2 := by linarith
        simp [g2Data, h1, h2]
    · rcases lt_or_gt_of_ne hx0w.2 with hlt | hgt
      · rw [hS.fn_left (by linarith) hlt]
        have h1 : ¬ x < 0 := by linarith
        have h2 : ¬ x < w / 2 := by linarith
        simp [g2Data, h1, h2, hlt]
      · rw [hS.fn_right hgt (by linarith)]
        have h1 : ¬ x < 0 := by linarith
        have h2 : ¬ x < w / 2 := by linarith
        have h3 : ¬ x < w := not_lt.2 hgt.le
        simp [g2Data, h1, h2, h3]
  have hJO : ∀ x ∈ O, x ∈ J ↔ x ∈ ({0, w / 2, w} : Finset ℝ) := by
    intro x hx
    rw [hS.mem_jumps_iff hκ (hOmem x hx)]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl h
      · exfalso
        rcases hx with hx | hx <;> rw [abs_lt, h] at hx <;> linarith [hx.1, hx.2]
      · exact Or.inr h
  have hH' : IsGFFWithBoundaryData Q₀ H₀ c' J := (isGFFWithBoundaryData_congr Q₀ H₀ hoff').2 hH
  have h₁' : IsFlowLine κ c' J w θ₁ Q₀ H₀ Γ₁ U₁ := (isFlowLine_congr_of_eqOn hoff).2 h₁
  have h₂' : IsFlowLine κ c' J 0 θ₂ Q₀ H₀ Γ₂ U₂ := (isFlowLine_congr_of_eqOn hoff).2 h₂
  -- the comparison on every rational pair of per-seed buffers
  have hall : ∀ᵐ x ∂Q₀, ∀ r : ℚ × ℚ × ℚ, 0 < (r.1 : ℝ) → 0 < (r.2.1 : ℝ) → (r.2.1 : ℝ) < ε₀ →
      ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ exitTime (seedBufferSet w r.1 r.2.1 r.2.2) (Γ₁ x) (U₁ x) →
        (s₂ : ℝ≥0∞) ≤ exitTime (seedBufferSet 0 r.1 r.2.1 r.2.2) (Γ₂ x) (U₂ x) →
        IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
    refine ae_all_iff.2 fun r => ?_
    by_cases hr : 0 < (r.1 : ℝ) ∧ 0 < (r.2.1 : ℝ) ∧ (r.2.1 : ℝ) < ε₀
    · have hI₁ : Icc (w - r.2.1) (w + r.2.1) ⊆ O := fun x hx =>
        Or.inr (abs_lt.2 ⟨by linarith [hx.1, hr.2.2], by linarith [hx.2, hr.2.2]⟩)
      have hI₂ : Icc ((0 : ℝ) - r.2.1) (0 + r.2.1) ⊆ O := fun x hx =>
        Or.inl (abs_lt.2 ⟨by linarith [hx.1, hr.2.2], by linarith [hx.2, hr.2.2]⟩)
      filter_upwards [ae_isChartCompletable_of_buffers_src hG2 hG3 hκ hκ4 hθ (half_pos hw) (half_lt_self hw) hpc hO
        hcO hJO (isOpen_seedBufferSet _ _ _ _) (isOpen_seedBufferSet _ _ _ _) (isBounded_seedBufferSet _ _ _ _)
        (isBounded_seedBufferSet _ _ _ _) hI₁ hI₂ (fun z hz hz0 => re_mem_of_mem_closure_seedBufferSet hr.1 hz hz0)
        (fun z hz hz0 => re_mem_of_mem_closure_seedBufferSet hr.1 hz hz0) Q₀ H₀ hH' Γ₁ Γ₂ U₁ U₂ h₁' h₂']
        with x hx _ _ _
      exact hx
    · exact Eventually.of_forall fun x h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hr
  filter_upwards [hall, Supp9.ae_apply_zero_of_isFlowLine h₁, Supp9.ae_apply_zero_of_isFlowLine h₂,
    Sec7.ae_continuousOn_of_isFlowLine h₁, Sec7.ae_continuousOn_of_isFlowLine h₂] with x hx z₁ z₂ k₁ k₂
  intro s₁ s₂ hs₁ hs₂ i₁ i₂
  have cont₁ : ContinuousOn (Γ₁ x) (Iic s₁) := k₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hs₁.le
  have cont₂ : ContinuousOn (Γ₂ x) (Iic s₂) := k₂.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hs₂.le
  obtain ⟨ε, hε0, hεε₀⟩ := exists_rat_btwn hε₀pos
  obtain ⟨e₁, he₁, hp₁⟩ := exists_rat_im_of_prefix cont₁ z₁ i₁ hε0
  obtain ⟨e₂, he₂, hp₂⟩ := exists_rat_im_of_prefix cont₂ z₂ i₂ hε0
  obtain ⟨R₁, hR₁⟩ := exists_rat_norm_lt_of_prefix cont₁
  obtain ⟨R₂, hR₂⟩ := exists_rat_norm_lt_of_prefix cont₂
  have he : (0 : ℝ) < ((min e₁ e₂ : ℚ) : ℝ) := by push_cast; exact lt_min he₁ he₂
  have mem₁ : ∀ t ≤ s₁, Γ₁ x t ∈ seedBufferSet w (min e₁ e₂ : ℚ) ε (max R₁ R₂ : ℚ) := by
    intro t ht
    refine ⟨lt_of_lt_of_le (hR₁ t ht) (by push_cast; exact le_max_left _ _), ?_⟩
    rcases hp₁ t ht with h | h
    · exact Or.inr h
    · exact Or.inl (lt_of_le_of_lt (by push_cast; exact min_le_left _ _) h)
  have mem₂ : ∀ t ≤ s₂, Γ₂ x t ∈ seedBufferSet 0 (min e₁ e₂ : ℚ) ε (max R₁ R₂ : ℚ) := by
    intro t ht
    refine ⟨lt_of_lt_of_le (hR₂ t ht) (by push_cast; exact le_max_right _ _), ?_⟩
    rcases hp₂ t ht with h | h
    · exact Or.inr h
    · exact Or.inl (lt_of_le_of_lt (by push_cast; exact min_le_right _ _) h)
  exact hx (min e₁ e₂, ε, max R₁ R₂) he hε0 hεε₀ s₁ s₂ (le_exitTime hs₁ mem₁) (le_exitTime hs₂ mem₂)

/-! ### The retained chart completion from the source-form G3 -/

section Chart

open Supp7 Supp9D

/-- **`RetainedChartCompletionStatement` from G2 (+ G2b), the source-form G3 and the retained-pair restart** (the proof
of `RLC.retainedChartCompletionStatement_of_restart`, with the per-seed buffer selection
`ae_chartInteriorCompletion_of_hasSeedGerms_src`). -/
theorem retainedChartCompletionStatement_of_restart_src (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3SourceStatement.{0}) (hR : RetainedPairRestartStatement.{u}) :
    RetainedChartCompletionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨d, hd, hu, hr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ u r
  subst hu hr
  obtain ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hker, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  have := hK
  obtain ⟨-, hU₁m, hU₂m, hΓ₁m, hΓ₂m, hΓ₁c, hΓ₂c⟩ := hco
  -- (1) the chart position of the first tip is positive
  have F1 : ∀ᵐ ω ∂P, ω ∈ M → 0 < (β ω).2 :=
    (ae_restrict_iff' hM).1 (ae_of_ae_map hβ.aemeasurable (hker.mono fun c hc => hc.1))
  -- (2) the chart seeds
  have F2 : ∀ᵐ ω ∂P, ω ∈ M → Γ₁ (X ω) 0 = ((β ω).2 : ℂ) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | Γ₁ p.2 0 = (p.1.2 : ℂ)} :=
      measurableSet_eq_fun ((hΓ₁m 0).comp measurable_snd)
        (Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst))
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => Supp9.ae_apply_zero_of_isFlowLine hc.2.2.1)
  have F3 : ∀ᵐ ω ∂P, ω ∈ M → Γ₂ (X ω) 0 = ((0 : ℝ) : ℂ) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | Γ₂ p.2 0 = ((0 : ℝ) : ℂ)} :=
      measurableSet_eq_fun ((hΓ₂m 0).comp measurable_snd) measurable_const
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => Supp9.ae_apply_zero_of_isFlowLine hc.2.2.2)
  -- (3) a wrong side at the first tip kills the first continuation
  have F4 : ∀ᵐ ω ∂P, ω ∈ M → (β ω ∈ BadSeed κ θ₁ → U₁ (X ω) = 0) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | p.1 ∈ BadSeed κ θ₁ → U₁ p.2 = 0} := by
      have e : {p : (BoundaryWord × ℝ) × S | p.1 ∈ BadSeed κ θ₁ → U₁ p.2 = 0} =
          (Prod.fst ⁻¹' BadSeed κ θ₁)ᶜ ∪ {p | U₁ p.2 = 0} := by
        ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
      rw [e]
      exact ((measurableSet_badSeed κ θ₁).preimage measurable_fst).compl.union
        (measurableSet_eq_fun (hU₁m.comp measurable_snd) measurable_const)
    refine ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => ?_)
    by_cases hcb : c ∈ BadSeed κ θ₁
    · filter_upwards [ae_eq_zero_of_mem_badSeed hκ hcb hc.2.2.1] with s hs _ using hs
    · exact Eventually.of_forall fun s h' => absurd h' hcb
  -- (4) the chart interior completion property, integrated over the datum
  have hCICum : LQGMetric.UMeasurableSet {x : S | ChartInteriorCompletion (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x)} :=
    uMeasurableSet_chartInteriorCompletion hU₁m hU₂m hΓ₁m hΓ₂m hΓ₁c hΓ₂c
  have F5 : ∀ᵐ ω ∂P, ω ∈ M → (β ω ∈ HasSeedGerms κ θ₁ θ₂ →
      ChartInteriorCompletion (Γ₁ (X ω)) (U₁ (X ω)) (Γ₂ (X ω)) (U₂ (X ω))) := by
    have hE : LQGMetric.UMeasurableSet {p : (BoundaryWord × ℝ) × S | p.1 ∈ HasSeedGerms κ θ₁ θ₂ →
        ChartInteriorCompletion (Γ₁ p.2) (U₁ p.2) (Γ₂ p.2) (U₂ p.2)} := by
      have e : {p : (BoundaryWord × ℝ) × S | p.1 ∈ HasSeedGerms κ θ₁ θ₂ →
          ChartInteriorCompletion (Γ₁ p.2) (U₁ p.2) (Γ₂ p.2) (U₂ p.2)} =
          (Prod.fst ⁻¹' HasSeedGerms κ θ₁ θ₂)ᶜ ∪
            Prod.snd ⁻¹' {x : S | ChartInteriorCompletion (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x)} := by
        ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
      rw [e]
      exact (LQGMetric.UMeasurableSet.of_measurableSet
        ((measurableSet_hasSeedGerms κ θ₁ θ₂).preimage measurable_fst)).compl.union
        (hCICum.preimage measurable_snd)
    refine ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw hE (hker.mono fun c hc => ?_)
    by_cases hcg : c ∈ HasSeedGerms κ θ₁ θ₂
    · filter_upwards [ae_chartInteriorCompletion_of_hasSeedGerms_src hG2 hG3 hκ hκ4 hθ hcg (K c) H₀ hc.2.1 Γ₁ Γ₂
        U₁ U₂ hc.2.2.1 hc.2.2.2] with s hs _ using hs
    · exact Eventually.of_forall fun s h' => absurd h' hcg
  refine ⟨fun ω => H₀ (X ω), fun ω => Γ₁ (X ω), fun ω => Γ₂ (X ω), fun ω => U₁ (X ω), fun ω => U₂ (X ω),
    fun ω => (β ω).2, ?_⟩
  filter_upwards [hpath, hag, F1, F2, F3, F4, F5, Sec7.ae_continuousOn_of_isFlowLine hη₁,
    Sec7.ae_continuousOn_of_isFlowLine hη₂, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁]
    with ω hω hagω f1 f2 f3 f4 f5 k₁ k₂ i₁ hord
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
  obtain ⟨hMω, hHX, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩, ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂, hH₂⟩,
    hword⟩ := hω hord
  have hg := hd.good ω (RetData.E_subset_G hE)
  obtain ⟨-, hC⟩ := hd.isRetChart hE
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have hdom := activeDomain_congr_Icc e₁ e₂
  have htip : d.η₂ ω d.r = η₂ ω d.r := ha₂ d.r le_rfl
  have htip₁ : d.η₁ ω d.u = η₁ ω d.u := ha₁ d.u le_rfl
  -- the joint chart (the proof of `RLC.jointRetainedChartStatement_of_restart`)
  have htr := hd.isChartTransport_chartField κ h ω
  rw [RetData.chart_of_mem hE, ← hHX] at htr
  have hJ : IsJointRetainedChart κ (h ω) (H₀ (X ω)) (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r (Γ₁ (X ω)) (Γ₂ (X ω))
      (U₁ (X ω)) (U₂ (X ω)) := by
    refine ⟨d.fwd ω, d.inv ω, d.lift ω, c₁, c₂, σ₁, σ₂, ?_, ?_, hC.fwd_inv, ?_, ?_, ?_, htr,
      hC.continuousOn_inv, hC.2.2.2.2.2.2.2.2.2.1, ?_, hσ₁, hmono₁, himg₁, hσ₂, hmono₂, himg₂,
      fun s hs => ⟨hpth₁ s hs, hH₁ s hs⟩, fun s hs => ⟨hpth₂ s hs, hH₂ s hs⟩, ?_⟩
    · rw [← hdom, ← htip]; exact hC.isActiveChart hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.bijOn hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.inv_notMem hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.continuousOn_lift hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.deriv_eq hg.2.2.2.2.2.1
    · rw [← htip]; exact hC.inv_zero hg.2.2.2.2.2.1
    · intro s₁ s₂ hs₁ hs₂ he hA
      have hψ : d.inv ω (Γ₁ (X ω) s₁) = d.inv ω (Γ₂ (X ω) s₂) := by rw [← hpth₁ s₁ hs₁, ← hpth₂ s₂ hs₂, he]
      have hK : d.inv ω (Γ₁ (X ω) s₁) ∉ prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
        rw [prefixSet_congr_Icc e₁ e₂, ← hpth₁ s₁ hs₁]; exact hA
      exact eq_of_inv_eq_of_notMem hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 (hH₁ s₁ hs₁) (hH₂ s₂ hs₂) hψ hK
  have hW0 : 0 < (β ω).2 := f1 hMω
  have hΓ0 : Γ₁ (X ω) 0 = ((β ω).2 : ℂ) := f2 hMω
  have hΓ0' : Γ₂ (X ω) 0 = 0 := by rw [f3 hMω]; simp
  -- the inverse chart sends the first chart seed to the first tip
  have h00 : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₁ := by simp
  have hc₁0 : c₁ 0 = d.u := clock_zero hord.1.le hmono₁ himg₁
  have hψW : d.inv ω ((β ω).2 : ℂ) = d.η₁ ω d.u := by
    rw [htip₁, ← hc₁0, hpth₁ 0 h00, hΓ0]
  -- the first continuation runs for a positive time, so the first seed has the right sides
  have hB : IsClosed (η₂ ω '' Icc 0 d.r) :=
    (isCompact_Icc.image_of_continuousOn (k₂.mono fun t ht =>
      (ENNReal.coe_le_coe.2 ht.2).trans hord.2.1.le)).isClosed
  have hU₁pos : 0 < U₁ (X ω) :=
    lt_of_lt_of_le (pos_of_isClock hord.1 k₁ i₁ hB hord.2.2.2.2.2.1 hmono₁ himg₁) hσ₁
  have hnb : β ω ∉ BadSeed κ θ₁ := fun hb' => (ne_of_gt hU₁pos) (f4 hMω hb')
  -- the retained word near the chart seeds
  have hi : InjOn (d.η₁ ω) (Icc 0 d.u) :=
    (i₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hord.1.le).congr e₁.symm
  have hpH : d.η₂ ω d.r ∈ H := by rw [htip]; exact hord.2.2.2.1
  have hp : d.η₂ ω d.r ∉ d.η₁ ω '' Icc 0 d.u := by rw [htip, e₁.image_eq]; exact hord.2.2.2.2.1
  have hqH : d.η₁ ω d.u ∈ H := by rw [htip₁]; exact hord.2.2.1
  have hq : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r := by rw [htip₁, e₂.image_eq]; exact hord.2.2.2.2.2.1
  obtain ⟨δ, hδ, h0g, hWg⟩ := exists_wordGerm_of_retChart hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hpH hp
    hg.2.2.2.2.2.2 hqH hq hi hψW (isRetainedWord_congr e₁.symm e₂.symm hword)
  have hgerm : β ω ∈ HasSeedGerms κ θ₁ θ₂ := by
    have := mem_hasSeedGerms_of_wordGerm (θ₂ := θ₂) hW0 hδ h0g hWg (by rwa [Prod.mk.eta])
    rwa [Prod.mk.eta] at this
  exact ⟨hJ, hW0, hΓ0, hΓ0', f5 hMω hgerm⟩

/-- **`RetainedChartCompletionStatement` from G2 (+ G2b), the source-form G3, Theorems 1.2 (param), 1.3 and
PROVE-CONDDET's two-tip P-side input** (R43: downstream of Theorem 1.2). -/
theorem retainedChartCompletionStatement_of_param_src (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3SourceStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetStatement.{u}) :
    RetainedChartCompletionStatement.{u} :=
  retainedChartCompletionStatement_of_restart_src hG2 hG3
    (retainedPairRestartStatement_of_clock (retainedKernelClockStatement_of_param h12p h13 hD))

end Chart

/-! ### Theorem W5 from the source-form G3 -/

/-- **The localized local completion from G2, the source-form G3, Theorems 1.2 (param), 1.3, PROVE-CONDDET's two-tip
input and the localized real-contact case.** -/
theorem retainedLocalCompletionLocStatement_of_param_src (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3SourceStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Restart.RetainedCanonCondDetStatement.{u})
    (hR : RetainedLocalCompletionRealLocStatement.{u}) : RetainedLocalCompletionLocStatement.{u} :=
  retainedLocalCompletionLocStatement_of_interior_of_realLoc
    (retainedLocalCompletionInteriorStatement_of_chart
      (retainedChartCompletionStatement_of_param_src hG2 hG3 h12p h13 hD)) hR

/-- **Theorem W5** (`Theorem15.W5Statement`) from Aux. lemma 25, W0a, W0b, Lemma 7.7, the joint G7 carrier, the
common-seed comparison, G2 (with G2b), **the source-form G3**, Theorems 1.2 (param) and 1.3, PROVE-CONDDET's two-tip
input and the localized real-contact case (`RLC.w5Statement_of_realLoc_param` with `G3SourceStatement`). -/
theorem w5Statement_of_realLoc_param_src (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0})
    (hJ : Supp9D.JointRetainedPairStatement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u})
    (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3SourceStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Restart.RetainedCanonCondDetStatement.{u})
    (hR : RetainedLocalCompletionRealLocStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_loc h25 hW0a hW0b h77 hJ
    (retainedLocalCompletionLocStatement_of_param_src hG2 hG3 h12p h13 hD hR) hCS

/-- **Theorem W5** from Aux. lemma 25, W0a, W0b, Lemma 7.7, the joint G7 carrier, the common-seed comparison, G2,
**the source-form G3**, Theorems 1.2 (param), 1.3, PROVE-CONDDET's two-tip input and the chart-level real-contact input
`RetainedChartRealCompletionStatement` (`RLC.w5Statement_of_chartReal_param` with `G3SourceStatement`). -/
theorem w5Statement_of_chartReal_param_src (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0})
    (hJ : Supp9D.JointRetainedPairStatement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u})
    (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3SourceStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Restart.RetainedCanonCondDetStatement.{u})
    (hC : RetainedChartRealCompletionStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_realLoc_param_src h25 hW0a hW0b h77 hJ hCS hG2 hG3 h12p h13 hD
    (retainedLocalCompletionRealLocStatement_of_chart hC)

end RLC

end InteractingSLE

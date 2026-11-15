/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2TcRead
import InteractingSLE.Spec.Supplement.SB2DrvEntrance
import InteractingSLE.Spec.Supplement.WalkInfVersion

/-!
# SB2(1)'s version half: the flow and its relative points read from the line marks

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The version's clock, driver and trace
are built from countably many readings of the line marks `D.absMarks T`:

* `etaRead D q`: the upper flow at the rational time `q`, read from the capped flow `η_⌈q⌉`;
  **`measurable_etaRead`** (`D.absMarks T`-measurable for `q ≤ T`) and **`ae_etaRead_eq`** (almost surely it is the
  flow itself at every rational time up to the lifetime, `D.version`);
* `relRead D I q`: the relative point at `q`, the past-measurable launch chart `I.chart` (the recentred version
  chart) applied to `etaRead D q`, masked by the chart domain; **`measurable_relRead`**,
  **`measurableSet_relGood`** (the event "the flow at `q` is in the chart domain") for `D.absMarks T`, `q ≤ T`.

Deterministic in the data; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vh

open Lv Restart Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- The upper flow at the rational time `q`, read from the capped flow `η_⌈q⌉`. -/
def etaRead (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (q : ℚ≥0) (ω : Ω) : ℂ :=
  D.ηc ⌈((q : ℝ≥0) : ℝ)⌉₊ ω q

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The reading at `q` is a line mark at every `T ≥ q`.** -/
theorem measurable_etaRead (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {q : ℚ≥0} {T : ℝ≥0∞}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) ≤ T) : Measurable[D.absMarks T] (etaRead D q) :=
  Tc.EntranceUnion.measurable_ηc_absMarks D _ hq

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The reading is the flow**, almost surely at every rational time up to the lifetime. -/
theorem ae_etaRead_eq (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω ∂P, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ ζ ω → etaRead D q ω = η ω q := by
  filter_upwards [D.version] with ω hv q hq
  unfold etaRead
  rw [hv]
  congr 1
  unfold capTime
  refine min_eq_left ?_
  have hn : ((q : ℝ≥0) : ℝ≥0∞) ≤ ((⌈((q : ℝ≥0) : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_natCast]
    exact Nat.le_ceil _
  have hfin : min (ζ ω) (((⌈((q : ℝ≥0) : ℝ)⌉₊ : ℕ) : ℝ≥0) : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
  exact le_min hq hn

/-- The relative point at the rational time `q`: the past-measurable launch chart applied to the reading, masked by
the chart domain. -/
def relRead (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (I : K2LaunchInputs κ b jumps P h E k u ψ) (q : ℚ≥0)
    (ω : Ω) : ℂ :=
  ({ω | etaRead D q ω ∈ (I.chart ω).dom}.indicator fun ω => (I.chart ω).1 (etaRead D q ω)) ω

/-- **The domain event at `q` is a line mark at every `T ≥ q`.** -/
theorem measurableSet_relGood (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {q : ℚ≥0} {T : ℝ≥0∞} (hq : ((q : ℝ≥0) : ℝ≥0∞) ≤ T) :
    MeasurableSet[D.absMarks T] {ω | etaRead D q ω ∈ (I.chart ω).dom} := by
  have hc := WalkInf.IsMeasChart.mono ((D.past_le_marks).trans (D.marks_le_absMarks T)) I.chart_measurable
  exact WalkInf.IsMeasChart.measurableSet_mem_dom_of_measurable hc (measurable_etaRead D hq)

/-- **The relative point at `q` is a line mark at every `T ≥ q`.** -/
theorem measurable_relRead (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {q : ℚ≥0} {T : ℝ≥0∞} (hq : ((q : ℝ≥0) : ℝ≥0∞) ≤ T) :
    Measurable[D.absMarks T] (relRead D I q) := by
  have hc := WalkInf.IsMeasChart.mono ((D.past_le_marks).trans (D.marks_le_absMarks T)) I.chart_measurable
  exact WalkInf.IsMeasChart.measurable_fwd_of_measurable hc (measurable_etaRead D hq)

end InteractingSLE.Theorem14.SB.Vh

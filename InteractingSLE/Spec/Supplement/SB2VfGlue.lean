/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VhRead
import InteractingSLE.Spec.Supplement.SB2LkRelMeas

/-!
# SB2(1)'s version half: good readings and the shifted chart domain

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The version's lift is read at rational
times through the past-measurable chart `I.chart = launchChart.recenter m` (a.s.); the records use the shifted
chart `c' = shiftChart (launchChart) u m` and the shifted domain `ℍ \ fill A'`. Glue:

* `ratQ i`: the `i`-th rational time as a `ℚ≥0` (`coe_ratQ`: it is `Lk.ratPt i`), so that the readings
  `Vh.relRead … (ratQ i)` are the values at `Lk.ratPt i` used by `Vc.measurable_of_dense_good_at`;
* **`mem_dom_recenter_iff`**: for a conformal `c` whose shift is a domain chart of `ℍ \ fill A'`, a point `z` is in
  the domain of `c.recenter m` iff `z − u ∈ ℍ \ fill A'`;
* **`recenter_fwd_eq_shift`**: there `(c.recenter m).1 z = c'(z − u)`;
* **`relRead_eq`**: hence a reading in the chart domain is the shifted chart's forward image of the shifted flow, the
  value of the record's lift at the good time (`Vh.lift_eq_fwd`).

Deterministic; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vf

open Lv

/-- The `i`-th rational time as a nonnegative rational. -/
def ratQ (i : ℕ) : ℚ≥0 := (Denumerable.ofNat ℚ i).toNNRat

/-- **`ratQ i` is the `i`-th rational time of `Lk.ratPt`.** -/
theorem coe_ratQ (i : ℕ) : ((ratQ i : ℚ≥0) : ℝ≥0) = Lk.ratPt i := by
  unfold ratQ Lk.ratPt
  set q : ℚ := Denumerable.ofNat ℚ i
  rcases le_total 0 q with hq | hq
  · ext
    have h : ((q.toNNRat : ℚ) : ℝ) = q := by rw [Rat.coe_toNNRat q hq]
    rw [Real.coe_toNNReal _ (by exact_mod_cast hq), ← h]
    norm_cast
  · rw [Rat.toNNRat_eq_zero.2 hq, Real.toNNReal_of_nonpos (by exact_mod_cast hq)]
    simp

/-- **The domain of the recentred chart is the shifted domain**, read at `z − u`. -/
theorem mem_dom_recenter_iff {c : Chart} (hc : c.IsConformal) {A' : Set ℂ} {u m : ℝ}
    (hD : IsDomainChart (H \ fillH A') (Lw.shiftChart c u m)) (z : ℂ) :
    z ∈ (c.recenter m).dom ↔ z - u ∈ H \ fillH A' := by
  rw [← SetLike.mem_coe, Chart.dom_recenter, hc.coe_dom, ← hD.coe_dom, hD.1.coe_dom]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w - m, ?_, ?_⟩
    · have := (Lw.add_real_mem_H_iff (w := w - m) m).2
      simpa using (Lw.add_real_mem_H_iff (w := w - (m : ℂ)) m).1 (by simpa using hw)
    · simp [Lw.shiftChart_inv]
  · rintro ⟨w, hw, hwe⟩
    refine ⟨w + m, (Lw.add_real_mem_H_iff m).2 hw, ?_⟩
    rw [Lw.shiftChart_inv] at hwe
    linear_combination hwe

/-- **The recentred chart is the shifted chart read at `z − u`.** -/
theorem recenter_fwd_eq_shift (c : Chart) (u m : ℝ) (z : ℂ) :
    (c.recenter m).1 z = (Lw.shiftChart c u m).1 (z - u) := by
  simp [Chart.recenter, Lw.shiftChart_fwd]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **A reading in the chart domain is the shifted chart's image of the shifted flow** (at a sample where the
version chart is the recentred launch chart and the reading is the flow). -/
theorem relRead_eq (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    {ω : Ω} {c : Chart} (hc : c.IsConformal) {A' : Set ℂ} {m : ℝ}
    (hD : IsDomainChart (H \ fillH A') (Lw.shiftChart c u m)) (hch : I.chart ω = c.recenter m) {q : ℚ≥0}
    (hη : Vh.etaRead D q ω = η ω q) (hgood : η ω q - u ∈ H \ fillH A') :
    Vh.relRead D I q ω = (Lw.shiftChart c u m).1 (η ω q - u) ∧ Vh.etaRead D q ω ∈ (I.chart ω).dom := by
  have hdom : Vh.etaRead D q ω ∈ (I.chart ω).dom := by
    rw [hch, mem_dom_recenter_iff hc hD, hη]; exact hgood
  refine ⟨?_, hdom⟩
  unfold Vh.relRead
  rw [Set.indicator_of_mem (show ω ∈ {ω | Vh.etaRead D q ω ∈ (I.chart ω).dom} from hdom), hch, hη,
    recenter_fwd_eq_shift]

/-- **A reading outside the shifted domain is not good.** -/
theorem relGood_iff (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    {ω : Ω} {c : Chart} (hc : c.IsConformal) {A' : Set ℂ} {m : ℝ}
    (hD : IsDomainChart (H \ fillH A') (Lw.shiftChart c u m)) (hch : I.chart ω = c.recenter m) {q : ℚ≥0}
    (hη : Vh.etaRead D q ω = η ω q) :
    Vh.etaRead D q ω ∈ (I.chart ω).dom ↔ η ω q - u ∈ H \ fillH A' := by
  rw [hch, mem_dom_recenter_iff hc hD, hη]

end InteractingSLE.Theorem14.SB.Vf

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WzUnb
import InteractingSLE.Spec.Sec7.Lemma75Bridge

/-!
# SB2(1)'s late (S) line mean, part 8: FIN's conclusion read back in the launch chart

Packet PROVE-T14-SB2DRV (round 10). FIN's union mean is applied in the coupling's coordinates: field
`h' = flowField u (ψχ) h` (`IsTranslateAddConst u (ψχ) h h'`), centred field `flowField u 0 (h − smoothDist u₀)`,
union mean `g' = flowField u 0 gU`, chart `Lw.shiftChart c u 0` with FIN's offset `0`. Its conclusion is about
`g' + smoothDist u₀' = g' + (h' − centred h')`; K2's (S) needs `gU + (h − h₀)` in the chart `c` with offset `ψχ`:

* `flowField_eq_add_oneDist`, `flowField_zero_add`, `flowField_zero_sub` (`flowField x a` is affine);
* `chartTransport_add_smul_oneDist`: a constant field moves into the chart offset (`∫ pushTest φ = ∫ φ`);
* `recenter_zero`;
* **`chartTransport_fin_back`**: `chartTransport (shiftChart c u 0) 1 0 k (flowField u 0 gU + (h' − flowField u 0 h₀))
  = chartTransport c 1 a₀ k (gU + (h − h₀))` when `h' = flowField u a₀ h`.

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.SB.Lv

/-- `flowField x a` is `flowField x 0` plus the constant field `a`. -/
theorem flowField_eq_add_oneDist (x a : ℝ) (X : DistOn upperHalfPlaneOpens) :
    Exist.flowField x a X = Exist.flowField x 0 X + a • Chart.oneDist := by
  ext φ
  simp only [Exist.flowField_apply, add_apply, smul_apply, Chart.oneDist_apply,
    zero_mul, add_zero, smul_eq_mul]

theorem flowField_zero_add (x : ℝ) (X Y : DistOn upperHalfPlaneOpens) :
    Exist.flowField x 0 (X + Y) = Exist.flowField x 0 X + Exist.flowField x 0 Y := by
  ext φ
  simp only [Exist.flowField_apply, add_apply, zero_mul, add_zero]

theorem flowField_zero_sub (x : ℝ) (X Y : DistOn upperHalfPlaneOpens) :
    Exist.flowField x 0 (X - Y) = Exist.flowField x 0 X - Exist.flowField x 0 Y := by
  ext φ
  simp only [Exist.flowField_apply, sub_apply, zero_mul, add_zero]

/-- **A constant field moves into the chart offset.** -/
theorem chartTransport_add_smul_oneDist {c : Chart} (hc : c.IsConformal) (a a' k : ℝ)
    (X : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    Chart.chartTransport hc 1 a k (X + a' • Chart.oneDist) φ = Chart.chartTransport hc 1 (a + a') k X φ := by
  have hone : Chart.oneDist (Chart.pushTest hc φ) = Chart.oneDist φ := by
    rw [Chart.oneDist_apply, Chart.oneDist_apply]
    have h := Chart.integral_mul_pushTest hc φ (fun _ => (1 : ℝ))
    simp only [one_mul] at h
    exact h
  rw [Chart.chartTransport_apply', Chart.chartTransport_apply', add_apply,
    smul_apply, hone, smul_eq_mul]
  ring

theorem recenter_zero (c : Chart) : c.recenter 0 = c := by
  obtain ⟨f, g, l⟩ := c
  simp only [Chart.recenter, Complex.ofReal_zero, sub_zero, add_zero]

/-- **FIN's conclusion read back in the launch chart**: the field `flowField u 0 gU + (h' − flowField u 0 h₀)` in the
seed-shifted chart with offset `0` is `gU + (h − h₀)` in the chart with offset `a₀`, when `h' = flowField u a₀ h`. -/
theorem chartTransport_fin_back {c : Chart} (hc : c.IsConformal) {u : ℝ} (hcs : (Lw.shiftChart c u 0).IsConformal)
    (a₀ k : ℝ) {gU h h₀ h' : DistOn upperHalfPlaneOpens} (hh' : h' = Exist.flowField u a₀ h)
    (φ : TestOn upperHalfPlaneOpens) :
    Chart.chartTransport hcs 1 0 k (Exist.flowField u 0 gU + (h' - Exist.flowField u 0 h₀)) φ =
      Chart.chartTransport hc 1 a₀ k (gU + (h - h₀)) φ := by
  have e : Exist.flowField u 0 gU + (h' - Exist.flowField u 0 h₀) =
      Exist.flowField u 0 (gU + (h - h₀)) + a₀ • Chart.oneDist := by
    subst hh'
    ext ψ
    simp only [Exist.flowField_apply, add_apply, sub_apply, smul_apply, Chart.oneDist_apply, smul_eq_mul,
      zero_mul, add_zero]
    ring
  rw [e, chartTransport_add_smul_oneDist hcs 0 a₀ k, zero_add,
    Shift.chartTransport_shiftChart_flowField hcs (hc.recenter 0),
    chartTransport_congr_chart (hc.recenter 0) hc (recenter_zero c)]

end InteractingSLE.Theorem14.SB.Lv

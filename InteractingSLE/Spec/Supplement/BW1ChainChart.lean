/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1ChainCf
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart
import InteractingSLE.Spec.Restart.RetAux79
import InteractingSLE.Spec.Supplement.BW1PropConfig

/-!
# The relative chain, part 6: the two readings of the conditional field

Packet PROVE-BW1-CHAIN. Proposition BW1's conclusion reads the field `h` in the state chart `L = g_A − W` and then
in the inversion `R(z) = −1/z` (`cfField`, the two transports of `SB.IsCondCounterflowDriverOn` and
`IsCenteredCounterflowDriver`). The relative configuration of BW1 (PROVE-BW1-PROP, `Q3Rel.IsRelConfigOff`) and the line
data live in the **counterflow frame**: the field `h′ = R_*h` (the frozen counterflow's own field) read in the
relative chart `Ψ = R ∘ L ∘ R` (`GW2JointKernel.jointChart`, `Ψ = relMap`, `Ψ⁻¹ = relInv`). This file proves that the
two readings agree, with the explicit additive offset `2πχ(16/κ)` (the inversion is an involution whose lift
`arg(−1/w) = π − arg w` adds `−2π`; cf. ruling R62):

* **`IsChartTransport.congr_chart`**: two conformal charts with the same inverse on `ℍ` whose lifts (read in `ℍ`)
  differ by a constant `δ` transport fields alike, up to the offset `k δ`;
* **`isChartTransport_trans_jointChart`**: `R.trans (jointChart w s)` and `(Chart.id.loewner w s).trans R` have the
  same inverse on `ℍ` and lifts differing by `2π`;
* **`chartTransport_jointChart_eq_cfField`**: `jointChart`-transport (coefficients `1, 2πχ(16/κ), χ(16/κ)`) of the
  counterflow-frame field `R_*h` (coefficients `−1, −πχ(κ), χ(16/κ)`) is `cfField κ` of `h` read in the Loewner chart.
  This is the identity `hXeq` of `BW1ChainMain.isCondCounterflowDriverOn_of_lineData` once the state chart is the
  Loewner chart of the piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Chain

open GW2JointKernel

/-- **Chart congruence with a constant lift shift.** If two conformal charts have the same inverse on `ℍ` and their
lifts read in `ℍ` differ by the constant `δ`, a transport in the first chart with coefficients `σ, a, k` is a
transport in the second with `σ, a − kδ, k`. -/
theorem IsChartTransport.congr_chart {c c' : Chart} (hc : c.IsConformal) (hc' : c'.IsConformal)
    (hinv : ∀ w ∈ H, c'.2.1 w = c.2.1 w) (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) (δ : ℝ)
    (hlift : ∀ w ∈ H, c'.2.2 (c'.2.1 w) = c.2.2 (c.2.1 w) + δ) {σ a k : ℝ} {h h' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport c σ a k h h') : IsChartTransport c' σ (a - k * δ) k h h' := by
  have hℓ' : ContinuousOn (fun w => c'.2.2 (c'.2.1 w)) H :=
    (hℓ.add continuousOn_const).congr fun w hw => hlift w hw
  have he : h' = Chart.chartTransport hc' σ (a - k * δ) k h := by
    ext φ'
    have hi1 : Integrable fun w => φ' w := φ'.continuous.integrable_of_hasCompactSupport φ'.hasCompactSupport
    have hi2 : Integrable fun w => c.2.2 (c.2.1 w) * φ' w :=
      InteractingSLE.integrable_mul_testOn_of_continuousOn hℓ φ'
    have hint : ∫ w, c'.2.2 (c'.2.1 w) * φ' w = (∫ w, c.2.2 (c.2.1 w) * φ' w) + δ * ∫ w, φ' w := by
      rw [← integral_const_mul, ← integral_add hi2 (hi1.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      by_cases hw : w ∈ H
      · change c'.2.2 (c'.2.1 w) * φ' w = c.2.2 (c.2.1 w) * φ' w + δ * φ' w
        rw [hlift w hw]
        ring
      · change c'.2.2 (c'.2.1 w) * φ' w = c.2.2 (c.2.1 w) * φ' w + δ * φ' w
        rw [InteractingSLE.testOn_eq_zero_of_notMem_H φ' hw]
        ring
    rw [ht.apply_eq hc, Chart.chartTransport_apply hc' (Chart.locallyIntegrableOn_of_continuousOn hℓ'),
      Chart.pushTest_congr hc hc' hinv, hint]
    ring
  rw [he]
  exact Chart.isChartTransport_chartTransport hc' (Chart.locallyIntegrableOn_of_continuousOn hℓ') _ _ _ _

section Joint

variable {w : ℝ → ℝ} {s : ℝ}

/-- The inversion is an involution of `ℂ` (with `0⁻¹ = 0`). -/
theorem infinitySourceChart_inv_inv (x : ℂ) : infinitySourceChart.2.1 (infinitySourceChart.2.1 x) = x := by
  change -(-x⁻¹)⁻¹ = x
  rw [inv_neg, inv_inv, neg_neg]

/-- **The relative joint chart after the inversion is the Loewner chart before it**: same inverse on `ℍ`. -/
theorem trans_jointChart_inv (v : ℂ) :
    (infinitySourceChart.trans (jointChart w s)).2.1 v =
      ((Chart.id.loewner w s).trans infinitySourceChart).2.1 v := by
  rw [jointChart_eq]
  simp only [Chart.trans_inv]
  exact infinitySourceChart_inv_inv _

/-- **The lifts differ by `2π`**: the lift of the Loewner chart followed by the inversion, read in `ℍ`, is the lift of
the inversion followed by the joint chart plus `2π` (`arg(−1/x) = π − arg x` at the inner inversion). -/
theorem trans_jointChart_lift (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {v : ℂ} (hv : v ∈ H) :
    ((Chart.id.loewner w s).trans infinitySourceChart).2.2
        (((Chart.id.loewner w s).trans infinitySourceChart).2.1 v) =
      (infinitySourceChart.trans (jointChart w s)).2.2 ((infinitySourceChart.trans (jointChart w s)).2.1 v) +
        2 * Real.pi := by
  have hR := Chart.isConformal_infinitySourceChart
  have hL := isConformal_loewner hw hw0 hs
  set R := infinitySourceChart with hRdef
  set L := Chart.id.loewner w s with hLdef
  have hJ : ((R.trans L).trans R).IsConformal := (hR.trans hL).trans hR
  have hu : R.2.1 v ∈ H := hR.2.1 hv
  have hx : L.2.1 (R.2.1 v) ∈ H := hL.2.1 hu
  have hJv : ((R.trans L).trans R).2.1 v ∈ H := hJ.2.1 hv
  rw [jointChart_eq, IsChartTransport.trans_lift_inv hL hu, IsChartTransport.trans_lift_inv hR hJv,
    IsChartTransport.trans_lift_inv (hR.trans hL) hu, IsChartTransport.trans_lift_inv hR hx]
  have e1 : ((R.trans L).trans R).2.1 v = R.2.1 (L.2.1 (R.2.1 v)) := by
    simp only [Chart.trans_inv]
  rw [e1, infinitySourceChart_inv_inv]
  have e2 : R.2.2 (R.2.1 (L.2.1 (R.2.1 v))) = -(2 * Real.pi) - R.2.2 (L.2.1 (R.2.1 v)) :=
    infinitySourceChart_lift_negInv hx
  rw [e2]
  ring

/-- The lift of the joint chart, read in `ℍ`, is continuous. -/
theorem continuousOn_jointChart_lift' (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    ContinuousOn (fun v => (jointChart w s).2.2 ((jointChart w s).2.1 v)) H := by
  have hR := Chart.isConformal_infinitySourceChart
  have hL := isConformal_loewner hw hw0 hs
  have hℓR := Chart.continuousOn_infinitySourceChart_lift
  have hℓL := continuousOn_loewner_lift hw hw0 hs
  rw [jointChart_eq]
  exact continuousOn_trans_lift (hR.trans hL) hR (continuousOn_trans_lift hR hL hℓR hℓL) hℓR

/-- **The two readings of the conditional field agree.** The counterflow-frame field `R_*h` (coefficients
`−1, −πχ(κ), χ(16/κ)`) read in the relative joint chart with coefficients `1, 2πχ(16/κ), χ(16/κ)` is `h` read in the
Loewner chart with the flow rule and then in the inversion (`cfField κ`). -/
theorem chartTransport_jointChart_eq_cfField {κ : ℝ} (hκ : 0 < κ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (h : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport (isConformal_jointChart hw hw0 hs) 1 (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ))
        (Chart.chartTransport Chart.isConformal_infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h) =
      cfField κ (isConformal_loewner hw hw0 hs) h := by
  have hR := Chart.isConformal_infinitySourceChart
  have hL := isConformal_loewner hw hw0 hs
  have hJ := isConformal_jointChart hw hw0 hs
  have hℓR := Chart.continuousOn_infinitySourceChart_lift
  have hℓL := continuousOn_loewner_lift hw hw0 hs
  have hℓJ := continuousOn_jointChart_lift' hw hw0 hs
  have hχ : chiC (16 / κ) = -1 * chiC κ := by rw [Sec4.chiC_sixteen_div hκ]; ring
  -- the reading through the inversion and the joint chart
  have h1 := Chart.isChartTransport_chartTransport hR (Chart.locallyIntegrableOn_of_continuousOn hℓR) (-1)
    (-(Real.pi * chiC κ)) (chiC (16 / κ)) h
  set hR' := Chart.chartTransport hR (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) h with hhR'
  set Z := Chart.chartTransport hJ 1 (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ)) hR' with hZ
  have h2 : IsChartTransport (jointChart w s) 1 (2 * Real.pi * chiC (16 / κ)) (1 * chiC (16 / κ)) hR' Z := by
    rw [one_mul]
    exact Chart.isChartTransport_chartTransport hJ (Chart.locallyIntegrableOn_of_continuousOn hℓJ) _ _ _ _
  have h3 := isChartTransport_trans_sign hR hJ hℓR hℓJ h1 h2
  have h4 := IsChartTransport.congr_chart (hR.trans hJ) (hL.trans hR) (fun v _ => (trans_jointChart_inv v).symm)
    (continuousOn_trans_lift hR hJ hℓR hℓJ) (2 * Real.pi) (fun v hv => trans_jointChart_lift hw hw0 hs hv) h3
  have e₁ : (1 : ℝ) * -1 = -1 := by ring
  have e₂ : (1 : ℝ) * -(Real.pi * chiC κ) + 2 * Real.pi * chiC (16 / κ) -
      1 * chiC (16 / κ) * (2 * Real.pi) = -(Real.pi * chiC κ) := by ring
  rw [e₁, e₂, one_mul] at h4
  -- the reading through the Loewner chart and the inversion
  have h5 := Chart.isChartTransport_chartTransport hL (Chart.locallyIntegrableOn_of_continuousOn hℓL) 1 0
    (chiC κ) h
  have h6 := isChartTransport_cfField κ hL h
  rw [hχ] at h6
  have h7 := isChartTransport_trans_sign hL hR hℓL hℓR h5 h6
  have e₃ : (-1 : ℝ) * 1 = -1 := by ring
  have e₄ : (-1 : ℝ) * 0 + -(Real.pi * chiC κ) = -(Real.pi * chiC κ) := by ring
  rw [e₃, e₄, ← hχ] at h7
  exact h4.unique (hL.trans hR) h7

end Joint

/-! ### BW1's state chart is the Loewner chart of the completed piece -/

section State

open Exist.StagedLaw

/-- The root chart recentred at `0` is the identity chart. -/
theorem id_recenter_zero : Chart.id.recenter 0 = Chart.id := by
  simp only [Chart.recenter, Chart.id, Complex.ofReal_zero, sub_zero, add_zero]

/-- **On a threshold, BW1's state chart after the first piece is the Loewner chart `g_A − W` of the piece**, driven
by the stopped piece driver `pieceDrv` up to the lifetime. -/
theorem stateChart_run_one_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {gw2 : Bool} {θ : ℝ} {t : ℝ≥0∞}
    {rest : List Instr} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {r : Bool}
    (h : BW1.EndsAtThresholdSide (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ D 1) r) :
    BW1.stateChart (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ D 1) =
      Chart.id.loewner (BW1Prop.pieceDrv (D 0)) (((D 0).2.toNNReal : ℝ≥0) : ℝ) := by
  rw [BW1Prop.run_one_eq_launch] at h ⊢
  have hle := BW1Prop.le_of_endsAtThresholdSide h
  have hfin := BW1Prop.ne_top_of_endsAtThresholdSide h
  rw [BW1Prop.launch_eq_top_of_le hle]
  change stChart (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤) = _
  rw [(launch_eq_of_ne_top (ExplState.init 0) 0 (D 0) θ ⊤ (GW1W.min_top_ne_top hfin)).1]
  have hs : stChart (ExplState.init 0) = Chart.id := id_recenter_zero
  rw [hs, stopDrv_def, stopTime, min_eq_right (le_top : (D 0).2 ≤ ⊤)]

/-- **BW1's identification `hXeq`**: on a threshold, the field read in the state chart and the inversion is the
counterflow-frame field read in the relative joint chart of the piece, with the offset `2πχ(16/κ)`. -/
theorem cfField_stateChart_eq {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {gw2 : Bool} {θ : ℝ}
    {t : ℝ≥0∞} {rest : List Instr} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {r : Bool}
    (h : BW1.EndsAtThresholdSide (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ D 1) r)
    (hc' : (BW1.stateChart (ExplState.run κ b jumps ⟨0, gw2, Sum.inl (θ, t) :: rest⟩ D 1)).IsConformal)
    (hU : Continuous (BW1Prop.pieceDrv (D 0))) (hU0 : BW1Prop.pieceDrv (D 0) 0 = 0)
    (f : DistOn upperHalfPlaneOpens) :
    cfField κ hc' f =
      Chart.chartTransport (isConformal_jointChart hU hU0 (NNReal.coe_nonneg (D 0).2.toNNReal)) 1
        (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ))
        (Chart.chartTransport Chart.isConformal_infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) f) := by
  rw [chartTransport_jointChart_eq_cfField hκ hU hU0 (NNReal.coe_nonneg (D 0).2.toNNReal) f]
  exact cfField_congr_chart κ hc' _ (stateChart_run_one_eq h) f

end State

end InteractingSLE.Theorem14.BW1Chain

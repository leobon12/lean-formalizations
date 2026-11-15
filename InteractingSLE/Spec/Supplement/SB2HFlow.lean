/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.FlowDilateFlow
import InteractingSLE.Spec.Supplement.W5CommonSeedShift
import InteractingSLE.Spec.Supplement.OrdFstShift
import InteractingSLE.Spec.Sec7.StripWallStage0
import InteractingSLE.Spec.Supplement.CondDriverBridge

/-!
# SB2(1) in launch form: the step after K2, at the seed `m`

Packet PROVE-T14-SB2FIN3. Lemma SB2(1) in launch form (`Lv.SB2UpperLaunchStatement`, ruling R87) asks, for **every**
witness `(b', jumps', h')` of the lower walk's launch clause (the field read in the launch chart `c`, a GFF with data
`b'` under the retained kernel), for a flow line of `h'` from the point `m ≤ 0` of the launch chart (the entry
`e_L = g_A(L⁻)` read in `c`). K2 (`SB.Cond.isCondFlowLineDriverOn_of_markedKernel`) produces a flow-line **driver from
`0`** in a random chart; read in the chart recentred at `m` (`c.recenter m`, forward map `c − m`) the relative upper
flow starts at `0`. This file converts the second form into the first:

* `eq_flowField_of_recenter`: the field read in `c.recenter m` is the translate `h'(· + m)` (`Exist.flowField m 0`) of
  the field read in `c`;
* `affField_one_flowField`, `affData_one_comp_add`, `affJumps_one_image_sub`, `cDil_one`: the affine map `z ↦ z + m`
  (`FlowDilate`, `a = 1`) undoes that recentring of fields, data and jump candidates;
* **`isFlowLine_of_recenter_driver`**: a flow-line driver of the field read in `c.recenter m` (data `bc`, with an
  almost sure generating trace `γ`) gives, for every witness `(b', J', h')` read in `c`, the flow line `γ + m` of `h'`
  from `m` with data `b'` (the data are matched off finite sets through the uniqueness of GFF data,
  `Exist.StagedLaw.eq_of_isGFFWithBoundaryData`, and `IsFlowLine.affine` translates the flow line).

Deterministic in the field and the data; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open FlowDilate

/-- The field read in a recentred chart is the translate of the field read in the chart. -/
theorem eq_flowField_of_recenter {c : Chart} (hc : c.IsConformal) (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H)
    {m k : ℝ} {f f' f'' : DistOn upperHalfPlaneOpens} (hT' : IsChartTransport c 1 0 k f f')
    (hT'' : IsChartTransport (c.recenter m) 1 0 k f f'') : f'' = Exist.flowField m 0 f' := by
  have e' : f' = Chart.chartTransport hc 1 0 k f :=
    hT'.unique hc (Chart.isChartTransport_chartTransport hc (Chart.locallyIntegrableOn_of_continuousOn hℓ) 1 0 k f)
  have e'' : f'' = Chart.chartTransport (hc.recenter m) 1 0 k f :=
    hT''.unique (hc.recenter m) (Chart.isChartTransport_chartTransport (hc.recenter m)
      (Chart.locallyIntegrableOn_of_continuousOn (Chart.continuousOn_recenter_lift hℓ)) 1 0 k f)
  rw [e', e'', RLC.OrdDet.chartTransport_recenter_eq_flowField hc hℓ]

/-- `affField m` with `a = 1` undoes the recentring `flowField m 0`. -/
theorem affField_one_flowField (m : ℝ) (f : DistOn upperHalfPlaneOpens) :
    affField m one_pos (Exist.flowField m 0 f) = f := by
  ext φ
  rw [affField_apply, Exist.flowField_apply, zero_mul, add_zero]
  congr 1
  ext z
  rw [Exist.pushTest_shiftChart_apply, affTest_apply]
  simp [aff]

/-- `affData 1 m` undoes the recentring of the data. -/
theorem affData_one_comp_add (m : ℝ) (b : ℝ → ℝ) : affData 1 m (fun y => b (y + m)) = b := by
  funext y
  simp [affData]

/-- `affJumps 1 m` undoes the recentring of the jump candidates. -/
theorem affJumps_one_image_sub (m : ℝ) (J : Finset ℝ) : affJumps 1 m (J.image (· - m)) = J := by
  rw [affJumps, Finset.image_image]
  convert Finset.image_id (s := J) using 2
  funext y
  simp [raff]

theorem cDil_one : cDil 1 = 1 := by
  simp [cDil]

/-- **The step after K2 at a seed `m`** (the launch form of SB2(1)): if, under `Q`, the driver `W` (lifetime `ζ`,
almost sure generating trace `γ`) is the angle-`ψ` flow-line driver of the field read in the chart `c` recentred at
`m` (`IsChartTransport (c.recenter m)`, a GFF with data `bc`), then for **every** witness `(b', J', h')` of the field
read in `c` itself (a GFF with data `b'`), the curve `γ + m` is the angle-`ψ` flow line of `h'` from `m` with data
`b'` and lifetime `ζ`. -/
theorem isFlowLine_of_recenter_driver {κ ψ m : ℝ} {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {c : Chart} (hc : c.IsConformal) (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H)
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {b' bc : ℝ → ℝ} {J' jc : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hbc : IsPiecewiseConstantBoundaryData bc jc)
    (hT' : ∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω))
    (hT'' : ∀ ω, IsChartTransport (c.recenter m) 1 0 (chiC κ) (h ω) (h'' ω))
    (hG' : IsGFFWithBoundaryData Q h' b' J') (hG'' : IsGFFWithBoundaryData Q h'' bc jc)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hd : IsFlowLineDriver κ bc jc ψ Q h'' W ζ)
    {γ : Ω → ℝ≥0 → ℂ} (htr : ∀ᵐ ω ∂Q, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) :
    IsFlowLine κ b' J' m ψ Q h' (fun ω t => γ ω t + m) ζ := by
  have hfe : h'' = fun ω => Exist.flowField m 0 (h' ω) :=
    funext fun ω => eq_flowField_of_recenter hc hℓ (hT' ω) (hT'' ω)
  have hbm : IsPiecewiseConstantBoundaryData (fun y => b' (y + m)) (J'.image (· - m)) :=
    Exist.isPiecewiseConstant_comp_add hb' m
  have hGm : IsGFFWithBoundaryData Q h'' (fun y => b' (y + m)) (J'.image (· - m)) := by
    rw [hfe]
    exact_mod_cast Supp9.IsGFFWithBoundaryData.recenter hb' m hG'
  have heq := Exist.StagedLaw.eq_of_isGFFWithBoundaryData hbc hbm hG'' hGm
  have hd' : IsFlowLineDriver κ (fun y => b' (y + m)) (J'.image (· - m)) ψ Q h'' W ζ :=
    (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hbc hbm (jc ∪ J'.image (· - m))
      (fun y hy => (heq y hy).symm)).2 hd
  have hfl0 := Sec7.StripWall.isFlowLine_of_isFlowLineDriver hd' htr
  have hfl := hfl0.affine (a := 1) (m := m) one_pos hbm
  rw [affData_one_comp_add, affJumps_one_image_sub, cDil_one] at hfl
  simp only [one_mul, raff, mul_zero, zero_add, hfe, affField_one_flowField, ENNReal.coe_one, div_one] at hfl
  convert hfl using 3 with ω t
  simp [aff]

end InteractingSLE.Theorem14.SB.Lv

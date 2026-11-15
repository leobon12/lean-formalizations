/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HsdDet
import InteractingSLE.Spec.Sec7.R7StopInSelect
import InteractingSLE.Spec.Supplement.GB10Proof

/-!
# Theorem R.7's counterflow on an R.7 configuration: the pathwise facts used by the outer pockets

Packet PROVE-R7-OUTERIN. The geometric assemblies of the mixed and outer change pockets (PROVE-R7-STOPIN,
PROVE-R7-GAPEQ) ask, for the counterflow's trace `η` on one realization, that it stays in the open half-plane at
positive times, has no time interval inside a simple arc (Aux. lemma 42), and avoids the certified exterior sides at
every real time. On an R.7 configuration (`R7Outer.IsR7OuterConfig`, heights `c, c′ ≥ 0`) with a decomposition of its
centred counterflow (`R7Leaves.IsCfDecomp`) and a version `η` of the counterflow's trace, these hold almost surely:

* `r7_stripFrame`: the counterflow is the Figure 5.1 strip counterflow of the frame `R7`'s `r7Frame` (the argument of
  `Hsd.r7_det`, isolated): strip field and strip counterflow driver with the same driving process;
* **`ae_counterflow_mem_H_r7`**: `η(t) ∈ ℍ` for every `t > 0` (Zhan's Part A through Aux. lemma 7 and the junction
  barrier: `Prop513Wire.fig51_trace_mem_H_of_partA_of_clearance`);
* **`ae_noSimpleArc_counterflow_r7`**: Aux. lemma 42 for `η` (Lemma GB10, `GB10.gb10Statement`, applied to the
  counterflow's integrated evolution);
* **`ae_avoid_counterflow_r7`**: `m(η(t)) ∉ E_R ∪ E_L` at every real `t ≥ 0` (the configuration's `avoid`).

R48: the only named statement used is Zhan's Part A (`PartAInputsSixteenDivOfClearance`, on R48's list of Theorem 1.2
inputs); nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.OuterIn

open WholeField StripSysField R7Outer R7Leaves Hsd
open Sec5 Sec4 Sec5.Prop513Bridge

section Counterflow

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ}

/-- **The R.7 counterflow is a Figure 5.1 strip counterflow** (the frame `Hsd.r7Frame`, chart `M_1`, `x₀ = 0`): its
coupling field `h″` read in the strip chart is a Figure 5.1 field and `W′` is a strip counterflow driver of it. This is
the argument of `Hsd.r7_det` (transport uniqueness, `r7_hword`) without Proposition 5.13. -/
theorem r7_stripFrame (hk4 : 4 < k)
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) :
    ∃ hS : Ω → DistOn upperHalfPlaneOpens,
      IsStripGFF (16 / k) P hS (fig51Lower (r7A k rR + c) (r7B k rL + c'))
        (fig51Upper 0 (r7A k rR + c + π * chiC (16 / k)) (r7B k rL + c' + π * chiC (16 / k))) {0} {0} ∧
      IsStripCounterflowDriver (16 / k) 0 (Real.exp (π * 0)) P hS W' ζ' := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have e : 16 / (16 / k) = k := by field_simp
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  obtain ⟨h₀, htr₀, hfl₀⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨-, hT, hTr, -⟩ := hD
  rw [e] at htr₀
  have e₀ : h₀ = h'' := by
    funext ω
    rw [IsChartTransport.unique Chart.isConformal_infinitySourceChart (htr₀ ω) (hT ω)]
    exact (Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (hTr ω)).symm
  rw [e₀] at hfl₀
  have hbP := isPiecewiseConstant_counterflowData (16 / k) hb
  have hG := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver (div_pos (by norm_num) hκ) hbP hfl₀
  have hGF := isStripGFF_parameterSource_of_word hκ hbP hG (r7_hword (rL := rL) (rR := rR) (c := c) (c' := c') hk4)
  have hTF : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * 0))) (-1) (-(π * chiC (16 / k)))
      (chiC (16 / (16 / k))) (fig51Source (16 / k) 0 h'' ω) (h'' ω) :=
    fun ω => isChartTransport_parameterSource (Real.exp_pos _) _ _ (h'' ω)
  refine ⟨fig51Source (16 / k) 0 h'', hGF, ?_⟩
  refine ⟨counterflowData (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')), counterflowJumps {0}, h'', hbP,
    ?_, hfl₀⟩
  simpa only [zero_add] using hTF

/-- **The R.7 counterflow stays in the open half-plane at positive times**: for a version `η` of its trace, almost
surely `η(t) ∈ ℍ` for every `t > 0` (the Figure 5.1 strip counterflow does not return to the real line:
`fig51_trace_mem_H_of_partA_of_clearance`, from Zhan's Part A through Aux. lemma 7). -/
theorem ae_counterflow_mem_H_r7 (hA : PartAInputsSixteenDivOfClearance) (hk4 : 4 < k) (hc : 0 ≤ c)
    (hc' : 0 ≤ c')
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ∈ H := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  obtain ⟨hS, hG, hcfS⟩ := r7_stripFrame hk4 hh hcf hD
  filter_upwards [Prop513Wire.fig51_trace_mem_H_of_partA_of_clearance hA hκ hκ4 (isFig51Bounds_r7Frame hk4 hc hc')
    hG hcfS, hηtr] with ω hω htr t ht
  have h1 := hω.2 _ htr t.toNNReal (Real.toNNReal_pos.2 ht)
  rwa [Real.coe_toNNReal _ ht.le] at h1

/-- **Aux. lemma 42 for the R.7 counterflow**: for a version `η` of its trace, almost surely no nontrivial time
interval of `η` lies in a simple arc (Lemma GB10 for the counterflow's integrated evolution, infinite lifetime). -/
theorem ae_noSimpleArc_counterflow_r7 (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η ω s) ⊤ := by
  obtain ⟨-, -, -, hC⟩ := hD
  have hG := Theorem14.GB10.gb10Statement k hk4 _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b' J' 0) P 𝓕 W' VL
    VR B ζ' hC.1
  filter_upwards [hG, hηtr, ae_counterflow_trace_r7 hk4 hc hc' hh hcf] with ω hω htr hζ
  have h1 := hω _ (by rw [hζ.1]; exact htr)
  rwa [hζ.1] at h1

end Counterflow

section Avoid

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **The R.7 counterflow avoids the certified exterior sides at every real time**: for a version `η` of its trace,
almost surely `m(η(t)) ∉ E_R ∪ E_L` for every `t ≥ 0` (`IsR7OuterConfig.avoid` on the infinite-lifetime event). -/
theorem ae_avoid_counterflow_r7 [IsProbabilityMeasure P] (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      WangWu.negInv (η ω t) ∉ rightSideOf (range (βR ω)) ∪ leftSideOf (range (βL ω)) := by
  filter_upwards [hcfg.avoid, hηtr, ae_counterflow_trace_r7 hk4 hc hc' hcfg.gff hcfg.counterflow]
    with ω hω htr hζ t ht
  have h1 := hω hζ.1 _ htr t.toNNReal
  rwa [Real.coe_toNNReal _ ht] at h1

end Avoid

end InteractingSLE.Sec7.OuterIn

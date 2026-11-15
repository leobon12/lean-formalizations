/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1ChainK2
import InteractingSLE.Spec.Supplement.CondDriverBridge

/-!
# The relative chain, part 3: the conditional centred counterflow

Packet PROVE-BW1-CHAIN. Proposition BW1's conclusion is a **conditional centred counterflow**
(`SB.IsCondCounterflowDriverOn`): for almost every `ω₀` of the live event, under `condExpKernel P 𝒢 ω₀`, the
relative driver drives the frozen centred counterflow of the conditional field read in the fixed chart `c ω₀`.
The K2 chain (`BW1ChainK2`) produces an optional hull coupling for the field read through the **random** chart
`c ω` and the inversion (`cfField`), with K2's word. This file is the counterflow analogue of
`CondDriverBridge` (which does the same for conditional flow lines):

* `cfField κ hc f`: the field `f` read in the chart `c` with the flow rule `(1, 0, χ(κ))`, then in the inversion
  chart with the counterflow coefficients `(−1, −πχ(κ), χ(16/κ))` (the two transports of
  `IsCondCounterflowDriverOn` and `IsCenteredCounterflowDriver`), and its measurability;
* **`isCenteredCounterflowDriver_of_coupling_cfField`** (one kernel measure): if `c` is almost surely the fixed
  chart `c₀`, an optional hull coupling at `16/κ` of the angle-`0` flow-line word of `(b, J)` for `cfField κ (c ω)`
  and a driver `W'` equal to `W` gives the centred counterflow of the field read in `c₀`, driven by `W`;
* **`isCondCounterflowDriverOn_of_k2Output`**: the conditional version, from K2's output with a fixed number of marks
  and the word of the conditional data;
* `IsCondCounterflowDriverOn.iUnion`: conditional counterflows on countably many events glue (the word types);
* **`isCondCounterflowDriverOn_of_hasSafeLaw_top`**: the whole chain — (S), (L) with infinite lifetime and no
  threshold, plus the word of the conditional data and the kernel-almost sure constancy of the chart, give the
  conditional centred counterflow, with lifetime the threshold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.BW1Chain

open Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7 Sec7.PocketTraversal MartChar CondDriverBridge
open Exist.Staged

/-- **The counterflow-frame field of `f` read in the chart `c`**: the flow-rule transport by `c` (coefficients
`(1, 0, χ(κ))`) followed by the inversion chart with the counterflow coefficients `(−1, −πχ(κ), χ(16/κ))`. -/
def cfField (κ : ℝ) {c : Chart} (hc : c.IsConformal) (f : DistOn upperHalfPlaneOpens) :
    DistOn upperHalfPlaneOpens :=
  Chart.chartTransport Chart.isConformal_infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ))
    (Chart.chartTransport hc 1 0 (chiC κ) f)

theorem measurable_cfField (κ : ℝ) {c : Chart} (hc : c.IsConformal) : Measurable (cfField κ hc) :=
  (Chart.measurable_chartTransport _ _ _ _).comp (Chart.measurable_chartTransport hc 1 0 (chiC κ))

/-- The inversion transport of `cfField` is the frozen `IsChartTransport` of the inversion chart. -/
theorem isChartTransport_cfField (κ : ℝ) {c : Chart} (hc : c.IsConformal) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ))
      (Chart.chartTransport hc 1 0 (chiC κ) f) (cfField κ hc f) :=
  Chart.isChartTransport_chartTransport Chart.isConformal_infinitySourceChart
    (Chart.locallyIntegrableOn_of_continuousOn Chart.continuousOn_infinitySourceChart_lift) _ _ _ _

/-- `cfField` depends only on the chart. -/
theorem cfField_congr_chart (κ : ℝ) {c c' : Chart} (hc : c.IsConformal) (hc' : c'.IsConformal) (e : c = c')
    (f : DistOn upperHalfPlaneOpens) : cfField κ hc f = cfField κ hc' f := by
  subst e
  rfl

/-- A field is its own translate by `0` with the constant `0 · χ`. -/
theorem isTranslateAddConst_zero_self (k : ℝ) (f : DistOn upperHalfPlaneOpens) :
    IsTranslateAddConst 0 (0 * k) f f := by
  intro φ φ' hφ
  have e : φ' = φ := by
    ext z
    rw [hφ z, Complex.ofReal_zero, add_zero]
  rw [e, zero_mul, zero_mul, add_zero]

/-! ### One kernel measure -/

section One

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- **The counterflow bridge under one probability measure.** Let `c` be a random conformal chart which is almost
surely the fixed chart `c₀`, and suppose the field `cfField κ (c ω) (h ω)` and a driver `W'` form an optional hull
coupling at `16/κ` of the angle-`0` flow-line word of `(b, J)` at the seed `0`. If `W` is measurable at every time and
agrees with `W'` almost surely, then `W` drives the centred counterflow of the field read in `c₀` (flow rule
`(1, 0, χ)`). -/
theorem isCenteredCounterflowDriver_of_coupling_cfField (hb : IsPiecewiseConstantBoundaryData b J)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) {c₀ : Chart} (hc₀ : c₀.IsConformal) (hcc : ∀ᵐ ω ∂Q, c ω = c₀)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {𝓕 : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hC : IsOptionalHullCoupling (16 / κ) (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL (16 / κ) b J 0 0)
      (flowLineRhoR (16 / κ) b J 0 0) Q 𝓕 W' VL VR B ζ (fun ω => cfField κ (hc ω) (h ω)))
    (hWm : ∀ t, Measurable (W t)) (hWW : ∀ᵐ ω ∂Q, ∀ t, W' t ω = W t ω) :
    IsCenteredCounterflowDriver κ Q (fun ω => Chart.chartTransport hc₀ 1 0 (chiC κ) (h ω)) W ζ := by
  set h'' : Ω → DistOn upperHalfPlaneOpens := fun ω => cfField κ hc₀ (h ω) with hh''
  have he : h'' =ᵐ[Q] fun ω => cfField κ (hc ω) (h ω) :=
    hcc.mono fun ω hω => cfField_congr_chart κ hc₀ (hc ω) hω.symm _
  have hm : Measurable h'' := (measurable_cfField κ hc₀).comp hhm
  have hC'' := Sec7.Prop74B.IsOptionalHullCoupling.congr_field hC hm (fun u₀ hu₀ =>
    isZBGFFProcess_congr_ae (hC.2.2.1 u₀ hu₀)
      (fun φ => ((LQGMetric.measurable_distOn_apply φ).comp hm).sub_const _)
      fun φ => he.mono fun ω hω => by simp only [hω]) he
  have hfl : IsFlowLineDriver (16 / κ) b J 0 Q h'' W' ζ :=
    ⟨h'', 𝓕, VL, VR, B, fun ω => isTranslateAddConst_zero_self _ _, hC''⟩
  exact ⟨b, J, h'', hb, fun ω => isChartTransport_cfField κ hc₀ (h ω),
    StagedReg.isFlowLineDriver_congr_ae hfl hWm (hWW.mono fun ω hω => ⟨(hω 0).symm, fun t _ => (hω t).symm⟩)⟩

end One

/-! ### The conditional counterflow -/

section Cond

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  {κ : ℝ} {F : Set Ω} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {bc : Ω → ℝ → ℝ}
  {jc : Ω → Finset ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Conditional counterflows on countably many events glue.** -/
theorem isCondCounterflowDriverOn_iUnion [IsFiniteMeasure P] {ι : Type*} [Countable ι] {F : ι → Set Ω}
    (hW : ∀ i, SB.IsCondCounterflowDriverOn κ 𝒢 P (F i) h c W ζ) :
    SB.IsCondCounterflowDriverOn κ 𝒢 P (⋃ i, F i) h c W ζ := by
  filter_upwards [ae_all_iff.2 hW] with ω₀ hω₀ hF
  obtain ⟨i, hi⟩ := mem_iUnion.1 hF
  exact hω₀ i hi

/-- **K2's output gives the conditional centred counterflow** (the counterflow analogue of
`CondDriverBridge.isCondFlowLineDriverOn_of_k2Output`): on the live event the word `((ΘL, ΘR), (ρL, ρR))` is the
angle-`0` flow-line word at `16/κ` of the conditional data `(bc, jc)` (with `nL`, `nR` marks), and the chart is
kernel-almost surely constant. -/
theorem isCondCounterflowDriverOn_of_k2Output [IsFiniteMeasure P] {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hhm : Measurable h) (hc : ∀ ω, (c ω).IsConformal)
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) (hWm : ∀ t, Measurable (W t))
    (hword : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (bc ω) (jc ω) ∧ flowLineNL (bc ω) (jc ω) 0 = nL ∧
      flowLineNR (bc ω) (jc ω) 0 = nR ∧
        truncWord nL nR (padFL (16 / κ) 0 (bc ω) (jc ω)) = ((ΘL ω, ΘR ω), (ρL, ρR)))
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀)
    (hK2 : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling (16 / κ) (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' ζ
          (fun ω => cfField κ (hc ω) (h ω)) ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧
          ∀ j, VR' j t ω = VR j t ω) :
    SB.IsCondCounterflowDriverOn κ 𝒢 P F h c W ζ := by
  filter_upwards [hword, hcc, hK2] with ω₀ hw hc₀ hK₀ hF
  obtain ⟨hb, hnL, hnR, htw⟩ := hw hF
  obtain ⟨𝓕', W', VL', VR', B', hC, hag⟩ := hK₀ hF
  obtain ⟨VL'', VR'', hC'⟩ := coupling_flowLineWord_of_truncWord hnL hnR htw hC
  exact ⟨fun ω => Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω), fun ω =>
    isChartTransport_chartTransport_of_continuousOn (hc ω₀) (hlc ω₀) 1 0 (chiC κ) (h ω),
    isCenteredCounterflowDriver_of_coupling_cfField hb hc (hc ω₀) (hc₀ hF) hhm hC' hWm
      (hag.mono fun ω hω t => (hω t).1)⟩

/-- **The whole chain for a relative counterflow of infinite relative lifetime** (`BW1ChainK2` at `16/κ` followed by
`isCondCounterflowDriverOn_of_k2Output`). Let the field be read through a random conformal chart `c` (measurable in
the coordinates, continuous lift) and the inversion (`cfField`). On a live event `F ∈ 𝒢` of a fixed word type, suppose:
the relative driver `W` is continuous from `0` and `𝓗`-adapted (`𝒢 ≤ 𝓗 0`), with the geometric force points of a
`𝒢`-measurable ordered word `(xL, xR)`; K2's (S) and (L) hold with infinite lifetime; the word reaches no continuation
threshold on `F`; the word is the angle-`0` flow-line word at `16/κ` of the conditional data `(bc, jc)`; and the chart
is kernel-almost surely constant. Then `W` drives, conditionally on `𝒢` on `F`, the centred counterflow of the field
read in the chart, with lifetime the continuation threshold. -/
theorem isCondCounterflowDriverOn_of_hasSafeLaw_top [IsProbabilityMeasure P] (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0) (hF : MeasurableSet[𝒢] F)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) (hhm : Measurable h) (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => cfField κ (hc ω) (h ω) φ) P)
    (hlaw : HasSafeLaw (16 / κ) ρL ρR P 𝓗 F (fun _ => ⊤) W (geomLW W xL) (geomRW W xR)
      fun ω => cfField κ (hc ω) (h ω))
    (hmem : HasSafeMembers P 𝓗 F (fun _ => ⊤) W fun ω => cfField κ (hc ω) (h ω))
    (hthr : ∀ᵐ ω ∂P, ω ∈ F → thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω) = ⊤)
    (hword : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (bc ω) (jc ω) ∧ flowLineNL (bc ω) (jc ω) 0 = nL ∧
      flowLineNR (bc ω) (jc ω) 0 = nR ∧
        truncWord nL nR (padFL (16 / κ) 0 (bc ω) (jc ω)) = ((xL ω, xR ω), (ρL, ρR)))
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀) :
    SB.IsCondCounterflowDriverOn κ 𝒢 P F h c W
      (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
        (fun j t => geomRW W xR j t ω)) := by
  have hX : Measurable fun ω => cfField κ (hc ω) (h ω) :=
    (Chart.measurable_chartTransport _ _ _ _).comp
      (Chart.measurable_chartTransport_random' hc hdom hfwd hliftm hlc hhm 1 0 (chiC κ))
  have hWm : ∀ t, Measurable (W t) := fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl
  exact isCondCounterflowDriverOn_of_k2Output (VL := geomLW W xL) (VR := geomRW W xR) hhm hc hlc hWm hword hcc
    (ae_isOptionalHullCoupling_of_hasSafeLaw_top (div_pos (by norm_num) hκ) h𝒢 hF hxL hxR hxL0 hxR0 hxLa hxRm
      hW0 hWc hWa hX hint hlaw hmem hthr)

end Cond

end InteractingSLE.Theorem14.BW1Chain

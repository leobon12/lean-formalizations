/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovMeanK2
import InteractingSLE.Spec.Supplement.SB2Remainder
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Sec7.Prop74BMain
import InteractingSLE.Spec.Sec7.Lemma725RefK2
import InteractingSLE.Spec.Exist.StagedLawPast

/-!
# From K2's conditional coupling to `SB.IsCondFlowLineDriverOn`

Packet PROVE-T14-SB8, item (a4) of `planning/handoffs/PROVE-T14-SB7.md` §5 (b). K2
(`Restart.DomainMarkov.Mean.ae_isOptionalHullCoupling_chartTransport`) gives, for almost every `ω₀` of the live event
`F`, an optional hull coupling under `condExpKernel P 𝒢 ω₀` of the word `(ΘL ω₀, ΘR ω₀)` with **deterministic**
weights `ρL ρR` and a fixed number of marks, for the field `chartTransport (c ω) 1 a k h` read in the **random** chart
`c ω`, with a driver `W'` equal to the continuation `W` kernel-almost surely. The carrier `SB.IsCondFlowLineDriverOn`
(the frozen staged launch clause with explicit σ-algebra, chart and event) asks instead for the frozen
`IsFlowLineDriver` of the data `(bc ω₀, jc ω₀)` at angle `θ`, for the field read in the **fixed** chart `c ω₀` with the
flow rule `(1, 0, χ)`, driven by `W` itself. The bridge:

1. the word: on the event where the flow-line word of `(bc, jc)` at the seed `0` has `nL`, `nR` marks and padded data
   `((ΘL, ΘR), (ρL, ρR))` (`truncWord_padFL`), K2's word is the flow-line word (`coupling_flowLineWord_of_truncWord`);
2. the chart: if `c ω = c ω₀` kernel-almost surely, the field `chartTransport (c ω) 1 (θχ) χ h` is a null modification
   of `chartTransport (c ω₀) 1 (θχ) χ h` (`IsOptionalHullCoupling.congr_field`); this holds when `c` is almost surely
   a function of a `𝒢`-measurable record with values in a countably separated space (`ae_ae_chart_eq_of_ae_eq_comp`);
3. the translation: `chartTransport c 1 (θχ) χ h` is the translate by `θχ` (`IsTranslateAddConst 0 (θχ)`) of
   `chartTransport c 1 0 χ h`, which is the frozen transport `IsChartTransport c 1 0 χ` of `h`;
4. the driver: `W'` is replaced by `W` (`StagedReg.isFlowLineDriver_congr_ae`);
5. the words of different pieces: K2 is applied on each piece of a countable partition of `F` by the values of
   `(nL, nR, ρL, ρR)`; the conditional flow lines on the pieces glue (`IsCondFlowLineDriverOn.iUnion`).

Main results: **`isFlowLineDriver_of_coupling_chartTransport`** (one kernel measure),
**`isCondFlowLineDriverOn_of_coupling`**, **`isCondFlowLineDriverOn_of_k2Output`** (K2's conclusion as input) and
**`isCondFlowLineDriverOn_of_k2`** (K2's hypotheses as input).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace CondDriverBridge

open Exist.Staged

/-! ### Chart bookkeeping -/

/-- The chart transport only depends on the chart (not on the conformality proof). -/
theorem chartTransport_congr_chart {c c' : Chart} (hc : c.IsConformal) (hc' : c'.IsConformal) (e : c = c')
    (σ a k : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport hc σ a k f = Chart.chartTransport hc' σ a k f := by
  subst e
  rfl

/-- **Adding a constant after the transport**: `chartTransport c 1 a k f` is the translate by `0` plus the constant
`a` of `chartTransport c 1 0 k f`. -/
theorem isTranslateAddConst_chartTransport {c : Chart} (hc : c.IsConformal) (a k : ℝ)
    (f : DistOn upperHalfPlaneOpens) :
    IsTranslateAddConst 0 a (Chart.chartTransport hc 1 0 k f) (Chart.chartTransport hc 1 a k f) := by
  intro φ φ' hφ
  have e : φ' = φ := by
    ext z
    rw [hφ z, Complex.ofReal_zero, add_zero]
  subst e
  rw [Chart.chartTransport_apply', Chart.chartTransport_apply', Chart.oneDist_apply]
  ring

/-- The lift of a conformal chart with a continuous lift on its domain is continuous on `ℍ` in the coordinate. -/
theorem continuousOn_lift_inv {c : Chart} (hc : c.IsConformal) (hlc : ContinuousOn c.2.2 c.dom) :
    ContinuousOn (fun w => c.2.2 (c.2.1 w)) H :=
  hlc.comp hc.1.continuousOn fun _ hw => hc.inv_mem_dom hw

/-- **The flow-rule transport in a conformal chart with a continuous lift** is the frozen `IsChartTransport`. -/
theorem isChartTransport_chartTransport_of_continuousOn {c : Chart} (hc : c.IsConformal)
    (hlc : ContinuousOn c.2.2 c.dom) (σ a k : ℝ) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport c σ a k f (Chart.chartTransport hc σ a k f) :=
  Chart.isChartTransport_chartTransport hc
    (Chart.locallyIntegrableOn_of_continuousOn (continuousOn_lift_inv hc hlc)) σ a k f

/-! ### Null modifications -/

section Congr

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- A null modification of a zero-boundary GFF process (with measurable coordinates) is one. -/
theorem isZBGFFProcess_congr_ae {U : TopologicalSpace.Opens ℂ} {Q : Measure Ω} {X Y : TestOn U → Ω → ℝ}
    (hX : LQGMetric.IsZBGFFProcess U X Q) (hY : ∀ φ, Measurable (Y φ)) (he : ∀ φ, X φ =ᵐ[Q] Y φ) :
    LQGMetric.IsZBGFFProcess U Y Q := by
  refine ⟨hY, hX.gaussian.congr he, fun φ => ?_, fun φ ψ => ?_⟩
  · rw [← integral_congr_ae (he φ)]
    exact hX.centered φ
  · rw [← hX.covariance_eq φ ψ]
    unfold covariance
    rw [integral_congr_ae (he φ), integral_congr_ae (he ψ)]
    refine integral_congr_ae ?_
    filter_upwards [he φ, he ψ] with ω h1 h2
    simp only [h1, h2]

/-- **The flow-line word, read from padded data.** If the flow-line word of `(b, J)` at the seed `0` has `nL`, `nR`
marks and padded data `((xL, xR), (ρL, ρR))`, an optional hull coupling of the word `(xL, xR, ρL, ρR)` is one of the
flow-line word (with the same driver, lifetime, noise and field). -/
theorem coupling_flowLineWord_of_truncWord {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}
    (hnL : flowLineNL b J 0 = nL) (hnR : flowLineNR b J 0 = nR)
    (hw : truncWord nL nR (padFL κ θ b J) = ((xL, xR), (ρL, ρR)))
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 W VL VR B ζ X) :
    ∃ (VL' : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ) (VR' : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
        (flowLineRhoR κ b J 0 θ) Q 𝓕 W VL' VR' B ζ X := by
  subst hnL hnR
  rw [truncWord_padFL] at hw
  simp only [Prod.mk.injEq] at hw
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hw
  rw [e1, e2, e3, e4]
  exact ⟨VL, VR, hC⟩

end Congr

/-! ### One kernel measure -/

section One

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- **The bridge under one probability measure.** Let `c` be a random conformal chart which is almost surely the
fixed chart `c₀`, and suppose the field `chartTransport (c ω) 1 (θχ) χ (h ω)` and a driver `W'` form an optional hull
coupling of the angle-`θ` flow-line word of `(b, J)` at the seed `0`. If `W` is measurable at every time and agrees
with `W'` almost surely, then `W` drives the angle-`θ` flow line of the field read in `c₀` with the flow rule
`(1, 0, χ)`. -/
theorem isFlowLineDriver_of_coupling_chartTransport {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) {c₀ : Chart}
    (hc₀ : c₀.IsConformal) (hcc : ∀ᵐ ω ∂Q, c ω = c₀) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {𝓕 : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hC : IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) Q 𝓕 W' VL VR B ζ
      (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω)))
    (hWm : ∀ t, Measurable (W t)) (hWW : ∀ᵐ ω ∂Q, ∀ t, W' t ω = W t ω) :
    IsFlowLineDriver κ b J θ Q (fun ω => Chart.chartTransport hc₀ 1 0 (chiC κ) (h ω)) W ζ := by
  set h'' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hc₀ 1 (θ * chiC κ) (chiC κ) (h ω)
    with hh''
  have he : h'' =ᵐ[Q] fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) :=
    hcc.mono fun ω hω => chartTransport_congr_chart hc₀ (hc ω) hω.symm _ _ _ _
  have hm : Measurable h'' := (Chart.measurable_chartTransport hc₀ 1 (θ * chiC κ) (chiC κ)).comp hhm
  have hC'' := Sec7.Prop74B.IsOptionalHullCoupling.congr_field hC hm (fun u₀ hu₀ =>
    isZBGFFProcess_congr_ae (hC.2.2.1 u₀ hu₀)
      (fun φ => ((LQGMetric.measurable_distOn_apply φ).comp hm).sub_const _)
      fun φ => he.mono fun ω hω => by simp only [hω]) he
  have hfl : IsFlowLineDriver κ b J θ Q (fun ω => Chart.chartTransport hc₀ 1 0 (chiC κ) (h ω)) W' ζ :=
    ⟨h'', 𝓕, VL, VR, B, fun ω => isTranslateAddConst_chartTransport hc₀ _ _ _, hC''⟩
  exact StagedReg.isFlowLineDriver_congr_ae hfl hWm
    (hWW.mono fun ω hω => ⟨(hω 0).symm, fun t _ => (hω t).symm⟩)

end One

/-! ### The conditional flow line -/

section Cond

variable {Ω : Type u} {𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  {κ θ : ℝ} {F : Set Ω} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {bc : Ω → ℝ → ℝ}
  {jc : Ω → Finset ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Conditional flow lines on countably many events glue.** -/
theorem _root_.InteractingSLE.Theorem14.SB.IsCondFlowLineDriverOn.iUnion [IsFiniteMeasure P] {ι : Type*}
    [Countable ι] {F : ι → Set Ω} (hW : ∀ i, SB.IsCondFlowLineDriverOn κ θ 𝒢 P (F i) h c bc jc W ζ) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P (⋃ i, F i) h c bc jc W ζ := by
  filter_upwards [ae_all_iff.2 hW] with ω₀ hω₀ hF
  obtain ⟨i, hi⟩ := mem_iUnion.1 hF
  exact hω₀ i hi

/-- **The conditional flow line from conditional couplings in the random chart.** For almost every `ω₀ ∈ F`: the
data `(bc ω₀, jc ω₀)` are piecewise constant, the random conformal chart is `c ω₀` kernel-almost surely, and under
`condExpKernel P 𝒢 ω₀` the field `chartTransport (c ω) 1 (θχ) χ (h ω)` and some driver equal to `W` kernel-almost
surely form an optional hull coupling of the angle-`θ` flow-line word of `(bc ω₀, jc ω₀)`. Then `W` is a conditional
angle-`θ` flow line on `F` in the chart `c`. -/
theorem isCondFlowLineDriverOn_of_coupling [IsFiniteMeasure P] (hhm : Measurable h)
    (hc : ∀ ω, (c ω).IsConformal) (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) (hWm : ∀ t, Measurable (W t))
    (hbc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsPiecewiseConstantBoundaryData (bc ω₀) (jc ω₀))
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀)
    (hK : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin (flowLineNL (bc ω₀) (jc ω₀) 0) → ℝ≥0 → Ω → ℝ)
        (VR' : Fin (flowLineNR (bc ω₀) (jc ω₀) 0) → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ (flowLineXL (bc ω₀) (jc ω₀) 0) (flowLineXR (bc ω₀) (jc ω₀) 0)
          (flowLineRhoL κ (bc ω₀) (jc ω₀) 0 θ) (flowLineRhoR κ (bc ω₀) (jc ω₀) 0 θ) (condExpKernel P 𝒢 ω₀) 𝓕' W'
          VL' VR' B' ζ (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω)) ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ := by
  filter_upwards [hbc, hcc, hK] with ω₀ hb hc₀ hK₀ hF
  obtain ⟨𝓕', W', VL', VR', B', hC, hWW⟩ := hK₀ hF
  exact ⟨hb hF, fun ω => Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω),
    fun ω => isChartTransport_chartTransport_of_continuousOn (hc ω₀) (hlc ω₀) 1 0 (chiC κ) (h ω),
    isFlowLineDriver_of_coupling_chartTransport hc (hc ω₀) (hc₀ hF) hhm hC hWm hWW⟩

/-- **K2's conclusion gives the conditional flow line.** Suppose that almost surely on `F` the data `(bc, jc)` are
piecewise constant and their flow-line word at the seed `0` has `nL`, `nR` marks and padded data
`((ΘL, ΘR), (ρL, ρR))`, and that the random chart is kernel-almost surely constant. Then the conclusion of K2 for the
flow rule `(1, θχ, χ)` (`Restart.DomainMarkov.Mean.ae_isOptionalHullCoupling_chartTransport` with `a = θχ`,
`k = χ`) makes `W` a conditional angle-`θ` flow line on `F` in the chart `c`. -/
theorem isCondFlowLineDriverOn_of_k2Output [IsFiniteMeasure P] {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hhm : Measurable h) (hc : ∀ ω, (c ω).IsConformal) (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hWm : ∀ t, Measurable (W t))
    (hword : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (bc ω) (jc ω) ∧ flowLineNL (bc ω) (jc ω) 0 = nL ∧
      flowLineNR (bc ω) (jc ω) 0 = nR ∧ truncWord nL nR (padFL κ θ (bc ω) (jc ω)) = ((ΘL ω, ΘR ω), (ρL, ρR)))
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀)
    (hK2 : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' ζ
          (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω)) ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧
          ∀ j, VR' j t ω = VR j t ω) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ := by
  refine isCondFlowLineDriverOn_of_coupling hhm hc hlc hWm (hword.mono fun ω hω hF => (hω hF).1) hcc ?_
  filter_upwards [hword, hK2] with ω₀ hw hk hF
  obtain ⟨-, hn1, hn2, htw⟩ := hw hF
  obtain ⟨𝓕', W', VL', VR', B', hC, hagree⟩ := hk hF
  obtain ⟨VL'', VR'', hC'⟩ := coupling_flowLineWord_of_truncWord hn1 hn2 htw hC
  exact ⟨𝓕', W', VL'', VR'', B', hC', hagree.mono fun ω hω t => (hω t).1⟩

/-- **Conditional flow lines only depend on the conditional kernels**: they transfer between σ-algebras whose regular
conditional kernels agree almost surely (e.g. σ-algebras equal up to null sets,
`KernelTower.ae_condExpKernel_eq_of_le_aeSigma`). -/
theorem _root_.InteractingSLE.Theorem14.SB.IsCondFlowLineDriverOn.congr_kernel [IsFiniteMeasure P]
    (hW : SB.IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ)
    (hker : ∀ᵐ ω ∂P, condExpKernel P 𝒢 ω = condExpKernel P 𝒢' ω) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢' P F h c bc jc W ζ := by
  filter_upwards [hW, hker] with ω₀ h1 h2 hF
  rw [← h2]
  exact h1 hF

/-- **The chart is kernel-almost surely constant** when it is almost surely a function of a `𝒢`-measurable record
with values in a countably separated space. -/
theorem ae_ae_chart_eq_of_ae_eq_comp [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {R : Type*} [MeasurableSpace R]
    [MeasurableSpace.CountablySeparated R] {X : Ω → R} (hX : Measurable[𝒢] X) {C : R → Chart}
    (hcX : ∀ᵐ ω ∂P, c ω = C (X ω)) : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀ := by
  filter_upwards [Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢 hX,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hcX, hcX] with ω₀ h1 h2 h3
  filter_upwards [h1, h2] with ω e1 e2
  rw [e2, e1, h3]

end Cond

/-! ### The launch chart of a staged piece is fixed by the retained past -/

section Staged

open Exist.StagedLaw

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The run of a staged history through `k` instructions is constant under the conditional kernels given any
σ-algebra containing the retained past** (`pastSigma k`, generated by the records of the first `k` pieces;
`run_eq_of_pastMap_eq`). -/
theorem ae_ae_run_eq_of_le (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hreg : ∀ j < k, ∀ ω, Exist.Staged.IsRegularDriver (E j ω)) (h𝒢 : 𝒢 ≤ mΩ)
    (hpast : pastSigma κ b jumps spec E k ≤ 𝒢) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      ExplState.run κ b jumps spec (fun j => E j ω) k = ExplState.run κ b jumps spec (fun j => E j ω₀) k := by
  let := upgradeStandardBorel (Exist.Staged.PastData k)
  have hm : Measurable[𝒢] (Exist.Staged.pastMap κ b jumps spec E k) :=
    (comap_measurable (Exist.Staged.pastMap κ b jumps spec E k)).mono hpast le_rfl
  have h := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hm
  filter_upwards [h] with ω₀ hω₀
  filter_upwards [hω₀] with ω hω
  exact run_eq_of_pastMap_eq spec hreg hω

/-- **The launch chart of instruction `k` is kernel-almost surely constant** given any σ-algebra containing the retained
past `pastSigma k` (the chart hypothesis `hcc` of the bridge, for the launched pieces of a staged history). -/
theorem ae_ae_launchChart_eq_of_le (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hreg : ∀ j < k, ∀ ω, Exist.Staged.IsRegularDriver (E j ω)) (h𝒢 : 𝒢 ≤ mΩ)
    (hpast : pastSigma κ b jumps spec E k ≤ 𝒢) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      SB.launchChart κ b jumps spec (fun j => E j ω) k = SB.launchChart κ b jumps spec (fun j => E j ω₀) k := by
  filter_upwards [ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec hreg h𝒢 hpast] with ω₀ hω₀
  filter_upwards [hω₀] with ω hω
  unfold SB.launchChart
  rw [launches_run_succ_of_run_eq spec hω]

end Staged

/-! ### K2 composed with the bridge -/

section K2

open Restart.DomainMarkov.Mean

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {nL nR : ℕ}
  {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {𝓗 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P] {bc : Ω → ℝ → ℝ}
  {jc : Ω → Finset ℝ}

/-- **K2 for the flow rule gives the conditional flow line** (`ae_isOptionalHullCoupling_chartTransport` with
`a = θχ`, `k = χ`, followed by `isCondFlowLineDriverOn_of_k2Output`). The hypotheses are those of K2 (the random word
evolution (E), the Gaussian kernels and mean identification (S), the history-marked locality (L)), together with the
word of the conditional data (`hword`), the kernel-almost sure constancy of the chart (`hcc`) and the measurability of
the driver. -/
theorem isCondFlowLineDriverOn_of_k2
    (hE : Sec7.Aux122Disint.IsRandomWordEvolution κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B ζ)
    (hζ0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < ζ ω)
    {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0) (hW' : AdaptedBefore 𝓗' ζ W)
    (hVL' : ∀ i, AdaptedBefore 𝓗' ζ (VL i)) (hVR' : ∀ j, AdaptedBefore 𝓗' ζ (VR j))
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓗𝓜 : ∀ q, 𝓗' q ≤ 𝓜 q) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
            ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ Restart.DomainMarkov.avoidSet W ζ ψ q →
        Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (M q ω) ψ =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q
            (Restart.DomainMarkov.bheProc κ ρL ρR W VL VR ω q) z * ψ z)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓗ℋ : ∀ s, 𝓗' s ≤ ℋ s) (hℋ : ∀ s, ℋ s ≤ mΩ)
    (A : ℝ≥0 → Ω → Set ℂ) (hAm : ∀ s, Measurable[mΩ, hittingSigma] (A s))
    (hAc : ∀ s ω, A s ω ⊆ H ∧ IsOpen (H \ A s ω))
    (hloc : ∀ s, WholeField.IsHistoryAvoidanceLocal (ℋ s) (A s) (WholeField.centredField h u₀) P)
    (hAK : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (s : ℝ≥0∞) < ζ ω →
      H \ A s ω = (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) s))
    (hword : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (bc ω) (jc ω) ∧ flowLineNL (bc ω) (jc ω) 0 = nL ∧
      flowLineNR (bc ω) (jc ω) 0 = nR ∧ truncWord nL nR (padFL κ θ (bc ω) (jc ω)) = ((ΘL ω, ΘR ω), (ρL, ρR)))
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀) (hWm : ∀ t, Measurable (W t)) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ :=
  isCondFlowLineDriverOn_of_k2Output (VL := VL) (VR := VR) hhm hc hliftc hWm hword hcc
    (ae_isOptionalHullCoupling_chartTransport hE hζ0 h𝒢' hW' hVL' hVR' hhm hu₀ hh0 hc hdom hfwd hliftm hliftc
      hlift (θ * chiC κ) (chiC κ) 𝓜 h𝓗𝓜 h𝓜 M hcond hmean ℋ h𝓗ℋ hℋ A hAm hAc hloc hAK)

end K2

end CondDriverBridge

end Theorem14

end InteractingSLE

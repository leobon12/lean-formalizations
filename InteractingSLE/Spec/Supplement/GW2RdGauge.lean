/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEVersion
import InteractingSLE.Spec.Supplement.Q3KernelNoReturn

/-!
# GW2's relative determination, part 4: GB6's gauge readout without `κ < 4`

Packet PROVE-GW2-RELDET (`GW2RdVersionStatement`, handoff §4.1). GB6's live separation readout
(`GB6.GaugeE.hasLiveReadout`: the causal Borel gauge that is positive before the relative life and tends to `0` there,
by contact or escape) uses `κ < 4` for the RETAINED flow line only through the no-return of its trace
(`Q3Kernel.ae_trace_ne_zero_of_isFlowLineDriver`, Aux. lemma 25). GW2's retained curve is the counterflow at
`16/κ > 4`, whose no-return is a separate statement. This file reruns GB6's chain with the no-return as a hypothesis
`hNR` (the proofs of `Q3KernelNoReturn`, `GB6GaugeEChart`, `GB6GaugeESource`, `GB6GaugeELive`, `GB6GaugeETerminal`,
`GB6GaugeEEndpoint`, `GB6GaugeEVersion` verbatim, with the leaf replaced by `hNR`):

* `ae_exists_frozen_retainedChartOff_nr`, `ae_retainedChart_record_nr`, `ae_physicalReadback_nr`,
  `ae_separationRead_regular_nr`, `hasLiveReadout_of_physicalTerminal_nr`, `hasPhysicalTerminalLimits_nr`;
* **`hasLiveReadout_nr`**: the live readout for every retained flow-line driver (any `κ`) whose traces do not return
  to `0`, and every explored curve that is continuous, from `0`, with a transient generating trace on `[0, ∞)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Supp8 Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD Supp8.GB6.RelDrv Supp8.Q3Kernel Exist.StagedLaw
open Supp8.GB6 (relMap relInv)
open Supp8.Q3Rel (invHull relLog relBad IsRetainedChartOff)
open YuanCorollary13 (extDrive extTrace)

/-- **GB6's retained chart for the actual flow, almost surely** (any `κ`, the retained trace not returning to
`0`). For a flow-line driver `Wα` with
generating traces `α`, almost surely on the interior-tip event `{s < ζα, α(s) ∈ ℍ}` there is a frozen flow driver `U`
(continuous, from `0`, with a global Loewner trace, agreeing with the flow driver on `[0, t₂]` for some `t₂ > s`, so
with the same relative map and clock) whose relative map is an `IsRetainedChartOff` of `invHull U s` landing off
`relBad U s`. -/
theorem ae_exists_frozen_retainedChartOff_nr {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∃ (U : ℝ → ℝ) (αr : ℝ → ℂ) (t₂ : ℝ), (s : ℝ) < t₂ ∧ ENNReal.ofReal t₂ < ζα ω ∧ Continuous U ∧ U 0 = 0 ∧
        IsLoewnerTrace U αr ∧ (∀ r ∈ Icc (0 : ℝ) t₂, U r = Wα r.toNNReal ω) ∧
        (∀ r ∈ Icc (0 : ℝ) t₂, αr r = α ω r.toNNReal) ∧
        IsRetainedChartOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s) := by
  filter_upwards [GB6.ae_driver_zero_continuousOn hF, hα, hNR]
    with ω hω hαω hNRω hs hsH
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · exfalso
      exact GB6.ne_zero_of_mem_H hsH (by rw [← h0]; exact hαω.1)
    · exact h0
  exact exists_frozen_retainedChartOff hαω hω.2 hω.1 hs hs0 fun v hv hvs =>
    hNRω (α ω) hαω v hv (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hvs) hs)

/-- Almost surely on the source interior-tip event, the actual retained
record has the retained-chart landing property and the correct inverse tip. -/
theorem ae_retainedChart_record_nr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ}
    {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsRetainedChartOff (invHull (rdrv (gb6Rec s Wα ζα ω)) s)
        (relMap (rdrv (gb6Rec s Wα ζα ω)) s) (relInv (rdrv (gb6Rec s Wα ζα ω)) s)
        (relLog (rdrv (gb6Rec s Wα ζα ω)) s) (relBad (rdrv (gb6Rec s Wα ζα ω)) s) ∧
      Tendsto (fwdMapInv (rdrv (gb6Rec s Wα ζα ω)) s) (𝓝[H] 0) (𝓝 (α ω s)) := by
  filter_upwards [ae_exists_frozen_retainedChartOff_nr hF hα hNR s,
    ae_driver_zero_continuousOn hF, hα] with ω hchart hreg htrace hs hsH
  obtain ⟨U, αr, t₂, hst₂, _, hU, hU0, _, hUeq, _, hΨ⟩ := hchart hs hsH
  let V := rdrv (gb6Rec s Wα ζα ω)
  have hV : Continuous V := continuous_rdrv _
  have hV0 : V 0 = 0 := rdrv_zero _
  have heq : EqOn V U (Icc 0 (s : ℝ)) := by
    intro x hx
    have hrec : V x = Wα x.toNNReal ω := rdrv_recOf_cfE s hreg.1 hreg.2 hs hx.2
    exact hrec.trans (hUeq x ⟨hx.1, hx.2.trans hst₂.le⟩).symm
  refine ⟨retainedChart_of_prefix hU hU0 hV hV0 s.coe_nonneg heq hΨ, ?_⟩
  have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip htrace hreg.2 hreg.1 hs
  have hInv : fwdMapInv U s = fwdMapInv (Ito.rpath (Wα · ω)) s :=
    fwdMapInv_eq_of_eqOn s.coe_nonneg hst₂ hUeq
  change Tendsto (fwdMapInv (Ito.rpath (Wα · ω)) s) (𝓝[H] 0) (𝓝 (α ω s)) at htip
  rw [← hInv] at htip
  exact htip.congr' (eventually_nhdsWithin_of_forall fun z hz =>
    (LP.fwdMapInv_eq_of_eqOn_Icc hV hU hV0 hU0 s.coe_nonneg heq hz).symm)

/-- The decoded record and source relative coordinates reconstruct the
physical trace at every clock value and every live relative capacity time. -/
theorem ae_physicalReadback_nr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) (hs0 : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      gb6Clock s W Wα ω 0 = 0 ∧
      StrictMonoOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} ∧
      ContinuousOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        physicalTrace s (gb6Clock s W Wα ω t).toNNReal (gb6Rec s Wα ζα ω, (fun u => D u ω)) = γ ω t) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0,
        (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ gb6Clock s W Wα ω t = u ∧
        physicalTrace s u (gb6Rec s Wα ζα ω, (fun u => D u ω)) = γ ω t := by
  filter_upwards [ae_retainedChart_record_nr hF hα hNR s, ae_driver_zero_continuousOn hF,
    hα, hW, hC.relative] with ω hchart hreg hflow hcounter hcoords hs hsH
  obtain ⟨hΨ, htip⟩ := hchart hs hsH
  obtain ⟨hw, hw0, hγ⟩ := hcounter
  obtain ⟨hrange, hhulls⟩ := hcoords hs hsH
  let U := rdrv (gb6Rec s Wα ζα ω)
  have hU : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hmap : relMap U s = relMap (Ito.rpath (Wα · ω)) s := record_relMap_eq s hreg.1 hreg.2 hs
  have hclock : relClock U s (Ito.rpath (W · ω)) = relClock (Ito.rpath (Wα · ω)) s (Ito.rpath (W · ω)) :=
    record_relClock_eq s hreg.1 hreg.2 hs _
  have hKrec : fwdHull U s = fwdHull (Ito.rpath (Wα · ω)) s := record_hull_eq s hreg.1 hreg.2 hs
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < gb6Tc s γ α ω → Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath (W · ω)) T)) := by
    intro T hT
    rw [hKrec]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hflow hreg.2 hreg.1 hγ hw.continuousOn hw0
      hs ENNReal.coe_lt_top hT
  have hTc : 0 < gb6Tc s γ α ω := by
    obtain ⟨t, ht, _⟩ := hrange 0 (hC.life_pos ω)
    exact lt_of_le_of_lt bot_le ht
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  obtain ⟨ha0, ham, hac⟩ := relative_clock_regular hU hU0 hsR htip hw hw0 hγ hTc hd
  have hclockN : (fun t : ℝ≥0 => relClock U s (Ito.rpath (W · ω)) t) = gb6Clock s W Wα ω := by
    funext t
    rw [hclock]
    rfl
  have hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
      physicalTrace s (relClock U s (Ito.rpath (W · ω)) t).toNNReal
        (gb6Rec s Wα ζα ω, (fun u => D u ω)) = γ ω t := by
    intro t ht
    obtain ⟨S, htS, hS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    obtain ⟨T, hST, hT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hS
    have hST' : S < T := ENNReal.coe_lt_coe.1 hST
    have htS' : t < S := ENNReal.coe_lt_coe.1 htS
    have hS0 : 0 < S := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ t) htS'
    have hT0 : 0 < T := hS0.trans hST'
    have hlife : ENNReal.ofReal (relClock U s (Ito.rpath (W · ω)) S) < L ω := by
      rw [hclock]
      exact (hhulls S hS).2.1
    have hD : ∀ q ∈ Icc (0 : ℝ) S,
        fwdHull (Ito.rpath (D · ω)) (relClock U s (Ito.rpath (W · ω)) q) =
          relMap U s '' fwdHull (Ito.rpath (W · ω)) q := by
      intro q hq
      rw [hclock, hmap]
      have hqS : q.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hq.2
      have hqTc : (q.toNNReal : ℝ≥0∞) < gb6Tc s γ α ω :=
        (ENNReal.coe_le_coe.2 hqS).trans_lt hS
      have he := (hhulls q.toNNReal hqTc).2.2
      rw [← Real.coe_toNNReal q hq.1]
      exact he
    exact physicalTrace_of_relHulls s hs0 hΨ htip hw hw0 hγ hT0 hS0 hST' (hd T hT)
      (hC.continuous ω) (hC.zero ω) hlife hD htS'.le
  rw [← hclockN]
  refine ⟨ha0, ham, hac, hread, ?_⟩
  intro u hu
  obtain ⟨T, hT, huT⟩ := hrange u hu
  have huT' : (u : ℝ) ≤ relClock U s (Ito.rpath (W · ω)) T := by
    rw [hclock]
    exact huT.le
  obtain ⟨t, ht, hat⟩ := exists_clock_eq (hac.mono fun q hq =>
    (ENNReal.coe_le_coe.2 hq.2).trans_lt hT) ha0 huT'
  have htTc : (t : ℝ≥0∞) < gb6Tc s γ α ω := (ENNReal.coe_le_coe.2 ht.2).trans_lt hT
  refine ⟨t, htTc, hat, ?_⟩
  have hr := hread t htTc
  rw [hat, Real.toNNReal_coe] at hr
  exact hr

/-- The two preterminal clauses of `HasLiveReadout` follow from the original
source hypotheses and the existing source coordinate predicate. -/
theorem ae_separationRead_regular_nr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) (hs0 : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s →
      ContinuousOn (fun t => separationRead s t (gb6Rec s Wα ζα ω, (fun u => D u ω)))
        {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω →
        0 < separationRead s t (gb6Rec s Wα ζα ω, (fun u => D u ω))) ∧
      recordTrace 0 (gb6Rec s Wα ζα ω) = 0 ∧
      ContinuousOn (fun v => recordTrace v (gb6Rec s Wα ζα ω)) (Iic s) ∧
      ContinuousOn (fun u => physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω)))
        {u | (u : ℝ≥0∞) < L ω} := by
  filter_upwards [ae_physicalReadback_nr hF hα hNR hW s hs0 hC, hC.relative,
    ae_gb6RecGood hF hα s, hW, hα, ae_driver_zero_continuousOn hF]
    with ω hread hcoords hgood hcounter hflow hreg hrec
  obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hgood).2 hrec
  obtain ⟨ha0, ham, hac, hat, hcapacity⟩ := hread hs hsH
  obtain ⟨hrange, _⟩ := hcoords hs hsH
  have hγc : Continuous (γ ω) := by
    have hc := hcounter.2.2.2.1
    simp only [le_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  have hX := continuousOn_liveReadback
    (X := fun u => physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω))) ha0 ham hac hrange hγc hat
  have hAe : ∀ v ≤ s, recordTrace v (gb6Rec s Wα ζα ω) = α ω v :=
    fun _ hv => recordTrace_eq s hreg.1 hreg.2 hflow hs hv
  have hA : ContinuousOn (fun v => recordTrace v (gb6Rec s Wα ζα ω)) (Iic s) :=
    (hflow.2.1.mono (fun v hv => show (v : ℝ≥0∞) ≤ ζα ω from
      ((ENNReal.coe_le_coe.2 hv).trans_lt hs).le)).congr (fun v hv => hAe v hv)
  refine ⟨continuousOn_separationRead s _ _ hX hA, ?_, ?_, hA, hX⟩
  · intro t ht
    apply separationRead_pos s t _ _ (hX.mono (fun u hu => (ENNReal.coe_le_coe.2 hu).trans_lt ht)) hA
    intro u hu v hv
    obtain ⟨q, hq, _, hXu⟩ := hcapacity u ((ENNReal.coe_le_coe.2 hu).trans_lt ht)
    rw [hXu, hAe v hv]
    intro hzero
    exact notMem_of_lt_firstContactTime hq ⟨v, ⟨zero_le, hv⟩,
      ((SourceC.sphereInv_eq_iff _ _).2 hzero).symm⟩
  · rw [hAe 0 zero_le]
    exact hflow.1

/-- All other clauses of the corrected live readout follow from the source
hypotheses. Only the physical terminal alternatives are used as a named input. -/
theorem hasLiveReadout_of_physicalTerminal_nr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    (s : ℝ≥0) (hs : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L)
    (hterm : HasPhysicalTerminalLimits s P (gb6Rec s Wα ζα) D L) :
    HullId.HasLiveReadout s P (gb6Rec s Wα ζα) D L := by
  refine ⟨separationRead s, measurable_separationRead s, isCausal_separationRead s, ?_⟩
  filter_upwards [ae_separationRead_regular_nr hF hα hNR hW s hs hC, hterm] with ω hreg ht hrec
  obtain ⟨hc, hp, hA0, hA, hX⟩ := hreg hrec
  refine ⟨hc, hp, ?_⟩
  intro T hT
  have hXI : ContinuousOn (fun u => physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω))) (Iio T) :=
    hX.mono (fun u hu => by rw [← hT]; exact ENNReal.coe_lt_coe.2 hu)
  rcases ht hrec T hT with ⟨z, v, hv, hc, hz⟩ | hz
  · exact tendsto_separationRead_contact s _ _ hs hXI hA hv hz hc
  · exact tendsto_separationRead_escape s _ _ hs hXI hA hA0 hz

/-- The source hypotheses prove the terminal contact-or-escape alternatives
for every relative driver satisfying the full source coordinates. -/
theorem hasPhysicalTerminalLimits_nr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) (hs : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    HasPhysicalTerminalLimits s P (gb6Rec s Wα ζα) D L := by
  classical
  have hW' : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) :=
    hW.mono (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  filter_upwards [ae_physicalReadback_nr hF hα hNR hW' s hs hC, hC.relative,
    ae_gb6RecGood hF hα s, hW, hα, ae_driver_zero_continuousOn hF]
    with ω hread hcoords hgood hcounter hflow hreg hrec T hTL
  obtain ⟨hsζ, hsH⟩ := (mem_gb6TS_iff hgood).2 hrec
  obtain ⟨_, ham, _, _, hcapacity⟩ := hread hsζ hsH
  obtain ⟨_, hhulls⟩ := hcoords hsζ hsH
  let a := gb6Clock s W Wα ω
  let Tc := gb6Tc s γ α ω
  change StrictMonoOn a {t | (t : ℝ≥0∞) < Tc} at ham
  have hbound : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ a t < T := by
    intro t ht
    obtain ⟨hn, hl, _⟩ := hhulls t ht
    refine ⟨hn, ?_⟩
    rw [← hTL] at hl
    simpa only [ENNReal.coe_toReal] using (ENNReal.ofReal_lt_iff_lt_toReal hn ENNReal.coe_ne_top).1 hl
  have hex : ∀ u : ℝ≥0, u < T → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u ∧
      physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω)) = γ ω t := by
    intro u hu
    apply hcapacity u
    rw [← hTL]
    exact ENNReal.coe_lt_coe.2 hu
  let c : ℝ≥0 → ℝ≥0 := fun u => if hu : u < T then (hex u hu).choose else 0
  have hcspec : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < Tc ∧ a (c u) = u ∧
      physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω)) = γ ω (c u) := by
    intro u hu
    simpa only [c, hu, ↓reduceDIte] using (hex u hu).choose_spec
  have hc : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < Tc ∧ a (c u) = u :=
    fun u hu => ⟨(hcspec u hu).1, (hcspec u hu).2.1⟩
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
  have he : (fun u => γ ω (c u)) =ᶠ[𝓝[<] T]
      (fun u => physicalTrace s u (gb6Rec s Wα ζα ω, (fun v => D v ω))) :=
    hu.mono (fun u hu => (hcspec u hu).2.2.symm)
  have hγc : Continuous (γ ω) := by
    have hh := hcounter.2.2.1.2.1
    simp only [le_top, ofPred_true] at hh
    exact continuousOn_univ.1 hh
  rcases eq_top_or_lt_top Tc with htop | hfin
  · right
    have hm : StrictMonoOn a {t | (t : ℝ≥0∞) < ⊤} := by simpa only [htop] using ham
    have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ → 0 ≤ a t ∧ a t < T := by simpa only [htop] using hbound
    have hc' : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < ⊤ ∧ a (c u) = u := by simpa only [htop] using hc
    have hinf := hcounter.2.2.2.comp (tendsto_clockInverse_top hm hb hc')
    exact hinf.congr' (he.mono (fun _ h => congrArg norm h))
  · let C := Tc.toNNReal
    have hTc : Tc = (C : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin.ne).symm
    have hm : StrictMonoOn a {t | (t : ℝ≥0∞) < (C : ℝ≥0∞)} := by simpa only [hTc] using ham
    have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (C : ℝ≥0∞) → 0 ≤ a t ∧ a t < T := by simpa only [hTc] using hbound
    have hc' : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < (C : ℝ≥0∞) ∧ a (c u) = u := by simpa only [hTc] using hc
    have hlim := ((hγc.tendsto C).comp (tendsto_clockInverse_finite hm hb hc')).congr' he
    have hA : IsCompact ((fun v => (α ω v : OnePoint ℂ)) '' Icc 0 s) := by
      have hcompact : IsCompact (α ω '' Icc 0 s) := isCompact_Icc.image_of_continuousOn
        (hflow.2.1.mono fun v hv => (ENNReal.coe_le_coe.2 hv.2).trans hsζ.le)
      simpa only [image_image] using hcompact.image OnePoint.continuous_coe
    obtain ⟨v, hv, hcontact⟩ := firstContactTime_mem
      (continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc)) hA.isClosed hTc
    left
    refine ⟨γ ω C, v, hv.2, ?_, hlim⟩
    rw [recordTrace_eq s hreg.1 hreg.2 hflow hsζ hv.2]
    exact (SourceC.sphereInv_eq_iff _ _).1 hcontact.symm

/-- The original flow-line and transient counterflow trace hypotheses give
the corrected live readout for any proved source relative coordinates. -/
theorem hasLiveReadout_nr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W Wα D : ℝ≥0 → Ω → ℝ}
    {ζα L : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) (hs : 0 < s) (hC : SourceC.RelativeDriverCoordinates s P W Wα ζα γ α D L) :
    HullId.HasLiveReadout s P (gb6Rec s Wα ζα) D L :=
  hasLiveReadout_of_physicalTerminal_nr hF hα hNR
    (hW.mono (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)) s hs hC
    (hasPhysicalTerminalLimits_nr hF hα hNR hW s hs hC)

end InteractingSLE.Theorem14.GW2Rd

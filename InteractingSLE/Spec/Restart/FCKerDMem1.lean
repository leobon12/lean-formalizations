/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerCWire
import InteractingSLE.Spec.Sec5.Aux61ChLocRestart

/-!
# Theorem 1.5's corrected first-contact kernels: the member field of the first path

Packet PROVE-T15-FCKER4 (R82). The member field of `FCK2CapForwardInputsC` for the first canonical chart path
(`FirstContactK2ForwardMembers₁Statement`), from Aux. 77's locality at the physical lines.

At a positive physical line `t`, on the live box `m`, the physical record agrees with the capped record
(`fcPhysicalFiltration_trace_capped`), and the capped record is recovered from the capped shifted histories
(`comap_fcCappedRecord_le_aeSigma_shHist`). So the trace on the live box of every physical event is an event of the
completed capped-history σ-algebra `capSigma` (`measurableSet_inter_liveBox_shHist`), the marks for which the filled
capped union is a history-marked local set (`exists_filled_capped_locality`). The first-contact chart, replaced by the
identity off the live box (`Sec5.Aux61FibData.chartOf`), is then `capSigma`-measurable
(`isMeasChart_chartOf_of_trace`). On the box the filled capped union is the filled line union
(`shCompactPrefix_eq_lineK`), whose complement is the chart image of the Loewner domain
(`image_inv_compl_eq_lineDomain`), and `Aux79.setIntegral_lapTest_of_lineLocal` gives the member identity on the box
(`setIntegral_box_path₁`). The boxes are glued by `hasFCK2CapForwardMembers_of_boxMembers`.

* `harmonicOnNhd_lift_chart`, `chartTransport_congr`, `measurable_piecewise_of_trace`,
  `isMeasChart_chartOf_of_trace`, `measurableSet_inter_liveBox_shHist`, `shCompactPrefix_eq_lineK`, `capSigma`;
* **`setIntegral_box_path₁`**, **`hasFCK2CapForwardMembers_path₁`**;
* **`firstContactK2ForwardMembers₁Statement_of`** (from Lemmas 7.5, 7.7 and Aux. 56),
  `firstContactK2ForwardMembers₁Statement_of_thm12_thm13_lemma76`,
  `firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76_inputs₂`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerD

open Sec6 LocalSets FCAux79 WholeField DomainMarkov DomainMarkov.K2 DomainMarkov.Aux79 Coupling RetAux79
  Sec7.PocketTraversal FCKerC LQGMetric.MarkovZB

universe u

section Chart

variable {Ω : Type*}

/-- The lift of the first-contact chart is harmonic on its domain. -/
theorem harmonicOnNhd_lift_chart [MeasurableSpace Ω] {d : PairData Ω} (hd : d.IsMeasGood) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (d.chart ω).2.2 (d.chart ω).dom := by
  rw [hd.coe_dom_chart ω]
  by_cases hω : ω ∈ d.E
  · rw [PairData.chart_of_mem hω]
    have hdiff := (isCanonicalDerivLog_canonDerivLog (hd.isHPHull ω)).1.1
    intro z hz
    have hn : H \ fillH (d.K ω) ∈ 𝓝 z := (hd.isOpen_D ω).mem_nhds hz
    exact (hdiff.analyticAt hn).harmonicAt_im
  · rw [PairData.chart_of_notMem hω]
    exact InnerProductSpace.harmonicOnNhd_const (0 : ℝ)

/-- Chart transports by equal charts agree. -/
theorem chartTransport_congr {c c' : Chart} (hc : c.IsConformal) (hc' : c'.IsConformal) (he : c = c')
    (σ a k : ℝ) (g : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport hc σ a k g = Chart.chartTransport hc' σ a k g := by
  subst he; rfl

/-- A piecewise function is measurable for `𝒢` if its first piece is measurable for a σ-algebra whose trace on the
piece's set lies in `𝒢`. -/
theorem measurable_piecewise_of_trace {β : Type*} [MeasurableSpace β] {m₁ 𝒢 : MeasurableSpace Ω} {A : Set Ω}
    [DecidablePred (· ∈ A)] (hA : MeasurableSet[𝒢] A)
    (htr : ∀ S, MeasurableSet[m₁] S → MeasurableSet[𝒢] (S ∩ A)) {f g : Ω → β} (hf : Measurable[m₁] f)
    (hg : Measurable[𝒢] g) : Measurable[𝒢] (A.piecewise f g) := by
  intro T hT
  rw [piecewise_preimage]
  exact (htr _ (hf hT)).union ((hg hT).diff hA)

end Chart


section Trace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
open Sec5.Aux61FibData in
/-- The chart `c` on `A` (identity off `A`) is measurable for `𝒢` when `A ∈ 𝒢` and the traces on `A` of the
`m₁`-events lie in `𝒢`, for a chart `c` measurable for `m₁`. -/
theorem isMeasChart_chartOf_of_trace {m₁ 𝒢 : MeasurableSpace Ω} {A : Set Ω} (hA : MeasurableSet[𝒢] A)
    (htr : ∀ S, MeasurableSet[m₁] S → MeasurableSet[𝒢] (S ∩ A)) {c : Ω → Chart}
    (hdom : ∀ z, MeasurableSet[m₁] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[m₁] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hlift : ∀ z, Measurable[m₁] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) :
    @IsMeasChart Ω 𝒢 (chartOf A c) := by
  classical
  have hdomA : ∀ z, {x | z ∈ (chartOf A c x).dom} = ({x | z ∈ (c x).dom} ∩ A) ∪ (Aᶜ ∩ {_x | z ∈ H}) := by
    intro z; ext x
    by_cases hx : x ∈ A
    · simp [chartOf_of_mem hx, hx]
    · simp only [mem_ofPred_eq, chartOf_of_notMem hx, mem_union, mem_inter_iff, hx, and_false, mem_compl_iff,
        not_false_eq_true, true_and, false_or]
      rw [← SetLike.mem_coe, coe_dom_id]
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_⟩
  · rw [hdomA z]
    exact (htr _ (hdom z)).union (hA.compl.inter (MeasurableSet.const _))
  · have e : ({x | z ∈ (chartOf A c x).dom}.indicator fun x => (chartOf A c x).1 z) =
        A.piecewise ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z) (fun _ => if z ∈ H then z else 0) := by
      funext x
      by_cases hx : x ∈ A
      · simp [Set.indicator, Set.piecewise, chartOf_of_mem hx, hx]
      · have hz : z ∈ (Chart.id : Chart).dom ↔ z ∈ H := by rw [← SetLike.mem_coe, coe_dom_id]
        simp only [Set.indicator, Set.piecewise, mem_ofPred_eq, chartOf_of_notMem hx, hx, ite_false, hz]
        split_ifs <;> rfl
    rw [e]
    exact measurable_piecewise_of_trace hA htr (hfwd z) measurable_const
  · have e : ({x | z ∈ (chartOf A c x).dom}.indicator fun x => (chartOf A c x).2.2 z) =
        A.piecewise ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z) (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ A
      · simp [Set.indicator, Set.piecewise, chartOf_of_mem hx, hx]
      · simp [Set.indicator, Set.piecewise, chartOf_of_notMem hx, hx, Chart.id]
    rw [e]
    exact measurable_piecewise_of_trace hA htr (hlift z) measurable_const

/-- **Physical events on a live box are capped-history events up to null sets**: the trace on the live box
`lineBox d t m ∩ {s₀ + t < ζ₁}` of a physical event at the line `t` is an event of the completed σ-algebra of the
capped shifted histories. -/
theorem measurableSet_inter_liveBox_shHist {P : Measure Ω} {d : PairData Ω} (hd : d.IsMeasGood)
    {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (m : ℕ) (t : ℝ≥0)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    (hpair : ∀ᵐ ω ∂P, ∃ σ₁ σ₂, IsFCPair (ηc₁ ω) (ηc₂ ω) σ₁ σ₂)
    {S : Set Ω} (hS : MeasurableSet[fcPhysicalFiltration P d t] S) :
    MeasurableSet[mΩ ⊓ aeSigma (MeasurableSpace.comap (shHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
        (fun ω => cutLife (d.ζ₂ ω) m) t 0) inferInstance) P]
      (S ∩ (lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω})) := by
  refine ⟨(fcPhysicalFiltration P d).le t _ (hS.inter (measurableSet_fcPhysicalLiveBox hd P t m)), ?_⟩
  have h1 := (fcPhysicalFiltration_trace_capped hd hc₁ hc₂ hm₁ hm₂ m t hae hag₁ hag₂ S
    ((le_sup_right : fcPhysicalFiltration P d t ≤ _ ⊔ fcPhysicalFiltration P d t) S hS)).1
  exact StagedEntrance.aeSigma_le_aeSigma (comap_fcCappedRecord_le_aeSigma_shHist hc₁ hc₂ hpair t) _ h1

end Trace

section Union

variable {Ω : Type*}

/-- **On the box the capped compact prefix is the later line union.** -/
theorem shCompactPrefix_eq_lineK {d : PairData Ω} {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (m : ℕ) {ω : Ω} (t : ℝ≥0)
    (hbox : ω ∈ meetBox d m) (hst : d.s₀ ω + t < m) (hlife : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) ≤ d.ζ₁ ω)
    (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s)
    (ha₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hc₁ : ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s)) (hc₂ : ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    (heq : retHist d ω = fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω) :
    shCompactPrefix ηc₁ ηc₂ (m : ℝ≥0) t 0 ω = lineK d t ω := by
  obtain ⟨hE, hs, ht, hsζ, htζ⟩ := mem_meetBox_iff.1 hbox
  have e₁ : recFst (fullHist ηc₁ ηc₂ ω) = d.s₀ ω := by
    have := congrArg (fun y : KHist × KHist => y.1.1.1) heq
    simp only [retHist, fcHist, khistOf, histOf, fcTime₁, hE, ↓reduceIte] at this
    exact this.symm
  have e₂ : recSnd (fullHist ηc₁ ηc₂ ω) = d.t₀ ω := by
    have := congrArg (fun y : KHist × KHist => y.2.1.1) heq
    simp only [retHist, fcHist, khistOf, histOf, fcTime₂, hE, ↓reduceIte] at this
    exact this.symm
  have hI : ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) → Icc 0 (capT (m : ℝ≥0) (u : ℝ≥0∞)) = Icc 0 u := by
    intro u hu
    ext s
    simp only [mem_Icc, zero_le, true_and, le_capT_iff, ENNReal.coe_le_coe]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hu, h⟩⟩
  have i₁ : ηc₁ ω '' Icc 0 (d.s₀ ω + t) = d.η₁ ω '' Icc 0 (d.s₀ ω + t) := by
    refine image_congr fun s hsI => ?_
    have hsle : (s : ℝ≥0∞) ≤ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hsI.2
    have hsm : (s : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
      have : s < (m : ℝ≥0) := lt_of_le_of_lt hsI.2 (by exact_mod_cast hst)
      exact_mod_cast this.le
    rw [hc₁, capTime_of_le, ha₁ _ (hsle.trans hlife)]
    exact le_min (hsle.trans hlife) hsm
  have i₂ : ηc₂ ω '' Icc 0 (d.t₀ ω) = d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    refine image_congr fun s hsI => ?_
    have hsle : (s : ℝ≥0∞) ≤ d.t₀ ω := ENNReal.coe_le_coe.2 hsI.2
    rw [hc₂, capTime_of_le, ha₂ _ (hsle.trans htζ.le)]
    exact le_min (hsle.trans htζ.le) (ENNReal.coe_le_coe.2 (hsI.2.trans ht.le))
  have hst' : d.s₀ ω + t ≤ (m : ℝ≥0) := by exact_mod_cast hst.le
  have ht' : d.t₀ ω ≤ (m : ℝ≥0) := by exact_mod_cast ht.le
  rw [shCompactPrefix, e₁, e₂, ← ENNReal.coe_add, ENNReal.coe_zero, add_zero, hI _ hst', hI _ ht', i₁, i₂, lineK,
    prefixSet]

end Union

section Box

/-- The completed σ-algebra of the capped shifted histories at the line `t` (cap `m`), inside `mΩ`. -/
@[instance_reducible]
def capSigma {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (d : PairData Ω) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ)
    (m : ℕ) (t : ℝ≥0) : MeasurableSpace Ω :=
  mΩ ⊓ aeSigma (MeasurableSpace.comap (shHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
    (fun ω => cutLife (d.ζ₂ ω) m) t 0) inferInstance) P

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {d : PairData Ω} {E F : Set Ω}

open Sec5.Aux61FibData Sec5.Aux61ChLoc in
/-- **The member identity on a box** for the canonical first continuation (Aux. 77's locality at the physical line,
through the filled capped union): on every physical event at a positive line `t` inside the live box `m`, the type
event `F` and the line safe event of the balls, the chart field has the member identities of the balls. -/
theorem setIntegral_box_path₁ (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ d.ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ d.ζ₂)
    (hd : d.IsMeasGood)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (hFE : F ⊆ E) (hFg : ∀ ω ∈ F, IsBoxGood₁ d E x₁ x₂ W γ U ω)
    {t : ℝ≥0} (ht : 0 < t) (m : ℕ) {B : Set Ω}
    (hB : ∀ ω ∈ B, ω ∈ lineBox d t m ∧ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω)
    (Fb : Finset (ℚ × ℚ × ℚ)) (hFb : ballsK Fb ⊆ H) (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens)
    {D : Set Ω} (hD : MeasurableSet[fcPhysicalFiltration P d t] D)
    (hDs : ∀ᵐ ω ∂P, ω ∈ D → (ω ∈ F ∧ ω ∈ lineSafe (fcCapacityClock d E) W U (ballsK Fb) t) ∧ ω ∈ B) :
    ∫ ω in D, Complex.exp (Complex.I *
        (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P =
      projFactor (ballsOpen Fb) f Ξ *
        ∫ ω in D, Complex.exp (Complex.I * (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) Ξ : ℂ)) ∂P := by
  classical
  have hG : ∀ᵐ ω ∂P, ω ∈ d.G := hae.mono fun ω h => h.1
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, -, -, hag₁, hag₂, hloc⟩ :=
    exists_filled_capped_locality h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ (m : ℝ≥0)
  obtain ⟨hcpt, hfillm, hlocal⟩ := hloc t 0
  have hpair := ae_isFCPair_capped_flowLines h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ (m : ℝ≥0) hag₁ hag₂
  set L : Set Ω := lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω} with hL_def
  have htr : ∀ S, MeasurableSet[fcPhysicalFiltration P d t] S →
      MeasurableSet[capSigma P d ηc₁ ηc₂ m t] (S ∩ L) := fun S hS =>
    measurableSet_inter_liveBox_shHist hd hc₁ hc₂ hm₁ hm₂ m t hae hag₁ hag₂ hpair hS
  have hL : MeasurableSet[capSigma P d ηc₁ ηc₂ m t] L := by
    have := htr univ MeasurableSet.univ
    rwa [univ_inter] at this
  have hchart := chart_measurability_fcPhysical (P := P) hd hG t
  have hmc := isMeasChart_chartOf_of_trace hL htr hchart.1 hchart.2.1 hchart.2.2
  have hc' : ∀ ω, (chartOf L d.chart ω).IsConformal := isConformal_chartOf fun ω _ => hd.isConformal_chart ω
  have hD' : MeasurableSet[capSigma P d ηc₁ ηc₂ m t] (D ∩ L) := htr D hD
  have hDD : D =ᵐ[P] (D ∩ L : Set Ω) := by
    filter_upwards [hDs] with ω hω
    refine propext ⟨fun hωD => ⟨hωD, hB ω (hω hωD).2⟩, fun hωD => hωD.1⟩
  have key := setIntegral_lapTest_of_lineLocal (𝒢 := capSigma P d ηc₁ ηc₂ m t) (ζ := U) (W := W) (F := F ∩ L)
    hh.1 hu₀.1 (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) hc' inf_le_left
    (@IsMeasChart.dom Ω (capSigma P d ηc₁ ηc₂ m t) _ hmc)
    (@IsMeasChart.fwd Ω (capSigma P d ηc₁ ηc₂ m t) _ hmc) (@IsMeasChart.lift Ω (capSigma P d ηc₁ ηc₂ m t) _ hmc)
    (continuousOn_lift_chartOf fun ω _ => hd.continuousOn_lift_chart ω)
    (harmonicOnNhd_lift_chartOf fun ω _ => harmonicOnNhd_lift_chart hd ω) (θ₁ * chiC κ) (chiC κ)
    (fcCapacityClock d E t) (fun ω => fillH (shCompactPrefix ηc₁ ηc₂ m t 0 ω)) hfillm
    (fun ω => ⟨fillH_subset_H _, isOpen_H_diff_fillH (hcpt ω).isBounded⟩) hlocal ?_
    (ae_of_all P fun ω _ => isDrvReg_of_continuous hWc hW0 ω) Fb hFb hD' ?_ f Ξ
  · have hX : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ ω ∈ D ∩ L,
        Complex.exp (Complex.I * (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) ψ : ℂ)) =
          Complex.exp (Complex.I * (Chart.chartTransport (hc' ω) 1 (θ₁ * chiC κ) (chiC κ) (h ω) ψ : ℂ)) := by
      intro ψ ω hω
      rw [show hd.chartField κ h ω = Chart.chartTransport (hd.isConformal_chart ω) 1 0 (chiC κ) (h ω) from rfl,
        RetFin.flowField_chartTransport,
        chartTransport_congr (hd.isConformal_chart ω) (hc' ω) (chartOf_of_mem hω.2).symm]
    have hDm : MeasurableSet (D ∩ L) := inf_le_left (α := MeasurableSpace Ω) _ hD'
    rw [setIntegral_congr_set hDD, setIntegral_congr_set hDD, setIntegral_congr_fun hDm (hX _),
      setIntegral_congr_fun hDm (hX _)]
    exact key
  · -- the chart domain of the filled capped union
    filter_upwards [hae, hag₁, hag₂, ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂]
      with ω ha h1 h2 hcmp hω hr
    obtain ⟨hωF, hωL⟩ := hω
    have hl := isFCLine_of_isBoxGood₁ hd hs hclk hWc hW0 (hFE hωF) (hFg ω hωF) ht hωL.2
    rw [chartOf_of_mem hωL, PairData.chart_of_mem (hs.subset (hFE hωF)), image_inv_compl_eq_lineDomain hd hl,
      shCompactPrefix_eq_lineK m t hωL.1.1 hωL.1.2 hl.le_life ha.2.1 ha.2.2 h1 h2 (hcmp.2 hωL.1.1)]
    rfl
  · filter_upwards [hDs] with ω hω hωD
    obtain ⟨⟨hωF, hlt, hdis⟩, hωB⟩ := hω hωD.1
    exact ⟨⟨hωF, hωD.2⟩, hlt, hdis⟩

end Box

section Main

/-- **The member field of the corrected forward inputs for the first canonical chart path**
(`FCK2CapForwardInputsC.members` for path 1), from Lemma 7.5, Lemma 7.7 and Aux. lemma 56 (the inputs of the filled
capped locality). -/
theorem hasFCK2CapForwardMembers_path₁
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞} (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂)
    {W₁ : ℝ≥0 → Ω → ℝ} (hm₁ : ∀ t, Measurable (W₁ t)) (hc₁ : ∀ ω, Continuous (W₁ · ω))
    (hz₁ : ∀ ω, W₁ 0 ω = 0) (hg₁ : ∀ᵐ ω ∂P, ω ∈ meetSet d → IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω))
    (q : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)) (hFb : ballsK Fb ⊆ H) (f : zsSub (ballsU Fb))
    (Ξ : TestOn upperHalfPlaneOpens) :
    HasFCK2CapForwardMembers P (fcRetainedDriverFiltration P hd W₁ hm₁ q)
      {ω | ω ∈ meetSet d ∧ (q : ℝ≥0∞) < U₁ ω ∧
        Disjoint (ballsK Fb) (fwdHull (fun r : ℝ => W₁ r.toNNReal ω) q)}
      (fun ω => Complex.exp (Complex.I *
        (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) (lapTest (ballsOpen Fb) f + Ξ) : ℂ)))
      (fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) Ξ : ℂ)))
      (projFactor (ballsOpen Fb) f Ξ) := by
  classical
  subst hζ₁ hζ₂
  obtain ⟨E, hEr, hEM, hME, hs, -, hclk, -⟩ :=
    exists_fcContEvent h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl hae
  have hG : ∀ᵐ ω ∂P, ω ∈ d.G := hae.mono fun ω h => h.1
  have hcan := ae_canon_cGamma₁ hd hs hclk hcanon
  have hgood : ∀ᵐ ω ∂P, (ω ∈ E → IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
      ((∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U₁ ω → γ₁ ω q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) ∧
        U₁ ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω) ∧ InjOn (γ₁ ω) {r | (r : ℝ≥0∞) ≤ U₁ ω}) ∧
      IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁ ∧ IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂ := by
    filter_upwards [hg₁, hcan, ae_canon_injOn_closed_life h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl hae hcanon,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂, hae]
      with ω hgω hcω hiω hp₁ hp₂ ha
    exact ⟨fun hω => ⟨hgω (hEM hω), hcω hω, (hiω (hEM hω)).1⟩,
      Sec7.SideHeightBox.isPathGood_congr hp₁ ha.2.1, Sec7.SideHeightBox.isPathGood_congr hp₂ ha.2.2⟩
  obtain ⟨Good, hGm, hGae, hGp⟩ := exists_measurable_good hgood
  set F : Set Ω := E ∩ Good with hFdef
  have hFr : MeasurableSet[retSigma d P] F := hEr.inter (measurableSet_retSigma_of_ae hGm hGae)
  have hF0 : MeasurableSet[fcPhysicalFiltration P d 0] F := retSigma_le_fcPhysicalFiltration P d 0 _ hFr
  have hFE : F ⊆ E := fun ω hω => hω.1
  have hFgood : ∀ ω ∈ F, IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
      (∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U₁ ω → γ₁ ω q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) ∧
        U₁ ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω := fun ω hω =>
    ⟨((hGp ω hω.2).1 hω.1).1, ((hGp ω hω.2).1 hω.1).2.1⟩
  have hFg : ∀ ω ∈ F, IsBoxGood₁ d E x₁ x₂ W₁ γ₁ U₁ ω := fun ω hω =>
    ⟨(hFgood ω hω).1, (hFgood ω hω).2.1, (hFgood ω hω).2.2, ((hGp ω hω.2).1 hω.1).2.2,
      (hGp ω hω.2).2.1, (hGp ω hω.2).2.2⟩
  refine hasFCK2CapForwardMembers_mono (S' := {ω | ω ∈ F ∧ (q : ℝ≥0∞) < U₁ ω ∧
      Disjoint (ballsK Fb) (fwdHull (fun r : ℝ => W₁ r.toNNReal ω) q)}) ?_ ?_
  · filter_upwards [hGae, hME] with ω hωG hωE hω
    exact ⟨⟨hωE hω.1, hωG⟩, hω.2⟩
  set B : ℝ≥0 → ℕ → Set Ω := fun t => disjointed fun m : ℕ =>
    lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω} with hB_def
  have hBG : ∀ t m, MeasurableSet[fcPhysicalFiltration P d t] (B t m) := fun t m =>
    MeasurableSet.disjointed (fun k => measurableSet_fcPhysicalLiveBox hd P t k) m
  have hBsub : ∀ t m ω, ω ∈ B t m → ω ∈ lineBox d t m ∧ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω :=
    fun t m ω hω => disjointed_subset _ m hω
  have hXm : ∀ ψ : TestOn upperHalfPlaneOpens, Integrable (fun ω => Complex.exp (Complex.I *
      (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) ψ : ℂ))) P := fun ψ =>
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp
      ((Exist.measurable_flowField 0 (θ₁ * chiC κ)).comp (hd.measurable_chartField κ hh.1)))
  refine hasFCK2CapForwardMembers_of_boxMembers (𝓖 := fcPhysicalFiltration P d)
    (VL := geomLW W₁ (fun _ : Ω => (Fin.elim0 : Fin 0 → ℝ)))
    (VR := geomRW W₁ (fun _ : Ω => (Fin.elim0 : Fin 0 → ℝ))) hd hm₁
    (continuous_fcCapacityClock hd hs hclk) (monotone_fcCapacityClock hd hs hclk)
    (fcCapacityClock_zero hd hs hclk) (measurable_fcCapacityClock_fcPhysical hd hG hs hEr)
    (measurable_retHist_fcPhysical hd)
    (measurable_indicator_driver_fcPhysical hd hG hs hclk hEr hm₁ hc₁ hz₁
      (hg₁.mono fun ω h hω => h (hEM hω)) hcan) Fb hFb q
    (fun t => measurableSet_inter_lineSafe_fcPhysical hd hG hs hclk hEr hF0 hFE hEM hFgood
      (isCompact_ballsK Fb) hFb t) ?_
    (ae_of_all P fun ω _ => FCDet.isForceReg_thr hz₁ hc₁ _ _ U₁ ω) B
    (fun t => disjoint_disjointed _) hBG ?_ (fun t _ => fcPhysicalFiltration P d t) (fun _ _ => le_rfl)
    (fun t _ => (fcPhysicalFiltration P d).le t) (hXm _) (hXm _) ?_
  · -- reach
    refine ae_of_all P fun ω hω hq => ?_
    have hU := (hFgood ω hω).2.2
    exact exists_le_fcCapacityClock hd hs hclk (hFE hω) (hU ▸ hq)
  · -- cover
    intro t
    refine ae_of_all P fun ω hω hS => ?_
    have hU := (hFgood ω hω).2.2
    have hlive := (coe_fcCapacityClock_lt_cLife_iff hd hs hclk (hFE hω) t).1 (hU ▸ hS.1)
    obtain ⟨m, hm⟩ := exists_mem_lineBox (hEM (hFE hω)) t
    have hmem : ω ∈ ⋃ k, B t k := by
      rw [iUnion_disjointed]
      exact mem_iUnion.2 ⟨m, hm, hlive⟩
    exact mem_iUnion.1 hmem
  · -- the per-box member identity
    intro t ht m D hD hDs
    exact setIntegral_box_path₁ h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hae hu₀ hs hclk hc₁ hz₁ hFE hFg ht m
      (hBsub t m) Fb hFb f Ξ hD hDs

end Main

end InteractingSLE.Restart.FCPlumb.FCKerD

namespace InteractingSLE.Restart.FCPlumb

open LQGMetric.MarkovZB

universe u

/-- **`FirstContactK2ForwardMembers₁Statement` from Lemma 7.5, Lemma 7.7 and Aux. lemma 56.** -/
theorem firstContactK2ForwardMembers₁Statement_of (h75 : Theorem15.Lemma75Statement.{u})
    (h77 : Supp10.Lemma77Statement.{u}) (h56 : RetainedRangeEntranceStatement.{u}) :
    FirstContactK2ForwardMembers₁Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg q Fb hFb f Ξ
  exact FCKerD.hasFCK2CapForwardMembers_path₁ h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
    hcanon hm₁ hc₁ hz₁ (hg.mono fun _ h hω => (h hω).1) q Fb hFb f Ξ

/-- **`FirstContactK2ForwardMembers₁Statement` from Theorems 1.2–1.3 and Lemma 7.6** (R48: the consumer is
Theorem 1.5). -/
theorem firstContactK2ForwardMembers₁Statement_of_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h76 : Sec7.Lemma76Statement.{u}) : FirstContactK2ForwardMembers₁Statement.{u} :=
  firstContactK2ForwardMembers₁Statement_of (lemma75Statement_of_thm12_thm13 h12 h13)
    (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76) firstContact_retainedRangeEntranceStatement

/-- **The corrected forward-kernel statement from the second path's inputs alone** (with Theorems 1.2–1.3 and
Lemma 7.6): the first path's two fields are proved. -/
theorem firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76_inputs₂
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h76 : Sec7.Lemma76Statement.{u}) (h2 : FirstContactK2ForwardInputs₂Statement.{u}) :
    FirstContactK2ForwardKernelsCStatement.{u} :=
  firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76 h12 h13 h76
    (firstContactK2ForwardMembers₁Statement_of_thm12_thm13_lemma76 h12 h13 h76) h2

end InteractingSLE.Restart.FCPlumb

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb3Random
import InteractingSLE.Spec.Sec7.ContinuityProbBase
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Spec.Sec2.Assembly2UpTo
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# §7.3: band transfer — the trace through a Girsanov deletion of a separated force group

Packet PROVE-SEC7-C4. Specification §7.3, Aux. lemma 103 (`source/spec/p337-384.md` L288–L305, p. 349): "If
initially `U ≤ 1/2`, use the left band and stop it on first reaching `U = 2/3` or the continuation threshold.
Throughout this band all right gaps are at least `D_0/3`. Deleting the entire right group changes the driver by a
bounded drift on every bounded physical-time interval and leaves at most `N − 1` active groups. Girsanov on the
integrated equations, with the deleted locations retained as passive coordinates for the stopping rule, transfers the
induction hypothesis." The same transfer closes Aux. lemma 101 and is used in Aux. lemmas 102, 106 and 113.

* `fullTraceSet`, `FullTrace`, `ae_mem_lawSetS_fullTraceSet`: a complete separated word at which Wiener-almost every
  path is solvable has, for Wiener-almost every path, a solution with the trace event up to its lifetime and up to
  every rational time before it.
* `le_lifetime_of_upTo`: a local solution before `τ` and a maximal solution driven by the same path agree before
  `τ`, and `τ` is at most the maximal lifetime (local pathwise uniqueness and the maximality clause).
* **`ae_isGeneratingTrace_of_changeWeights`** (band transfer): for an evolution of a separated word and a bounded
  stopping time `τ` before which every mark whose weight changes stays `δ`-far from the driver, if the changed word has
  the full trace event Wiener-almost surely, then almost surely the driver has a continuous generating trace on
  `[0, τ]`. Proof: Girsanov (`girsanov_changeWeights`) makes the process a local solution of the changed word driven
  by a Brownian motion `B̃`; Wiener-almost every path, hence `B̃`, drives a maximal solution of the changed word with
  the trace event; the local solution coincides with it before `τ ≤` its lifetime; equivalence of measures.
* `hitTime`, `le_of_lt_hitTime`, `isStoppingTime_hitTime`: rational hitting times, a lower bound before them, and
  their stopping-time property for right-continuous filtrations.
* `horizonR`, `horizonL`: the band horizons (first rational time at which a mark of the deleted side is within `2δ`,
  capped by `n` and the lifetime); `bandSetR`, `bandSetL`: the Borel code events "trace up to the band horizon".
* **`ae_traceEvent_horizonR`**, `ae_traceEvent_horizonL`: the band transfer for these horizons.
* `codeLaw_compl_bandSetR_eq_zero`, `codeLaw_compl_bandSetL_eq_zero`: the band events have canonical law one at every
  separated start where the word is solvable and the reduced word has the full trace event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace Band

open Sec2 Sec2.Assembly Sec2.Restart RandRestart Girsanov

variable {nL nR : ℕ}

/-! ### The full trace event on solution codes -/

/-- Solution codes whose decoded driver has the trace event up to the lifetime and up to every rational time
before it. -/
def fullTraceSet : Set (XCode nL nR) :=
  traceCodeSet ∩ ⋂ r : ℚ, {x | ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < cζ x → (cw x, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞)) ∈ traceSet}

theorem measurable_cw : Measurable (cw : XCode nL nR → ℝ≥0 → ℝ) :=
  measurable_pi_iff.2 fun t => measurable_dec_at measurable_code_w t

theorem measurableSet_fullTraceSet : MeasurableSet (fullTraceSet (nL := nL) (nR := nR)) := by
  refine measurableSet_traceCodeSet.inter (MeasurableSet.iInter fun r => ?_)
  have h1 : MeasurableSet {x : XCode nL nR | ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < cζ x} :=
    measurableSet_lt measurable_const measurable_cζ
  have h2 : MeasurableSet {x : XCode nL nR | (cw x, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞)) ∈ traceSet} :=
    (measurable_cw.prodMk measurable_const) measurableSet_traceSet
  have e : {x : XCode nL nR | ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < cζ x → (cw x, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞)) ∈ traceSet} =
      {x | ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < cζ x}ᶜ ∪ {x | (cw x, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞)) ∈ traceSet} := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [e]
  exact h1.compl.union h2

/-- The path predicate coded by `fullTraceSet`. -/
def FullTrace (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  TraceEvent w ζ ∧ ∀ r : ℚ, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < ζ → TraceEvent w ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞)

theorem fullTrace_congr (w w' : ℝ≥0 → ℝ) (ζ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = w' t) (hw : FullTrace w ζ) : FullTrace w' ζ :=
  ⟨hw.1.congr h, fun r hr => (hw.2 r hr).congr fun t ht => h t (ht.trans hr)⟩

theorem mem_fullTraceSet_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} :
    ∀ x ∈ CRelF a ρL ρR, HasLimW x → (x ∈ (fullTraceSet (nL := nL) (nR := nR)) ↔ FullTrace (cw x) (cζ x)) := by
  intro x hx hl
  have hp : IsIntegratedSLEPath a (startOf x).1 (startOf x).2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
    hx.1.2.2
  have hr : ∀ r : ℚ, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < cζ x →
      ((cw x, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞)) ∈ traceSet ↔ TraceEvent (cw x) ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞)) := by
    intro r hrζ
    refine mem_traceSet_iff (hp.isForcePath.continuousOn_w.mono fun t ht => ?_) hp.1 fun _ _ => ?_
    · exact (show (t : ℝ≥0∞) < (Real.toNNReal r : ℝ≥0) from ht).trans hrζ
    · refine ⟨cw x (Real.toNNReal r), ?_⟩
      have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} := isOpen_lt ENNReal.continuous_coe continuous_const
      have hc : ContinuousAt (cw x) (Real.toNNReal r : ℝ≥0) :=
        hp.isForcePath.continuousOn_w.continuousAt (hopen.mem_nhds hrζ)
      have e : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞).toNNReal = (Real.toNNReal r : ℝ≥0) := ENNReal.toNNReal_coe _
      rw [e]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_traceCodeSet_iff hx hl).1 h1, fun r hrζ => (hr r hrζ).1 ?_⟩
    exact mem_iInter.1 h2 r hrζ
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_traceCodeSet_iff hx hl).2 h1, mem_iInter.2 fun r hrζ => (hr r hrζ).2 (h2 r hrζ)⟩

/-- A trace event up to `ζ` gives the trace event up to every earlier finite time. -/
theorem traceEvent_mono {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : TraceEvent w ζ) {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ ζ) :
    TraceEvent w r := by
  obtain ⟨η, hη, -⟩ := h
  exact ⟨η, hη.mono_horizon hr, fun h => absurd h ENNReal.coe_ne_top⟩

theorem fullTrace_of_traceEvent {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : TraceEvent w ζ) : FullTrace w ζ :=
  ⟨h, fun _ hr => traceEvent_mono h hr.le⟩

/-- **A complete separated word: Wiener-almost every path drives a solution with the full trace event.** -/
theorem ae_mem_lawSetS_fullTraceSet {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hc : LP.IsCompleteForceWord.{u} κ s.1 s.2 ρL ρR)
    (hsep : SepStart s) (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR) :
    ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ ρL ρR (fullTraceSet (nL := nL) (nR := nR)) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{u} hsep hsolv
  have htr : ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω) (ζ ω) := hc P 𝓕 W VL VR B ζ hE
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (Φ := FullTrace) measurableSet_fullTraceSet
    mem_fullTraceSet_iff fullTrace_congr
  have hΦ : ∀ᵐ ω ∂P, FullTrace (fun t => W t ω) (ζ ω) := htr.mono fun ω h => fullTrace_of_traceEvent h
  have h1 : P {ω | FullTrace (fun t => W t ω) (ζ ω)} = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← measure_univ (μ := P)]
    exact measure_mono_ae (hΦ.mono fun ω h _ => h)
  rw [h1] at e
  have hm : MeasurableSet (Prod.mk s ⁻¹' restartSetS κ ρL ρR (fullTraceSet (nL := nL) (nR := nR))) :=
    (measurableSet_restartSetS measurableSet_fullTraceSet).preimage measurable_prodMk_left
  have h2 : wienerPath (Prod.mk s ⁻¹' restartSetS κ ρL ρR (fullTraceSet (nL := nL) (nR := nR))) = 1 :=
    e.symm
  rw [← measure_univ (μ := wienerPath)] at h2
  exact (ae_iff_measure_eq hm.nullMeasurableSet).2 h2


/-! ### A local solution before `τ` and a maximal solution driven by the same path -/

section Local

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ ζ : ℝ≥0∞}

/-- **A local solution cannot outlive the maximal one.** For a separated start, a local solution before `τ` and a
solution of Definition 2.1 (maximal lifetime `ζ`) driven by the same path agree before `min τ ζ`, and `τ ≤ ζ`. -/
theorem le_lifetime_of_upTo (hsep : ∀ i j, xL i < xR j) (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    (h' : IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b ζ) :
    τ ≤ ζ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := by
  have h'u : IsSLEPathUpTo a xL xR ρL ρR w' vL' vR' b ζ := h'.isSLEPathUpTo le_rfl
  have hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < min τ ζ →
      w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := fun t ht =>
    UpTo.agree_of_lt_min hsep h h.driverEq h'u h'u.driverEq ht
  have hp := h'.isForcePath
  have hle : τ ≤ ζ := by
    by_contra hlt
    rw [not_le] at hlt
    have hfin : ζ ≠ ⊤ := ne_top_of_lt hlt
    set T := ζ.toNNReal with hTdef
    have hT : (T : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hfin
    have hTτ : (T : ℝ≥0∞) < τ := by rw [hT]; exact hlt
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with h0 | h0
    · have hz : ζ = 0 := by rw [← hT, ← h0]; rfl
      have hthr := hp.threshold_of_eq_zero hz
      have hnt := h.not_threshold (t := 0) (by rw [← h0] at hTτ; exact_mod_cast hTτ)
      rw [h.w_zero] at hnt
      have e1 : (fun i => vL i 0) = xL := funext h.vL_zero
      have e2 : (fun j => vR j 0) = xR := funext h.vR_zero
      rw [e1, e2] at hnt
      exact hnt hthr
    · have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < τ} := isOpen_lt ENNReal.continuous_coe continuous_const
      have hca : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < τ} → ContinuousAt f T :=
        fun hf => hf.continuousAt (hopen.mem_nhds hTτ)
      have hcont : ContinuousAt (fun t => (w t, fun i => vL i t, fun j => vR j t)) T :=
        (hca h.continuousOn_w).prodMk ((continuousAt_pi.2 fun i => hca (h.continuousOn_vL i)).prodMk
          (continuousAt_pi.2 fun j => hca (h.continuousOn_vR j)))
      have hlim : Tendsto (fun t => (w' t, fun i => vL' i t, fun j => vR' j t)) (𝓝[<] T)
          (𝓝 (w T, fun i => vL i T, fun j => vR j T)) := by
        refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have htT : (t : ℝ≥0∞) < T := by exact_mod_cast ht
        obtain ⟨e1, e2, e3⟩ := hag t (lt_min (htT.trans hTτ) (by rw [← hT]; exact htT))
        simp only [e1, e2, e3]
      exact h.not_threshold hTτ (hp.threshold_of_tendsto h0 hT hlim)
  refine ⟨hle, fun t ht => hag t (lt_min ht (ht.trans_le hle))⟩

end Local

/-! ### Band transfer -/

section Transfer

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ τ : Ω → ℝ≥0∞}

/-- **Band transfer: the trace through a change of weights of separated marks** (Specification §7.3, Aux. lemma
103, L292: "Deleting the entire right group changes the driver by a bounded drift on every bounded physical-time
interval and leaves at most `N − 1` active groups. Girsanov on the integrated equations, with the deleted locations
retained as passive coordinates for the stopping rule, transfers the induction hypothesis"; Aux. lemma 101, last
paragraph). Let `(W, V, B)` be an evolution of a separated word, `τ ≤ ζ ∧ T` a stopping time before which every mark
whose weight changes from `(ρL; ρR)` to `(ρL'; ρR')` stays at distance `≥ δ > 0` from the driver, and suppose
Wiener-almost every path drives a solution of the new word from the same start with the full trace event (for
instance: the new word is complete, `ae_mem_lawSetS_fullTraceSet`). Then almost surely the driver has a continuous
generating trace on `[0, τ]`. -/
theorem ae_isGeneratingTrace_of_changeWeights [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    (ρL' : Fin nL → ℝ) (ρR' : Fin nR → ℝ) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR' i ≠ ρR i → δ ≤ |W t ω - VR i t ω|)
    (hfull : ∀ᵐ f ∂wienerPath, ((xL, xR), enc f) ∈ lawSetS κ ρL' ρR' (fullTraceSet (nL := nL) (nR := nR))) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η := by
  obtain ⟨hQ, hE'⟩ := hE.isSLEEvolutionUpTo.girsanov_changeWeights hκ ρL' ρR' hτ hτζ hτT hδ hgap
  set Q := girsanovMeasure P 𝓕 B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) (T + 1) with hQdef
  set B₁ := girsanovProcess B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) with hB₁def
  have : IsProbabilityMeasure Q := hQ.isProb
  obtain ⟨B', hm, hc, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 hE'.brownian.1
  have hpm : Measurable fun ω (s : ℝ≥0) => B' s ω := measurable_pi_iff.2 hm
  have hlaw : Q.map (fun ω s => B' s ω) = wienerPath := map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm
  rw [← hlaw] at hfull
  have hgood := ae_of_ae_map hpm.aemeasurable hfull
  have hlim := hQ.ac.ae_le (hE.ae_tendsto_threshold hκ)
  have hpath := hQ.ac.ae_le hE.2.2.2.2
  refine hQ.ac'.ae_le ?_
  filter_upwards [hgood, hae, hE'.ae_path, hlim, hpath] with ω hg hb hp hl hpa
  set f : ℝ≥0 → ℝ := fun s => B' s ω with hf
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxeq⟩ := hg
  simp only [Prod.mk.injEq] at hxeq
  have hxC : x ∈ CRel κ xL xR ρL' ρR' := mem_cRelF_iff.1 ⟨hxF, hxeq.1⟩
  have hxp : IsIntegratedSLEPath κ xL xR ρL' ρR' (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hcb : cb x = f := by
    funext t
    show dec x.1 t = f t
    rw [hxeq.2]
    exact dec_enc (hc ω).continuousWithinAt
  rw [hcb] at hxp
  have hp' : IsSLEPathUpTo κ xL xR ρL' ρR' (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) f
      (τ ω) := hp.congr_b fun t _ => hb t
  obtain ⟨hle, hag⟩ := le_lifetime_of_upTo hsep hp' hxp
  have hcont : ContinuousOn (cw x) {t | (t : ℝ≥0∞) < cζ x} := hxp.isForcePath.continuousOn_w
  rcases hle.lt_or_eq with hlt | heq
  · -- a rational time strictly between `τ` and the new lifetime
    obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    have hx2 := mem_iInter.1 hxS.2 q hq2
    have hev : TraceEvent (cw x) ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) := by
      refine (mem_traceSet_iff (hcont.mono fun t ht => ?_) hxp.1 fun _ _ => ?_).1 hx2
      · exact (show (t : ℝ≥0∞) < (Real.toNNReal q : ℝ≥0) from ht).trans hq2
      · refine ⟨cw x (Real.toNNReal q), ?_⟩
        have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} :=
          isOpen_lt ENNReal.continuous_coe continuous_const
        rw [ENNReal.toNNReal_coe]
        exact (hcont.continuousAt (hopen.mem_nhds hq2)).tendsto.mono_left nhdsWithin_le_nhds
    obtain ⟨η, hη, -⟩ := hev
    exact ⟨η, IsGeneratingTrace.congr_lt (hη.mono_horizon hq1.le) fun t ht => (hag t ht).1⟩
  · -- the new solution dies exactly at `τ`: it inherits the left limit of the driver there
    have hHL : HasLimW x := by
      intro h0 hfin
      have hTζ : (((cζ x).toNNReal : ℝ≥0) : ℝ≥0∞) = cζ x := ENNReal.coe_toNNReal hfin.ne
      have hT0 : 0 < (cζ x).toNNReal := by
        have : (0 : ℝ≥0∞) < ((cζ x).toNNReal : ℝ≥0∞) := by rw [hTζ]; exact h0
        exact_mod_cast this
      have hW : ∃ w₀ : ℝ, Tendsto (fun t => W t ω) (𝓝[<] (cζ x).toNNReal) (𝓝 w₀) := by
        rcases (hτζ ω).lt_or_eq with hlt' | heq'
        · refine ⟨W (cζ x).toNNReal ω, ?_⟩
          have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
            isOpen_lt ENNReal.continuous_coe continuous_const
          have hlt'' : (((cζ x).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hTζ, ← heq]; exact hlt'
          exact (hpa.isForcePath.continuousOn_w.continuousAt (hopen.mem_nhds hlt'')).tendsto.mono_left
            nhdsWithin_le_nhds
        · have hTz : (((cζ x).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ ω := by rw [hTζ, ← heq, heq']
          obtain ⟨w₀, vL₀, vR₀, hlim', -⟩ := hl _ hT0 hTz
          exact ⟨w₀, ((continuous_fst.tendsto _).comp hlim')⟩
      obtain ⟨w₀, hw₀⟩ := hW
      refine ⟨w₀, hw₀.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (t : ℝ≥0∞) < τ ω := by rw [heq, ← hTζ]; exact_mod_cast ht
      exact (hag t ht').1
    have hev : TraceEvent (cw x) (cζ x) := (mem_traceCodeSet_iff hxF hHL).1 hxS.1
    obtain ⟨η, hη, -⟩ := hev
    rw [← heq] at hη
    exact ⟨η, IsGeneratingTrace.congr_lt hη fun t ht => (hag t ht).1⟩

end Transfer

/-! ### Rational hitting times -/

open Classical in
/-- The infimum of the rational times `r < ζ` at which `p` holds (`⊤` if there is none). -/
def hitTime (p : ℝ≥0 → Prop) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ r : ℚ, if ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < ζ ∧ p (Real.toNNReal r) then
    ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) else ⊤

theorem hitTime_le {p : ℝ≥0 → Prop} {ζ : ℝ≥0∞} {r : ℚ} (hr : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < ζ)
    (hp : p (Real.toNNReal r)) : hitTime p ζ ≤ (Real.toNNReal r : ℝ≥0) := by
  classical
  refine (iInf_le _ r).trans ?_
  simp only [hr, hp, and_self, ↓reduceIte, le_refl]

/-- No hit before `u` (and before `ζ`): `u ≤ hitTime`. -/
theorem le_hitTime {p : ℝ≥0 → Prop} {ζ u : ℝ≥0∞}
    (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < u → (s : ℝ≥0∞) < ζ → ¬ p s) : u ≤ hitTime p ζ := by
  classical
  refine le_iInf fun r => ?_
  split_ifs with hc
  · by_contra hlt
    exact h _ (not_le.1 hlt) hc.1 hc.2
  · exact le_top

theorem hitTime_mono {p p' : ℝ≥0 → Prop} {ζ : ℝ≥0∞} (h : ∀ s, p s → p' s) : hitTime p' ζ ≤ hitTime p ζ := by
  classical
  refine iInf_mono fun r => ?_
  by_cases h2 : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < ζ ∧ p (Real.toNNReal r)
  · have h1 : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < ζ ∧ p' (Real.toNNReal r) := ⟨h2.1, h _ h2.2⟩
    simp only [h1, h2, and_self, ↓reduceIte, le_refl]
  · simp only [h2, ↓reduceIte, le_top]

theorem hitTime_congr {p p' : ℝ≥0 → Prop} {ζ : ℝ≥0∞} (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → (p s ↔ p' s)) :
    hitTime p ζ = hitTime p' ζ := by
  classical
  unfold hitTime
  refine iInf_congr fun r => ?_
  by_cases hr : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < ζ
  · simp only [hr, h _ hr, true_and]
  · simp only [hr, false_and, ↓reduceIte]

theorem hitTime_lt_iff {p : ℝ≥0 → Prop} {ζ : ℝ≥0∞} {s : ℝ≥0∞} :
    hitTime p ζ < s ↔ ∃ r : ℚ, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < s ∧
      ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < ζ ∧ p (Real.toNNReal r) := by
  classical
  unfold hitTime
  rw [iInf_lt_iff]
  refine exists_congr fun r => ?_
  split_ifs with hc
  · exact ⟨fun h => ⟨h, hc⟩, fun h => h.1⟩
  · refine ⟨fun h => absurd h (not_lt.2 le_top), fun h => absurd ⟨h.2.1, h.2.2⟩ hc⟩

/-- **Before the hitting time of `{g ≤ c}`, a function continuous before `ζ` stays at least `c`.** -/
theorem le_of_lt_hitTime {g : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hg : ContinuousOn g {t | (t : ℝ≥0∞) < ζ}) {c : ℝ}
    {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ) (ht : (t : ℝ≥0∞) < hitTime (fun s => g s ≤ c) ζ) : c ≤ g t := by
  by_contra hlt
  rw [not_le] at hlt
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hca : ContinuousAt g t := hg.continuousAt (hopen.mem_nhds htζ)
  -- a neighbourhood of `t` on which `g < c`, inside `{s < ζ}`
  have hev : ∀ᶠ s in 𝓝 t, g s < c ∧ (s : ℝ≥0∞) < ζ ∧ (s : ℝ≥0∞) < hitTime (fun s => g s ≤ c) ζ :=
    Filter.Eventually.and (hca.eventually (gt_mem_nhds hlt)) (Filter.Eventually.and (hopen.mem_nhds htζ)
      ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ht))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < t + ε by linarith)
  have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg t).trans hq1.le
  have hqt : (Real.toNNReal q : ℝ) = q := Real.coe_toNNReal _ hq0
  have hd : dist (Real.toNNReal q) t < ε := by
    rw [NNReal.dist_eq, hqt, abs_lt]
    constructor <;> linarith
  obtain ⟨h1, h2, h3⟩ := hball hd
  exact (not_le.2 h3) (hitTime_le h2 h1.le)

/-! ### Measurability -/

theorem measurable_hitTime {α : Type*} [MeasurableSpace α] {p : α → ℝ≥0 → Prop} {ζ : α → ℝ≥0∞}
    (hζ : Measurable ζ) (hp : ∀ s : ℝ≥0, MeasurableSet {x | p x s}) :
    Measurable fun x => hitTime (p x) (ζ x) := by
  classical
  refine Measurable.iInf fun r => Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt measurable_const hζ).inter (hp _)

/-- **A rational hitting time is a stopping time of a right-continuous filtration** when the hitting events at
rational times are adapted. -/
theorem isStoppingTime_hitTime {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [𝓕.IsRightContinuous] {p : Ω → ℝ≥0 → Prop} {ζ : Ω → ℝ≥0∞}
    (hp : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω ∧ p ω s}) :
    IsStoppingTime 𝓕 fun ω => (hitTime (p ω) (ζ ω) : WithTop ℝ≥0) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
  have hm : MeasurableSet[𝓕 i] (⋃ r : ℚ,
      {ω | ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < (i : ℝ≥0∞)} ∩
        {ω | ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ p ω (Real.toNNReal r)}) := by
    refine MeasurableSet.iUnion fun r => ?_
    by_cases hr : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < (i : ℝ≥0∞)
    · simp only [hr, ofPred_true, univ_inter]
      exact 𝓕.mono (le_of_lt (by exact_mod_cast hr)) _ (hp _)
    · simp only [hr, ofPred_false, empty_inter, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  exact hitTime_lt_iff


/-! ### Band horizons -/

/-- Some right mark is within `c` of the driver at time `s`. -/
def RightNear (c : ℝ) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ≥0) : Prop := ∃ j, vR j s - w s ≤ c

/-- Some left mark is within `c` of the driver at time `s`. -/
def LeftNear (c : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (s : ℝ≥0) : Prop := ∃ i, w s - vL i s ≤ c

/-- **The horizon of the band deleting the right group** (Aux. lemma 103: "use the left band"): the first rational
time at which a right mark comes within `2δ` of the driver, capped by `n` and the lifetime. -/
def horizonR (δ : ℝ) (n : ℕ) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  min (hitTime (RightNear (2 * δ) w vR) ζ) (min (n : ℝ≥0∞) ζ)

/-- The horizon of the band deleting the left group. -/
def horizonL (δ : ℝ) (n : ℕ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  min (hitTime (LeftNear (2 * δ) w vL) ζ) (min (n : ℝ≥0∞) ζ)

theorem horizonR_le_lifetime (δ : ℝ) (n : ℕ) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    horizonR δ n w vR ζ ≤ ζ := (min_le_right _ _).trans (min_le_right _ _)

theorem horizonR_le_n (δ : ℝ) (n : ℕ) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    horizonR δ n w vR ζ ≤ n := (min_le_right _ _).trans (min_le_left _ _)

theorem horizonL_le_lifetime (δ : ℝ) (n : ℕ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    horizonL δ n w vL ζ ≤ ζ := (min_le_right _ _).trans (min_le_right _ _)

theorem horizonL_le_n (δ : ℝ) (n : ℕ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    horizonL δ n w vL ζ ≤ n := (min_le_right _ _).trans (min_le_left _ _)

/-- Before the right-band horizon every right mark is at distance at least `2δ` from the driver. -/
theorem le_gapR_of_lt_horizonR {δ : ℝ} {n : ℕ} {w : ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hv : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < horizonR δ n w vR ζ) (j : Fin nR) : 2 * δ ≤ vR j t - w t := by
  have htζ : (t : ℝ≥0∞) < ζ := ht.trans_le (horizonR_le_lifetime δ n w vR ζ)
  have hth : (t : ℝ≥0∞) < hitTime (RightNear (2 * δ) w vR) ζ := ht.trans_le (min_le_left _ _)
  refine le_of_lt_hitTime ((hv j).sub hw) htζ (hth.trans_le (hitTime_mono fun s hs => ⟨j, hs⟩))

/-- Before the left-band horizon every left mark is at distance at least `2δ` from the driver. -/
theorem le_gapL_of_lt_horizonL {δ : ℝ} {n : ℕ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hv : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < horizonL δ n w vL ζ) (i : Fin nL) : 2 * δ ≤ w t - vL i t := by
  have htζ : (t : ℝ≥0∞) < ζ := ht.trans_le (horizonL_le_lifetime δ n w vL ζ)
  have hth : (t : ℝ≥0∞) < hitTime (LeftNear (2 * δ) w vL) ζ := ht.trans_le (min_le_left _ _)
  refine le_of_lt_hitTime (hw.sub (hv i)) htζ (hth.trans_le (hitTime_mono fun s hs => ⟨i, hs⟩))

/-! ### Band events on solution codes -/

theorem measurable_cvR (j : Fin nR) : Measurable fun x : XCode nL nR => cvR x j :=
  measurable_pi_iff.2 fun t => measurable_dec_at (measurable_code_vR j) t

theorem measurable_cvL (i : Fin nL) : Measurable fun x : XCode nL nR => cvL x i :=
  measurable_pi_iff.2 fun t => measurable_dec_at (measurable_code_vL i) t

theorem measurable_horizonR (δ : ℝ) (n : ℕ) :
    Measurable fun x : XCode nL nR => horizonR δ n (cw x) (cvR x) (cζ x) := by
  refine Measurable.min ?_ (measurable_const.min measurable_cζ)
  refine measurable_hitTime measurable_cζ fun s => ?_
  have e : {x : XCode nL nR | RightNear (2 * δ) (cw x) (cvR x) s} =
      ⋃ j, {x | cvR x j s - cw x s ≤ 2 * δ} := by
    ext x; simp only [RightNear, mem_ofPred_eq, mem_iUnion]
  rw [e]
  exact MeasurableSet.iUnion fun j => measurableSet_le
    ((measurable_dec_at (measurable_code_vR j) s).sub (measurable_dec_at measurable_code_w s)) measurable_const

theorem measurable_horizonL (δ : ℝ) (n : ℕ) :
    Measurable fun x : XCode nL nR => horizonL δ n (cw x) (cvL x) (cζ x) := by
  refine Measurable.min ?_ (measurable_const.min measurable_cζ)
  refine measurable_hitTime measurable_cζ fun s => ?_
  have e : {x : XCode nL nR | LeftNear (2 * δ) (cw x) (cvL x) s} =
      ⋃ i, {x | cw x s - cvL x i s ≤ 2 * δ} := by
    ext x; simp only [LeftNear, mem_ofPred_eq, mem_iUnion]
  rw [e]
  exact MeasurableSet.iUnion fun i => measurableSet_le
    ((measurable_dec_at measurable_code_w s).sub (measurable_dec_at (measurable_code_vL i) s)) measurable_const

/-- Codes whose driver has the trace event up to the right-band horizon. -/
def bandSetR (δ : ℝ) (n : ℕ) : Set (XCode nL nR) :=
  {x | (cw x, horizonR δ n (cw x) (cvR x) (cζ x)) ∈ traceSet}

/-- Codes whose driver has the trace event up to the left-band horizon. -/
def bandSetL (δ : ℝ) (n : ℕ) : Set (XCode nL nR) :=
  {x | (cw x, horizonL δ n (cw x) (cvL x) (cζ x)) ∈ traceSet}

theorem measurableSet_bandSetR (δ : ℝ) (n : ℕ) : MeasurableSet (bandSetR δ n : Set (XCode nL nR)) :=
  (measurable_cw.prodMk (measurable_horizonR δ n)) measurableSet_traceSet

theorem measurableSet_bandSetL (δ : ℝ) (n : ℕ) : MeasurableSet (bandSetL δ n : Set (XCode nL nR)) :=
  (measurable_cw.prodMk (measurable_horizonL δ n)) measurableSet_traceSet

/-- The trace event up to a horizon `h ≤ ζ` is coded by `traceSet` when the driver has a left limit at a finite
`h = ζ`. -/
theorem mem_traceSet_iff_of_le {w : ℝ≥0 → ℝ} {ζ h : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) (hhζ : h ≤ ζ)
    (hlim : 0 < ζ → ζ < ⊤ → ∃ w₀ : ℝ, Tendsto w (𝓝[<] ζ.toNNReal) (𝓝 w₀)) :
    (w, h) ∈ traceSet ↔ TraceEvent w h := by
  refine mem_traceSet_iff (hw.mono fun t ht => lt_of_lt_of_le ht hhζ) hw0 fun h0 hfin => ?_
  rcases hhζ.lt_or_eq with hlt | heq
  · refine ⟨w h.toNNReal, ?_⟩
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    have hh : ((h.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by rw [ENNReal.coe_toNNReal hfin.ne]; exact hlt
    exact (hw.continuousAt (hopen.mem_nhds hh)).tendsto.mono_left nhdsWithin_le_nhds
  · subst heq
    exact hlim h0 hfin

theorem mem_bandSetR_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (δ : ℝ) (n : ℕ) {x : XCode nL nR}
    (hx : x ∈ CRelF a ρL ρR) (hl : HasLimW x) :
    x ∈ bandSetR δ n ↔ TraceEvent (cw x) (horizonR δ n (cw x) (cvR x) (cζ x)) := by
  have hp : IsIntegratedSLEPath a (startOf x).1 (startOf x).2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
    hx.1.2.2
  exact mem_traceSet_iff_of_le hp.isForcePath.continuousOn_w hp.1 (horizonR_le_lifetime _ _ _ _ _) hl

theorem mem_bandSetL_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (δ : ℝ) (n : ℕ) {x : XCode nL nR}
    (hx : x ∈ CRelF a ρL ρR) (hl : HasLimW x) :
    x ∈ bandSetL δ n ↔ TraceEvent (cw x) (horizonL δ n (cw x) (cvL x) (cζ x)) := by
  have hp : IsIntegratedSLEPath a (startOf x).1 (startOf x).2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
    hx.1.2.2
  exact mem_traceSet_iff_of_le hp.isForcePath.continuousOn_w hp.1 (horizonL_le_lifetime _ _ _ _ _) hl


/-! ### Band horizons of an evolution are stopping times -/

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

theorem measurable_killed_of_adaptedBefore {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0 := by
  intro A hA
  have h1 := hX t A hA
  have h2 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    have := hX t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  by_cases h0 : (0 : ℝ) ∈ A
  · have e : (fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0) ⁻¹' A =
        {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∪ {ω | (t : ℝ≥0∞) < ζ ω}ᶜ := by
      ext ω
      by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [h, h0]
    rw [e]
    exact h1.union h2.compl
  · have e : (fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0) ⁻¹' A =
        {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := by
      ext ω
      by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [h, h0]
    rw [e]
    exact h1

theorem measurableSet_lt_and_le_of_adaptedBefore {X Y : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X)
    (hY : AdaptedBefore 𝓕 ζ Y) (t : ℝ≥0) (c : ℝ) :
    MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω - Y t ω ≤ c} := by
  have h2 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    have := hX t univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have h3 : MeasurableSet[𝓕 t] {ω | (if (t : ℝ≥0∞) < ζ ω then X t ω else 0) -
      (if (t : ℝ≥0∞) < ζ ω then Y t ω else 0) ≤ c} :=
    measurableSet_le ((measurable_killed_of_adaptedBefore hX t).sub
      (measurable_killed_of_adaptedBefore hY t)) measurable_const
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω - Y t ω ≤ c} = {ω | (t : ℝ≥0∞) < ζ ω} ∩
      {ω | (if (t : ℝ≥0∞) < ζ ω then X t ω else 0) - (if (t : ℝ≥0∞) < ζ ω then Y t ω else 0) ≤ c} := by
    ext ω
    by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [h]
  rw [e]
  exact h2.inter h3

theorem isStoppingTime_horizonR [𝓕.IsRightContinuous] {W : ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hW : AdaptedBefore 𝓕 ζ W) (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (δ : ℝ) (n : ℕ) :
    IsStoppingTime 𝓕 fun ω =>
      (horizonR δ n (fun t => W t ω) (fun j t => VR j t ω) (ζ ω) : WithTop ℝ≥0) := by
  have h1 : IsStoppingTime 𝓕 fun ω =>
      (hitTime (RightNear (2 * δ) (fun t => W t ω) (fun j t => VR j t ω)) (ζ ω) : WithTop ℝ≥0) := by
    refine isStoppingTime_hitTime fun s => ?_
    have e : {ω | (s : ℝ≥0∞) < ζ ω ∧ RightNear (2 * δ) (fun t => W t ω) (fun j t => VR j t ω) s} =
        ⋃ j, {ω | (s : ℝ≥0∞) < ζ ω ∧ VR j s ω - W s ω ≤ 2 * δ} := by
      ext ω
      simp only [RightNear, mem_ofPred_eq, mem_iUnion, exists_and_left]
    rw [e]
    exact MeasurableSet.iUnion fun j => measurableSet_lt_and_le_of_adaptedBefore (hVR j) hW s _
  exact h1.min ((isStoppingTime_const 𝓕 (n : ℝ≥0)).min (Ito.isStoppingTime_lifetime hW))

theorem isStoppingTime_horizonL [𝓕.IsRightContinuous] {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    (hW : AdaptedBefore 𝓕 ζ W) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i)) (δ : ℝ) (n : ℕ) :
    IsStoppingTime 𝓕 fun ω =>
      (horizonL δ n (fun t => W t ω) (fun i t => VL i t ω) (ζ ω) : WithTop ℝ≥0) := by
  have h1 : IsStoppingTime 𝓕 fun ω =>
      (hitTime (LeftNear (2 * δ) (fun t => W t ω) (fun i t => VL i t ω)) (ζ ω) : WithTop ℝ≥0) := by
    refine isStoppingTime_hitTime fun s => ?_
    have e : {ω | (s : ℝ≥0∞) < ζ ω ∧ LeftNear (2 * δ) (fun t => W t ω) (fun i t => VL i t ω) s} =
        ⋃ i, {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω - VL i s ω ≤ 2 * δ} := by
      ext ω
      simp only [LeftNear, mem_ofPred_eq, mem_iUnion, exists_and_left]
    rw [e]
    exact MeasurableSet.iUnion fun i => measurableSet_lt_and_le_of_adaptedBefore hW (hVL i) s _
  exact h1.min ((isStoppingTime_const 𝓕 (n : ℝ≥0)).min (Ito.isStoppingTime_lifetime hW))

end Process


/-! ### The band traces of an evolution -/

section BandTrace

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem natCast_le_coe (n : ℕ) : (n : ℝ≥0∞) = ((n : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_natCast n).symm

/-- **The trace through the band deleting the right group** (Aux. lemma 103, the left band). For an evolution of
a separated word, if Wiener-almost every path drives a solution of the word with all right weights `0` with the full
trace event (the induction hypothesis for the left group, `ae_mem_lawSetS_fullTraceSet`), then almost surely the
driver has the trace event up to the right-band horizon. -/
theorem ae_traceEvent_horizonR [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (hfull : ∀ᵐ f ∂wienerPath,
      ((xL, xR), enc f) ∈ lawSetS κ ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR))) :
    ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω)
      (horizonR δ n (fun t => W t ω) (fun j t => VR j t ω) (ζ ω)) := by
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hT := isStoppingTime_horizonR hE𝓖.2.1 hE𝓖.2.2.2.1 δ n
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < horizonR δ n (fun t => W t ω) (fun j t => VR j t ω) (ζ ω) →
      (∀ i, ρL i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧
        ∀ j, (0 : Fin nR → ℝ) j ≠ ρR j → δ ≤ |W t ω - VR j t ω| := by
    filter_upwards [hE.2.2.2.2] with ω hp t ht
    refine ⟨fun i h => absurd rfl h, fun j _ => ?_⟩
    have := le_gapR_of_lt_horizonR hp.isForcePath.continuousOn_w
      (fun j => hp.isForcePath.continuousOn_vR j) ht j
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have h := ae_isGeneratingTrace_of_changeWeights hκ hE𝓖 hsep ρL 0 (fun s => hT s)
    (fun ω => horizonR_le_lifetime _ _ _ _ _) (T := (n : ℝ≥0))
    (fun ω => (natCast_le_coe n) ▸ horizonR_le_n _ _ _ _ _) hδ hgap hfull
  filter_upwards [h] with ω ⟨η, hη⟩
  exact ⟨η, hη, fun htop => absurd htop
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (horizonR_le_n _ _ _ _ _))⟩

/-- **The trace through the band deleting the left group** (Aux. lemma 103, the right band). -/
theorem ae_traceEvent_horizonL [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (hfull : ∀ᵐ f ∂wienerPath,
      ((xL, xR), enc f) ∈ lawSetS κ (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR))) :
    ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω)
      (horizonL δ n (fun t => W t ω) (fun i t => VL i t ω) (ζ ω)) := by
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hT := isStoppingTime_horizonL hE𝓖.2.1 hE𝓖.2.2.1 δ n
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < horizonL δ n (fun t => W t ω) (fun i t => VL i t ω) (ζ ω) →
      (∀ i, (0 : Fin nL → ℝ) i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧
        ∀ j, ρR j ≠ ρR j → δ ≤ |W t ω - VR j t ω| := by
    filter_upwards [hE.2.2.2.2] with ω hp t ht
    refine ⟨fun i _ => ?_, fun j h => absurd rfl h⟩
    have := le_gapL_of_lt_horizonL hp.isForcePath.continuousOn_w
      (fun i => hp.isForcePath.continuousOn_vL i) ht i
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h := ae_isGeneratingTrace_of_changeWeights hκ hE𝓖 hsep 0 ρR (fun s => hT s)
    (fun ω => horizonL_le_lifetime _ _ _ _ _) (T := (n : ℝ≥0))
    (fun ω => (natCast_le_coe n) ▸ horizonL_le_n _ _ _ _ _) hδ hgap hfull
  filter_upwards [h] with ω ⟨η, hη⟩
  exact ⟨η, hη, fun htop => absurd htop
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (horizonL_le_n _ _ _ _ _))⟩

end BandTrace


/-! ### Canonical law of the band events at a start -/

section CodeLaw

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

theorem horizonR_congr (δ : ℝ) (n : ℕ) {w w' : ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = w' t) (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ j, vR j t = vR' j t) :
    horizonR δ n w vR ζ = horizonR δ n w' vR' ζ := by
  unfold horizonR
  rw [hitTime_congr fun s hs => ?_]
  simp only [RightNear, hw s hs, hv s hs]

theorem horizonL_congr (δ : ℝ) (n : ℕ) {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = w' t) (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL i t = vL' i t) :
    horizonL δ n w vL ζ = horizonL δ n w' vL' ζ := by
  unfold horizonL
  rw [hitTime_congr fun s hs => ?_]
  simp only [LeftNear, hw s hs, hv s hs]

/-- **A code event that holds almost surely for an evolution has canonical law one.** If `S` is a Borel set of
solution codes and, for an evolution from the separated start `(xL, xR)`, almost surely its code (with any good
version of its Brownian motion) lies in `S`, then `codeLaw Sᶜ (xL, xR) = 0`. -/
theorem codeLaw_compl_eq_zero_of_ae {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hκ : 0 < κ)
    (hsep : ∀ i j, xL i < xR j) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    (hmem : ∀ B' : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (B' · ω)) → (∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) →
      ∀ᵐ ω ∂P, codeOf xL xR B' W VL VR ζ ω ∈ S) :
    codeLaw κ ρL ρR Sᶜ (xL, xR) = 0 := by
  obtain ⟨B', hm, hc, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  have hpm : Measurable fun ω (s : ℝ≥0) => B' s ω := measurable_pi_iff.2 hm
  rw [codeLaw, ← map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm,
    Measure.map_apply hpm ((measurableSet_restartSetS hS.compl).preimage measurable_prodMk_left)]
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_codeOf_mem hκ hE hc hae, hmem B' hc hae] with ω hmemC' hS' hω
  have hmemC := hmemC'.1
  have h1 : ((xL, xR), (codeOf xL xR B' W VL VR ζ ω).1) ∈ lawSetS κ ρL ρR Sᶜ := hω
  exact ((mem_lawSetS_iff hsep hmemC).1 h1) hS'

/-- **The right-band event has canonical law one** at every separated start at which the word has an evolution
and at which the word with all right weights `0` has the full trace event Wiener-almost surely. -/
theorem codeLaw_compl_bandSetR_eq_zero (hκ : 0 < κ) {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hsep : SepStart s)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR)
    (hred : ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ ρL (0 : Fin nR → ℝ) (fullTraceSet (nL := nL) (nR := nR)))
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    codeLaw κ ρL ρR (bandSetR δ n)ᶜ s = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have hband := ae_traceEvent_horizonR hκ hE hsep hδ n hred
  refine codeLaw_compl_eq_zero_of_ae hκ hsep hE (measurableSet_bandSetR δ n) fun B' hc hae => ?_
  filter_upwards [ae_codeOf_mem hκ hE hc hae, hband, hE.ae_tendsto_threshold hκ] with ω ⟨hmemC, hdec⟩ hb hl
  set x := codeOf s.1 s.2 B' W VL VR ζ ω with hx
  have hxF : x ∈ CRelF κ ρL ρR := (mem_cRelF_iff.2 hmemC).1
  have hxl : HasLimW x := hasLimW_of_tendsto (fun t ht => (hdec t ht).1) hl
  have hxζ : cζ x = ζ ω := rfl
  rw [mem_bandSetR_iff δ n hxF hxl, hxζ,
    horizonR_congr δ n (w' := fun t => W t ω) (vR' := fun j t => VR j t ω)
      (fun t ht => (hdec t ht).1) (fun t ht => (hdec t ht).2.2.1)]
  exact hb.congr fun t ht => ((hdec t (ht.trans_le (horizonR_le_lifetime _ _ _ _ _))).1).symm

/-- **The left-band event has canonical law one** (the reflected statement). -/
theorem codeLaw_compl_bandSetL_eq_zero (hκ : 0 < κ) {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hsep : SepStart s)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR)
    (hred : ∀ᵐ f ∂wienerPath, (s, enc f) ∈ lawSetS κ (0 : Fin nL → ℝ) ρR (fullTraceSet (nL := nL) (nR := nR)))
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    codeLaw κ ρL ρR (bandSetL δ n)ᶜ s = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have hband := ae_traceEvent_horizonL hκ hE hsep hδ n hred
  refine codeLaw_compl_eq_zero_of_ae hκ hsep hE (measurableSet_bandSetL δ n) fun B' hc hae => ?_
  filter_upwards [ae_codeOf_mem hκ hE hc hae, hband, hE.ae_tendsto_threshold hκ] with ω ⟨hmemC, hdec⟩ hb hl
  set x := codeOf s.1 s.2 B' W VL VR ζ ω with hx
  have hxF : x ∈ CRelF κ ρL ρR := (mem_cRelF_iff.2 hmemC).1
  have hxl : HasLimW x := hasLimW_of_tendsto (fun t ht => (hdec t ht).1) hl
  have hxζ : cζ x = ζ ω := rfl
  rw [mem_bandSetL_iff δ n hxF hxl, hxζ,
    horizonL_congr δ n (w' := fun t => W t ω) (vL' := fun i t => VL i t ω)
      (fun t ht => (hdec t ht).1) (fun t ht => (hdec t ht).2.1)]
  exact hb.congr fun t ht => ((hdec t (ht.trans_le (horizonL_le_lifetime _ _ _ _ _))).1).symm

end CodeLaw

end Band

end Sec7

end InteractingSLE

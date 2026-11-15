/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StripRevVisitPath
import InteractingSLE.Spec.Sec5.Prop513WireRegularity
import InteractingSLE.Spec.Wire.PartAClearanceRestart

/-!
# Lemma 5.7's reverse visits: regularity of the actual curves

Packet PROVE-REVVISIT. The two continuity inputs of Lemma 5.7's proof (specification p. 138: "We first note that `η`
is almost surely continuous by Lemma 5.6"; Remark 5.8: "a continuous counterflow which reaches its designated target
without an earlier continuation threshold, continuous relevant angle-varying pieces"), for the actual objects of
`Prop513Wire.StripReverseVisitLaw`:

* **`ae_driverTree_regular`**: almost surely every actual Q prefix `driverTree E n` is continuous and injective on its
  closed horizon `[0, treeTime n]` (from the good-piece event of the restricted Section 4.2 input, as in
  `Prop513Wire.ae_driverTree_interior`; the simple continuation is `Prop513Wire.prefix_trace_of_good`'s);
* **`ae_stripTree_regular`**: hence every physical E prefix `stripTree q E n` is continuous and injective on
  `[0, treeTime n]`, starts at `0` and is in `ℍ` at positive times;
* **`ae_counterflow_regular`**: almost surely the counterflow trace `γ` starts at `0`, is in `ℍ` at positive times,
  and the completed counterflow `stripCounterflowPath q γ` is continuous on `[0, 1]` (infinite lifetime and
  interiority from Part A's barrier-seed route, transience from Aux. lemma 7 at `κ′ = 16/κ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.StripRevVisit

open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire
open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.StripWall Theorem14.StagedReg StripSideHeightProb

/-! ### The actual prefixes -/

/-- A generating trace on `[0, T]` read on real times is continuous and injective on `[0, T]` when it is injective. -/
theorem continuousOn_injOn_of_trace {w : ℝ≥0 → ℝ} {T : ℝ≥0} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w (T : ℝ≥0∞) η) (hinj : Function.Injective η) :
    ContinuousOn (fun t : ℝ => η t.toNNReal) (Icc 0 (T : ℝ)) ∧
      InjOn (fun t : ℝ => η t.toNNReal) (Icc 0 (T : ℝ)) := by
  refine ⟨hη.2.1.comp continuous_real_toNNReal.continuousOn fun t ht => ?_, fun s hs t ht he => ?_⟩
  · have : t.toNNReal ≤ T := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2
    exact ENNReal.coe_le_coe.2 this
  · exact (Real.toNNReal_eq_toNNReal_iff hs.1 ht.1).1 (hinj he)

/-- **The actual Q prefixes are continuous and injective on their closed horizons**, almost surely and simultaneously
for all `n` (Lemma 5.6 for the extreme-angle prefixes, from the restricted Section 4.2 input). -/
theorem ae_driverTree_regular (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c) (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (E s)) :
    ∀ᵐ ω ∂P, ∀ n, ContinuousOn (driverTree E n ω) (Icc 0 (treeTime n)) ∧
      InjOn (driverTree E n ω) (Icc 0 (treeTime n)) := by
  let F : Schedule → ℕ → Ω → Driver := fun s => regHist (scheduleSpec s) (E s)
  have hg := fun s => ae_schedule_goodPath h44 hκ hκ4 c hc hh s
    (isStagedHistory_regHist c.isPiecewiseConstantBoundaryData (hE s) (hR s))
    (fun _ _ => isRegularDriver_regHist _ _)
  filter_upwards [ae_all_iff.2 hg, ae_prefixDriver_regHist h44 hκ hκ4 c hc hh hE hR]
    with ω hgω he n
  obtain ⟨hw, hw0, η, hη, hinj, -⟩ := prefix_trace_of_good F (scheduleAt n) ω
    (fun _ => isRegularDriver_regHist _ _) (hgω (scheduleAt n))
  have hpt : EqOn (driverTree E n ω) (fun t : ℝ => η t.toNNReal) (Icc 0 (treeTime n)) := by
    intro t ht
    have h1 := prefixTrace_eq hw.continuousOn hw0 (D := prefixDriver F) (fun _ _ => rfl) hη ht
    have h2 : prefixTrace (prefixDriver F) (scheduleAt n) ω t =
        prefixTrace (prefixDriver E) (scheduleAt n) ω t := by
      unfold prefixTrace
      rw [show prefixDriver F (scheduleAt n) ω = prefixDriver E (scheduleAt n) ω from he _]
    show prefixTrace (prefixDriver E) (scheduleAt n) ω t = η t.toNNReal
    rw [← h2, h1]
  obtain ⟨hc', hi'⟩ := continuousOn_injOn_of_trace hη hinj
  exact ⟨hc'.congr hpt, hi'.congr hpt.symm⟩

/-- **The physical E prefixes are continuous, injective, rooted at `0` and interior**, almost surely and
simultaneously for all `n`. -/
theorem ae_stripTree_regular (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {q : ℝ} (hq : 0 < q)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c) (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (E s)) :
    ∀ᵐ ω ∂P, ∀ n, ContinuousOn (stripTree q E n ω) (Icc 0 (treeTime n)) ∧
      InjOn (stripTree q E n ω) (Icc 0 (treeTime n)) ∧ stripTree q E n ω 0 = 0 ∧
      ∀ t : ℝ, 0 < t → stripTree q E n ω t ∈ H := by
  filter_upwards [ae_driverTree_regular h44 hκ hκ4 c hc hh hE hR,
    ae_driverTree_interior h44 hκ hκ4 c hc hh hE hR] with ω hreg hint n
  obtain ⟨hcont, hinj⟩ := hreg n
  obtain ⟨h0, hH⟩ := hint n
  have h1 := ne_one_of_prefix h0 hH
  exact ⟨continuousOn_pullPrefix q hcont h1, injOn_pullPrefix hq subset_rfl hinj h1,
    pullPrefix_zero q (treeTime_pos n).le h0, pullPrefix_mem_H hq (treeTime_pos n) hH⟩

/-! ### The counterflow -/

/-- **The completed counterflow is continuous, starts at `0` and is interior** (Remark 5.8's "continuous counterflow
which reaches its designated target"): almost surely `γ(0) = 0`, `γ` is in `ℍ` at positive times, and
`stripCounterflowPath q γ` (`q = e^{πx₀}`) is continuous on `[0, 1]`. Only Aux. lemma 7 at `16/κ` is used from the
clearance form of Part A. -/
theorem ae_counterflow_regular (hA : PartAInputsSixteenDivOfClearance)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) :
    ∀ᵐ ω ∂P, γ ω 0 = 0 ∧ (∀ t : ℝ≥0, 0 < t → γ ω t ∈ H) ∧
      ContinuousOn (stripCounterflowPath (Real.exp (π * x₀)) (γ ω)) (Icc 0 1) := by
  have hreg := fig51_trace_mem_H_of_partA_of_clearance hA hκ hκ4 hb hG hcf
  obtain ⟨b₀, J₀, _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hinf := aux7Statement_sixteen_div_of_partA_of_clearance.{u} hA hκ hκ4 _ _ _ _ P 𝓕 W VL VR B ζ
    (Theorem15.isOrderedForceWord_flowLine b₀ J₀ 0) hadm hC.1
  filter_upwards [hreg, hinf, htr] with ω ⟨hζ, hH⟩ ⟨_, _, hT⟩ hγ
  rw [hζ] at hγ
  have hHω := hH _ hγ
  have hne : ∀ t, γ ω t ≠ -1 := by
    intro t ht
    rcases eq_zero_or_pos t with h0 | hpos
    · rw [h0, hγ.1] at ht
      norm_num at ht
    · have := hHω t hpos
      rw [ht] at this
      exact absurd this (by simp [H])
  exact ⟨hγ.1, hHω, continuousOn_stripCounterflowPath (Sec5.continuous_of_isGeneratingTrace_top hγ) hne (hT _ hγ)⟩

end InteractingSLE.Sec5.StripRevVisit

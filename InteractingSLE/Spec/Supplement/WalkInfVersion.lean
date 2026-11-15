/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfMeas

/-!
# The chart of a staged run, read from its retained past

Packet PROVE-T14-WALKINF, for input (B) of `WalkSide.walkPrefixSideStatement_of_prefix`. For any program `spec` and
driver family `E`, the **version chart** `verChart … n` is built from the retained records and the recentring amounts
of the run, one instruction at a time: unchanged after a launch with infinite stop, composed with the record chart of
the new record after a launch with finite stop, recentred otherwise. It is

* a measurable random chart for the retained past before `n` (`isMeasChart_verChart`): conformal with a continuous
  harmonic lift at every sample, domain events, masked forward maps and lifts and closed-disc events measurable;
* the chart of the run after `n` instructions whenever the drivers are regular and the records of the launched pieces
  with finite stop are good (`verChart_eq_run`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.WalkInf

open Exist.Staged Exist.StagedLaw

/-! ### Constant, monotone and piecewise random charts -/

section Basic

variable {Ω : Type*}

theorem isConformal_id_chart : (Chart.id : Chart).IsConformal := Chart.isConformal_id

/-- The identity chart is a measurable random chart. -/
theorem isMeasChart_id (m : MeasurableSpace Ω) : IsMeasChart m fun _ : Ω => Chart.id := by
  refine ⟨fun _ => Chart.isConformal_id, fun _ => continuousOn_const, fun _ => ?_, fun z => MeasurableSet.const _,
    fun z => measurable_const.indicator (MeasurableSet.const _), fun z ε => MeasurableSet.const _,
    fun z => measurable_const.indicator (MeasurableSet.const _)⟩
  intro x _
  exact InnerProductSpace.harmonicAt_const _

/-- A measurable random chart stays measurable for a larger σ-algebra. -/
theorem IsMeasChart.mono {m m' : MeasurableSpace Ω} (hmm' : m ≤ m') {c : Ω → Chart} (hc : IsMeasChart m c) :
    IsMeasChart m' c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  exact ⟨h1, h2, h3, fun z => hmm' _ (h4 z), fun z => (h5 z).mono hmm' le_rfl, fun z ε => hmm' _ (h6 z ε),
    fun z => (h7 z).mono hmm' le_rfl⟩

/-- Masked values of two random charts agree at a sample where the charts agree. -/
theorem indicator_dom_apply_congr {α : Type*} [Zero α] {c c' : Ω → Chart} {F : Chart → ℂ → α} {z : ℂ} {ω : Ω}
    (h : c ω = c' ω) :
    ({ω | z ∈ (c ω).dom}.indicator fun ω => F (c ω) z) ω = ({ω | z ∈ (c' ω).dom}.indicator fun ω => F (c' ω) z) ω := by
  by_cases hz : z ∈ (c' ω).dom
  · rw [indicator_of_mem (show ω ∈ {ω | z ∈ (c ω).dom} by show z ∈ (c ω).dom; rw [h]; exact hz),
      indicator_of_mem (show ω ∈ {ω | z ∈ (c' ω).dom} from hz), h]
  · rw [indicator_of_notMem (show ω ∉ {ω | z ∈ (c ω).dom} by show z ∉ (c ω).dom; rw [h]; exact hz),
      indicator_of_notMem (show ω ∉ {ω | z ∈ (c' ω).dom} from hz)]

/-- **Random charts chosen along a measurable event.** -/
theorem IsMeasChart.ite {m : MeasurableSpace Ω} {S : Set Ω} [DecidablePred (· ∈ S)] (hS : MeasurableSet[m] S)
    {c₁ c₂ : Ω → Chart}
    (h₁ : IsMeasChart m c₁) (h₂ : IsMeasChart m c₂) : IsMeasChart m fun ω => if ω ∈ S then c₁ ω else c₂ ω := by
  let _ : MeasurableSpace Ω := m
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h₂
  have hset : ∀ (P : Chart → Prop), MeasurableSet {ω | P (c₁ ω)} → MeasurableSet {ω | P (c₂ ω)} →
      MeasurableSet {ω | P (if ω ∈ S then c₁ ω else c₂ ω)} := by
    intro P hP1 hP2
    have e : {ω | P (if ω ∈ S then c₁ ω else c₂ ω)} = S.ite {ω | P (c₁ ω)} {ω | P (c₂ ω)} := by
      ext ω
      by_cases hω : ω ∈ S <;> simp [Set.ite, hω]
    rw [e]
    exact hS.ite hP1 hP2
  have hfunG : ∀ {α : Type} [Zero α] [MeasurableSpace α] (F : Chart → ℂ → α) (z : ℂ),
      Measurable ({ω | z ∈ (c₁ ω).dom}.indicator fun ω => F (c₁ ω) z) →
      Measurable ({ω | z ∈ (c₂ ω).dom}.indicator fun ω => F (c₂ ω) z) →
      Measurable ({ω | z ∈ (if ω ∈ S then c₁ ω else c₂ ω).dom}.indicator
        fun ω => F (if ω ∈ S then c₁ ω else c₂ ω) z) := by
    intro α _ _ F z h1 h2
    have e : ({ω | z ∈ (if ω ∈ S then c₁ ω else c₂ ω).dom}.indicator
        fun ω => F (if ω ∈ S then c₁ ω else c₂ ω) z) =
        S.piecewise ({ω | z ∈ (c₁ ω).dom}.indicator fun ω => F (c₁ ω) z)
          ({ω | z ∈ (c₂ ω).dom}.indicator fun ω => F (c₂ ω) z) := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [Set.piecewise_eq_of_mem _ _ _ hω]
        exact indicator_dom_apply_congr (ite_eq_left hω)
      · rw [Set.piecewise_eq_of_notMem _ _ _ hω]
        exact indicator_dom_apply_congr (ite_eq_right hω)
    rw [e]
    exact Measurable.piecewise hS h1 h2
  have hfun : ∀ (F : Chart → ℂ → ℝ) (z : ℂ),
      Measurable ({ω | z ∈ (c₁ ω).dom}.indicator fun ω => F (c₁ ω) z) →
      Measurable ({ω | z ∈ (c₂ ω).dom}.indicator fun ω => F (c₂ ω) z) →
      Measurable ({ω | z ∈ (if ω ∈ S then c₁ ω else c₂ ω).dom}.indicator
        fun ω => F (if ω ∈ S then c₁ ω else c₂ ω) z) := fun F z => hfunG F z
  have hfunC : ∀ (F : Chart → ℂ → ℂ) (z : ℂ),
      Measurable ({ω | z ∈ (c₁ ω).dom}.indicator fun ω => F (c₁ ω) z) →
      Measurable ({ω | z ∈ (c₂ ω).dom}.indicator fun ω => F (c₂ ω) z) →
      Measurable ({ω | z ∈ (if ω ∈ S then c₁ ω else c₂ ω).dom}.indicator
        fun ω => F (if ω ∈ S then c₁ ω else c₂ ω) z) := fun F z => hfunG F z
  refine ⟨fun ω => ?_, fun ω => ?_, fun ω => ?_, fun z => hset (fun c => z ∈ c.dom) (a4 z) (b4 z),
    fun z => hfunC (fun c => c.1) z (a5 z) (b5 z), fun z ε => hset (fun c => closedBall z ε ⊆ c.dom) (a6 z ε)
      (b6 z ε), fun z => hfun (fun c => c.2.2) z (a7 z) (b7 z)⟩
  · by_cases hω : ω ∈ S
    · simp only [hω, ↓reduceIte]; exact a1 ω
    · simp only [hω, ↓reduceIte]; exact b1 ω
  · by_cases hω : ω ∈ S
    · simp only [hω, ↓reduceIte]; exact a2 ω
    · simp only [hω, ↓reduceIte]; exact b2 ω
  · by_cases hω : ω ∈ S
    · simp only [hω, ↓reduceIte]; exact a3 ω
    · simp only [hω, ↓reduceIte]; exact b3 ω

end Basic

/-! ### The version chart of a run -/

section Version

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) {Ω : Type*}
  (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)

/-- The event that instruction `n` launches a piece. -/
def launchedEv (n : ℕ) : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n ≠ none}

/-- The record of instruction `n`, read from the retained past after it. -/
def recAt (n : ℕ) (ω : Ω) : RecData := pastMap κ b jumps spec E (n + 1) ω (Fin.last n)

/-- The recentring amount of instruction `n` (the change of the forward chart map at `0`). -/
def recAmt (n : ℕ) (ω : Ω) : ℝ :=
  ((ExplState.run κ b jumps spec (fun j => E j ω) n).2.2.2.2.1.1 0 -
    (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.2.1.1 0).re

open Classical in
/-- **The version chart of the run after `n` instructions**, read from the records and the recentring amounts. -/
def verChart : ℕ → Ω → Chart
  | 0 => fun _ => Chart.id.recenter spec.1
  | n + 1 => fun ω => if ω ∈ launchedEv κ b jumps spec E n then
      (if (recAt κ b jumps spec E n ω).2.1 = ⊤ then verChart n ω
        else (verChart n ω).trans (recChart (recAt κ b jumps spec E n ω)))
      else (verChart n ω).recenter (recAmt κ b jumps spec E n ω)

variable {κ b jumps spec E}

/-- **The version chart is a measurable random chart for the retained past.** -/
theorem isMeasChart_verChart [MeasurableSpace Ω] [StandardBorelSpace Ω] (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ n, IsMeasChart (pastSigma κ b jumps spec E n) (verChart κ b jumps spec E n) := by
  classical
  have hB := runMeasStatement.{u_1}
  intro n
  induction n with
  | zero => exact (isMeasChart_id _).recenter measurable_const
  | succ n ih =>
    have hEm' : ∀ j < n + 1, Measurable (E j) := fun j _ => hEm j
    have hreg' : ∀ j < n + 1, ∀ ω, IsRegularDriver (E j ω) := fun j _ => hreg j
    have ih' := ih.mono (pastSigma_mono (κ := κ) (b := b) (jumps := jumps) spec E (Nat.le_succ n))
    -- the launch event
    have hL : MeasurableSet[pastSigma κ b jumps spec E (n + 1)] (launchedEv κ b jumps spec E n) := by
      refine measurableSet_pastSigma_of_runs hB hb hEm' hreg'
        (measurableSet_launch_self hB hb (fun j _ => hEm j) (fun j _ => hreg j)) fun ω ω' h hω => ?_
      show _ ≠ none
      rw [← h (n + 1) le_rfl]
      exact hω
    -- the record
    have hr : Measurable[pastSigma κ b jumps spec E (n + 1)] (recAt κ b jumps spec E n) := by
      rw [pastSigma_eq_comap]
      exact (measurable_pi_apply _).comp (comap_measurable _)
    have hT : MeasurableSet[pastSigma κ b jumps spec E (n + 1)]
        {ω | (recAt κ b jumps spec E n ω).2.1 = ⊤} :=
      (measurable_fst.comp (measurable_snd.comp hr)) (measurableSet_singleton ⊤)
    -- the recentring amount
    have ha : Measurable[pastSigma κ b jumps spec E (n + 1)] (recAmt κ b jumps spec E n) := by
      refine measurable_pastSigma_of_runs hB hb hEm' hreg' ?_ fun ω ω' h => ?_
      · exact Complex.measurable_re.comp
          ((measurable_chart_apply hB hb spec hEm' hreg' (Nat.le_succ n) 0).sub
            (measurable_chart_apply hB hb spec hEm' hreg' le_rfl 0))
      · simp only [recAmt, h n (Nat.le_succ n), h (n + 1) le_rfl]
    have key := IsMeasChart.ite hL (IsMeasChart.ite hT ih' (ih'.trans_recChart hr)) (ih'.recenter ha)
    convert key using 2 with ω
    by_cases h1 : ω ∈ launchedEv κ b jumps spec E n
    · by_cases h2 : (recAt κ b jumps spec E n ω).2.1 = ⊤
      · simp [verChart, h1, h2]
      · simp [verChart, h1, h2]
    · simp [verChart, h1]

/-- **The version chart is the run's chart** when the drivers are regular and the records of the launched pieces with
a finite stop are good. -/
theorem verChart_eq_run {ω : Ω} (hreg : ∀ j, IsRegularDriver (E j ω)) {N : ℕ}
    (hgood : ∀ j < N, (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none →
      min (instrTime spec j) (E j ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf (instrTime spec j) (E j ω)))) :
    ∀ n ≤ N, verChart κ b jumps spec E n ω = (ExplState.run κ b jumps spec (fun j => E j ω) n).2.2.2.2.1 := by
  classical
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have ihn := ih (Nat.le_of_succ_le hn)
    by_cases hl : ω ∈ launchedEv κ b jumps spec E n
    · obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hcθ
      have hrec : recAt κ b jumps spec E n ω = recOf (instrTime spec n) (E n ω) :=
        pastMap_last_of_launch hl
      have h2 : (recAt κ b jumps spec E n ω).2.1 = min (instrTime spec n) (E n ω).2 := by rw [hrec]; rfl
      by_cases htop : min (instrTime spec n) (E n ω).2 = ⊤
      · have hv : verChart κ b jumps spec E (n + 1) ω = verChart κ b jumps spec E n ω := by
          simp only [verChart, hl, ↓reduceIte, h2, htop]
        rw [hv, ihn, he]
        exact (GW1P.chart_launch_of_top _ _ _ _ _ htop).symm
      · have htop' : ¬ (recOf (instrTime spec n) (E n ω)).2.1 = ⊤ := htop
        have hv : verChart κ b jumps spec E (n + 1) ω =
            (verChart κ b jumps spec E n ω).trans (recChart (recOf (instrTime spec n) (E n ω))) := by
          simp only [verChart, hl, ↓reduceIte, hrec, htop']
        rw [hv, ihn, recChart_eq_loewner (hreg n) (hgood n (Nat.lt_of_succ_le hn) hl htop),
          Sec5.CrossCond.Staged.trans_id_loewner, he, chart_launch _ _ _ _ _ htop]
        rfl
    · have hl' : (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n = none := by
        by_contra h
        exact hl h
      obtain ⟨a', ha'⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hl'
      have haa : recAmt κ b jumps spec E n ω = a' := by
        simp only [recAmt, ha', Chart.recenter]
        simp
      have hv : verChart κ b jumps spec E (n + 1) ω =
          (verChart κ b jumps spec E n ω).recenter (recAmt κ b jumps spec E n ω) := by
        simp only [verChart, hl, ↓reduceIte]
      rw [hv, ihn, haa, ha']

end Version

end InteractingSLE.Theorem14.WalkInf

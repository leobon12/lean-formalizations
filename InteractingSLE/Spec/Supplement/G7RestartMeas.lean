/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7RestartPath

/-!
# Measurable events and the chart path data of retained continuations

Packet PROVE-G7B. Measurability helpers for the canonical retained clocks:

* `measurableSet_mem_closure`: adherence of a measurable point to a random open set (with measurable membership) is
  a measurable event (dense sequence);
* `RetData.IsMeasGood.measurableSet_tipEvent`: the event that the first tip `η₁(u)` is interior, off the second
  prefix and adherent to the retained domain;
* `RetData.IsMeasGood.measurable_indicator_fwd`, `measurable_indicator_fwd_sub`: the forward chart (translated by a
  measurable real) is measurable on the domain;
* `RetData.IsMeasGood.measurable_tipLim`: the forward chart limit at the first tip is measurable.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

open Restart

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Adherence of a measurable point to a random open set is measurable.** -/
theorem measurableSet_mem_closure {D : Ω → Set ℂ} (hDo : ∀ ω, IsOpen (D ω))
    (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω}) {q : Ω → ℂ} (hq : Measurable q) :
    MeasurableSet {ω | q ω ∈ closure (D ω)} := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have heq : {ω | q ω ∈ closure (D ω)} =
      ⋂ m : ℕ, ⋃ j : ℕ, ({ω | e j ∈ D ω} ∩ {ω | dist (e j) (q ω) < 1 / ((m : ℝ) + 1)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    constructor
    · intro hc m
      have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      obtain ⟨y, hyD, hyq⟩ := Metric.mem_closure_iff.1 hc _ hr
      obtain ⟨j, hj⟩ := he.exists_mem_open ((hDo ω).inter isOpen_ball)
        ⟨y, hyD, mem_ball.2 (by rw [dist_comm]; exact hyq)⟩
      exact ⟨j, hj.1, mem_ball.1 hj.2⟩
    · intro h
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨j, hjD, hjd⟩ := h m
      exact ⟨e j, hjD, by rw [dist_comm]; exact hjd.trans hm⟩
  rw [heq]
  exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun j =>
    (hDm (e j)).inter (measurableSet_lt (measurable_const.dist hq) measurable_const)

namespace RetData

variable {d : RetData Ω}

/-- **The first-tip event** is measurable: `η₁(u)` interior, off the second prefix, adherent to the domain. -/
theorem IsMeasGood.measurableSet_tipEvent (hd : d.IsMeasGood) :
    MeasurableSet (d.E ∩ {ω | d.η₁ ω d.u ∈ H} ∩ {ω | d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r} ∩
      {ω | d.η₁ ω d.u ∈ closure (d.D ω)}) := by
  have h1 : MeasurableSet (d.E ∩ {ω | d.η₁ ω d.u ∈ H}) :=
    hd.measurableSet_E.inter (measurableSet_lt measurable_const (Complex.measurable_im.comp (hd.meas₁ d.u)))
  have h2 := measurableSet_inter_exists_eq h1 hd.meas₂ (f₂ := fun ω (_ : ℝ≥0) => d.η₁ ω d.u)
    (fun _ => hd.meas₁ d.u) (c₁ := fun _ => d.r) (c₂ := fun _ => 0) measurable_const measurable_const
    (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hd.good ω (E_subset_G hω.1)).2.1)
    (fun _ _ => continuousOn_const)
  have heq : d.E ∩ {ω | d.η₁ ω d.u ∈ H} ∩ {ω | d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r} =
      (d.E ∩ {ω | d.η₁ ω d.u ∈ H}) \
        ((d.E ∩ {ω | d.η₁ ω d.u ∈ H}) ∩ {ω | ∃ t ≤ d.r, ∃ s ≤ (0 : ℝ≥0), d.η₂ ω t = d.η₁ ω d.u}) := by
    ext ω
    constructor
    · rintro ⟨hE, hn⟩
      refine ⟨hE, fun hc => ?_⟩
      obtain ⟨t, ht, s, -, he⟩ := hc.2
      exact hn ⟨t, ⟨zero_le, ht⟩, he⟩
    · rintro ⟨hE, hn⟩
      exact ⟨hE, fun ⟨t, ht, he⟩ => hn ⟨hE, t, ht.2, 0, le_rfl, he⟩⟩
  rw [heq]
  exact (h1.diff h2).inter (measurableSet_mem_closure hd.isOpen_D hd.measurableSet_mem_D (hd.meas₁ d.u))

/-- The forward chart is measurable on the domain. -/
theorem IsMeasGood.measurable_indicator_fwd (hd : d.IsMeasGood) (z : ℂ) :
    Measurable ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z) := by
  have : ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z) =
      ({ω | z ∈ d.D ω}.indicator fun ω => d.g ω z) - {ω | z ∈ d.D ω}.indicator d.shift := by
    funext ω; by_cases hω : z ∈ d.D ω <;> simp [Set.indicator, hω, RetData.fwd]
  rw [this]
  exact (hd.measurable_indicator_g z).sub (hd.measurable_shift.indicator (hd.measurableSet_mem_D z))

/-- The forward chart translated by a measurable real is measurable on the domain. -/
theorem IsMeasGood.measurable_indicator_fwd_sub (hd : d.IsMeasGood) {c : Ω → ℝ} (hc : Measurable c) (z : ℂ) :
    Measurable ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z - c ω) := by
  have : ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z - c ω) =
      ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z) - {ω | z ∈ d.D ω}.indicator fun ω => (c ω : ℂ) := by
    funext ω; by_cases hω : z ∈ d.D ω <;> simp [Set.indicator, hω]
  rw [this]
  exact (hd.measurable_indicator_fwd z).sub
    ((Complex.measurable_ofReal.comp hc).indicator (hd.measurableSet_mem_D z))

open scoped Classical in
/-- **The forward chart limit at the first tip is measurable** (on a measurable event where it exists). -/
theorem IsMeasGood.measurable_tipLim (hd : d.IsMeasGood) {E : Set Ω} (hE : MeasurableSet E)
    (hcl : ∀ ω ∈ E, d.η₁ ω d.u ∈ closure (d.D ω))
    (hlim : ∀ ω ∈ E, ∃ w, Tendsto (d.fwd ω) (𝓝[d.D ω] (d.η₁ ω d.u)) (𝓝 w)) :
    Measurable fun ω => if ω ∈ E then limUnder (𝓝[d.D ω] (d.η₁ ω d.u)) (d.fwd ω) else 0 := by
  set D' : Ω → Set ℂ := fun ω => if ω ∈ E then d.D ω else H with hD'
  set f' : Ω → ℂ → ℂ := fun ω => if ω ∈ E then d.fwd ω else id with hf'
  set q' : Ω → ℂ := fun ω => if ω ∈ E then d.η₁ ω d.u else 0 with hq'
  have hDo' : ∀ ω, IsOpen (D' ω) := fun ω => by
    simp only [hD']; split_ifs
    · exact hd.isOpen_D ω
    · exact QuantumZipper.isOpen_H
  have hDm' : ∀ z, MeasurableSet {ω | z ∈ D' ω} := fun z => by
    have : {ω | z ∈ D' ω} = (E ∩ {ω | z ∈ d.D ω}) ∪ (Eᶜ ∩ {_ω | z ∈ H}) := by
      ext ω; by_cases hω : ω ∈ E <;> simp [hD', hω]
    rw [this]
    exact (hE.inter (hd.measurableSet_mem_D z)).union (hE.compl.inter (MeasurableSet.const _))
  have hfm' : ∀ z, Measurable ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) := fun z => by
    have : ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) =
        E.piecewise ({ω | z ∈ d.D ω}.indicator fun ω => d.fwd ω z) (fun _ => if z ∈ H then z else 0) := by
      funext ω
      by_cases hω : ω ∈ E <;> by_cases hz : z ∈ H <;> simp [Set.indicator, Set.piecewise, hD', hf', hω, hz]
    rw [this]
    exact (hd.measurable_indicator_fwd z).piecewise hE measurable_const
  have hqm : Measurable q' := Measurable.ite hE (hd.meas₁ d.u) measurable_const
  have hqD : ∀ ω, q' ω ∈ closure (D' ω) := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [hq', hD', hω, ↓reduceIte]; exact hcl ω hω
    · simp only [hq', hD', hω, ↓reduceIte]
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      show (0 : ℝ) ≤ (0 : ℂ).im
      simp
  refine measurable_of_tendsto_nhdsWithin hDo' hDm' hfm' hqm hqD fun ω => ?_
  by_cases hω : ω ∈ E
  · simp only [hf', hD', hq', hω, ↓reduceIte]
    exact tendsto_nhds_limUnder (hlim ω hω)
  · simp only [hf', hD', hq', hω, ↓reduceIte]
    exact tendsto_id.mono_left nhdsWithin_le_nhds

end RetData

end Supp7

end InteractingSLE

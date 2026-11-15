/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleL25
import Mathlib.Probability.Kernel.Basic

/-!
# The finite-candidate stopping lemma: its pathwise and selection steps

Packet PROVE-T14-TIP3, following ruling R52: Lemma 1.2 of the shortcut note (`source/external/AstraIG1/
ig1_shortcuts_audited.txt` §1.1), which replaces GB9a's special choice of `Q` and GB9's upward grid rounding
(pp. 525–527) in the tip exhaustion:

> Suppose `S < F` are finite stopping times, after the stage starts, such that `X_S = 2e`, `X_F = (17/8) e`, […] Assume
> `X` and `γ` are continuous there. For every `ε > 0`, there is a stopping rule which, with conditional probability at
> least `1 − ε`, stops at a time `q ∈ Q` satisfying `S < q < F`, `γ(q) ∈ ℍ`, `X_q ∈ I_e` […]. Its only selection before
> exploring the stage is an integer.

Its proof has a pathwise step and a selection step, proved here for any deterministic countable dense `Q`:

* **pathwise** ("Continuity at `S` gives a nonempty open time interval after `S`, before `F`, on which `X ∈ I_e`.
  Lemma 2.5 […] says that its real-boundary times have Lebesgue measure zero. Its interior times are therefore dense;
  they are open by continuity. Hence some nonempty open subinterval satisfies all the required tests. It contains an
  element of `Q`"): `exists_mem_band_interior` (and `exists_mem_inter_of_null` in general); its null-time hypothesis is
  Lemma 2.5 (`IsGeneratingTrace.volume_setOf_notMem_H`, `GW2ScheduleL25`);
* **selection** ("`K_z(E_m)` is measurable in `z`, and increases to one […]. Set `m(z) = min{m : K_z(E_m) ≥ 1 − ε}` with
  an arbitrary default on the exceptional states"): `measurable_selIndex`, `selIndex_spec`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Supp8

namespace GB9Stop

/-! ### The pathwise step -/

/-- **A nonempty open set of times contains a time of any dense set at which a continuous curve is in `ℍ`**, if the
curve spends zero Lebesgue time off `ℍ` there. -/
theorem exists_mem_inter_of_null {γ : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hγ : ContinuousOn γ U) (hnull : volume {t | t ∈ U ∧ γ t ∉ H} = 0) {Q : Set ℝ} (hQ : Dense Q) :
    ∃ q ∈ Q, q ∈ U ∧ γ q ∈ H := by
  have hV : IsOpen (U ∩ γ ⁻¹' H) := hγ.isOpen_inter_preimage hU QuantumZipper.isOpen_H
  have hVne : (U ∩ γ ⁻¹' H).Nonempty := by
    by_contra hV0
    rw [not_nonempty_iff_eq_empty] at hV0
    have hsub : U ⊆ {t | t ∈ U ∧ γ t ∉ H} := fun t ht => ⟨ht, fun hH => hV0.subset ⟨ht, hH⟩⟩
    have hpos : 0 < volume U := hU.measure_pos volume hne
    exact absurd (measure_mono_null hsub hnull) hpos.ne'
  obtain ⟨q, hqQ, hqV⟩ := hQ.exists_mem_open hV hVne
  exact ⟨q, hqQ, hqV.1, hqV.2⟩

/-- **The band of Lemma 1.2**: for a function continuous at `S < F` with `X_S` in an open set `I`, there is a nonempty
open set of times in `(S, F)` at which `X ∈ I`. -/
theorem exists_open_band {X : ℝ → ℝ} {S F : ℝ} (hSF : S < F) (hX : ContinuousAt X S) {I : Set ℝ} (hI : IsOpen I)
    (hXS : X S ∈ I) : ∃ U : Set ℝ, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ioo S F ∧ ∀ t ∈ U, X t ∈ I := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hX.eventually (hI.mem_nhds hXS))
  set c := min δ (F - S) with hc
  have hc0 : 0 < c := lt_min hδ (sub_pos.2 hSF)
  have hcδ : c ≤ δ := min_le_left δ (F - S)
  have hcF : c ≤ F - S := min_le_right δ (F - S)
  have hsub : Ioo S (S + c) ⊆ Ioo S F := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  have hX' : ∀ t ∈ Ioo S (S + c), X t ∈ I := by
    intro t ht
    refine hball ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  exact ⟨Ioo S (S + c), isOpen_Ioo, nonempty_Ioo.2 (by linarith), hsub, hX'⟩

/-- **The pathwise step of Lemma 1.2**: if `X` is continuous at `S < F` with `X_S ∈ I` (an open band), `γ` is continuous
on `(S, F)` and spends zero Lebesgue time off `ℍ` there, then every dense set `Q` contains a time `q` with `S < q < F`,
`γ(q) ∈ ℍ` and `X_q ∈ I`. -/
theorem exists_mem_band_interior {X : ℝ → ℝ} {γ : ℝ → ℂ} {S F : ℝ} (hSF : S < F) (hX : ContinuousAt X S)
    {I : Set ℝ} (hI : IsOpen I) (hXS : X S ∈ I) (hγ : ContinuousOn γ (Ioo S F))
    (hnull : volume {t | t ∈ Ioo S F ∧ γ t ∉ H} = 0) {Q : Set ℝ} (hQ : Dense Q) :
    ∃ q ∈ Q, S < q ∧ q < F ∧ γ q ∈ H ∧ X q ∈ I := by
  obtain ⟨U, hU, hUne, hUSF, hUX⟩ := exists_open_band hSF hX hI hXS
  have hsub : {t | t ∈ U ∧ γ t ∉ H} ⊆ {t | t ∈ Ioo S F ∧ γ t ∉ H} := fun t ht => ⟨hUSF ht.1, ht.2⟩
  obtain ⟨q, hqQ, hqU, hqH⟩ := exists_mem_inter_of_null hU hUne (hγ.mono hUSF) (measure_mono_null hsub hnull) hQ
  exact ⟨q, hqQ, (hUSF hqU).1, (hUSF hqU).2, hqH, hUX q hqU⟩

/-! ### The selection step -/

section Select

variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]

/-- The qualifying predicate of the selection: the index reaches the level `1 − ε`, or no index does. -/
def SelOK (K : Kernel Z Ω) (E : ℕ → Set Ω) (ε : ℝ≥0∞) (z : Z) (m : ℕ) : Prop :=
  1 - ε ≤ K z (E m) ∨ ∀ m', K z (E m') < 1 - ε

theorem exists_selOK (K : Kernel Z Ω) (E : ℕ → Set Ω) (ε : ℝ≥0∞) (z : Z) : ∃ m, SelOK K E ε z m := by
  by_cases h : ∃ m, 1 - ε ≤ K z (E m)
  · obtain ⟨m, hm⟩ := h; exact ⟨m, Or.inl hm⟩
  · push Not at h; exact ⟨0, Or.inr h⟩

/-- **The selected integer** of Lemma 1.2: the least index whose event has conditional probability at least `1 − ε`
(the default `0` on the exceptional states, where no index qualifies). -/
def selIndex (K : Kernel Z Ω) (E : ℕ → Set Ω) (ε : ℝ≥0∞) (z : Z) : ℕ :=
  open Classical in Nat.find (exists_selOK K E ε z)

/-- **The selected integer is measurable in the stage-start state.** -/
theorem measurable_selIndex (K : Kernel Z Ω) {E : ℕ → Set Ω} (hE : ∀ m, MeasurableSet (E m)) (ε : ℝ≥0∞) :
    Measurable (selIndex K E ε) := by
  classical
  have hA : ∀ m, MeasurableSet {z | 1 - ε ≤ K z (E m)} := fun m =>
    measurableSet_le measurable_const (K.measurable_coe (hE m))
  have hB : MeasurableSet {z | ∀ m', K z (E m') < 1 - ε} := by
    have e : {z | ∀ m', K z (E m') < 1 - ε} = ⋂ m', {z | 1 - ε ≤ K z (E m')}ᶜ := by
      ext z; simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, not_le]
    rw [e]; exact MeasurableSet.iInter fun m' => (hA m').compl
  exact measurable_find (exists_selOK K E ε) fun m => (hA m).union hB

/-- **The selected integer achieves the bound** at every state where some index does. -/
theorem selIndex_spec (K : Kernel Z Ω) (E : ℕ → Set Ω) (ε : ℝ≥0∞) {z : Z} (h : ∃ m, 1 - ε ≤ K z (E m)) :
    1 - ε ≤ K z (E (selIndex K E ε z)) := by
  classical
  rcases Nat.find_spec (exists_selOK K E ε z) with h1 | h2
  · exact h1
  · obtain ⟨m, hm⟩ := h
    exact absurd hm (not_le.2 (h2 m))

/-- Increasing events whose union has conditional probability one reach any level `1 − ε`, `ε > 0`. -/
theorem exists_index_of_tendsto (K : Kernel Z Ω) {E : ℕ → Set Ω} (hmono : Monotone E) {z : Z}
    (hone : K z (⋃ m, E m) = 1) {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ m, 1 - ε ≤ K z (E m) := by
  by_contra hno
  push Not at hno
  have hlim := tendsto_measure_iUnion_atTop (μ := K z) hmono
  rw [hone] at hlim
  have hle : ∀ m, K z (E m) ≤ 1 - ε := fun m => (hno m).le
  have : (1 : ℝ≥0∞) ≤ 1 - ε := le_of_tendsto' hlim hle
  have h1 : (1 : ℝ≥0∞) - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
  exact absurd this (not_le.2 h1)

end Select

end GB9Stop

end Supp8

end InteractingSLE

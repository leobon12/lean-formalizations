/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcClock

/-!
# A-stopped processes of an abstract chart path: observations, time change and adapted driver

Packet PROVE-T15-ASTOP-PROC. For a physical filtration `𝓖`, an event `M` and a chart path `Γ` with physical lifetime
`L` that are good on `M` (`IsAGood`) and observed in `𝓖` (`AObs`: `M` initial, the chart coordinates through `t`
and the survival `{t < L}` on `M` are `𝓖 t`-events):

* `AObs.measurable_clock`: the supported clock `M.indicator (aClock Γ t)` is `𝓖 t`-measurable; `aFilt` is the
  time change of `𝓖` along it (RETPLUMB's `timeChange`);
* `aCapPrefix` (the chart path in capacity time read from the observations through `t`), its measurability and its
  identification on the reached live event;
* **`AObs.adaptedBefore_aDriver`**: the driver is adapted before the supported capacity lifetime in `aFilt`;
* `aTrace` (the supported chart path in capacity time) and its measurability, continuity and value at `0`;
* **`AObs.exists_driver`**: a globally continuous adapted driver from `0`, equal to `aDriver` before the supported
  lifetime, which is an `aFilt`-stopping time, generating `aTrace` on `M`.

The proofs repeat RETPLUMB's (`RetPrefixObservations.*`, `retCapacityPrefix*`, `retKilledDriverObservable`) for the
abstract path.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Restart.RetAux79 Supp7 DomainMarkov.Aux79

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The observations of a chart path** in a physical filtration `𝓖` on the event `M`. -/
structure AObs (𝓖 : Filtration ℝ≥0 mΩ) (M : Set Ω) (Γ : Ω → ℝ≥0 → ℂ) (L : Ω → ℝ≥0∞) : Prop where
  initial : MeasurableSet[𝓖 0] M
  coordinates : ∀ t s : ℝ≥0, s ≤ t → Measurable[𝓖 t] (M.indicator fun ω => Γ ω s)
  survival : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] (M ∩ {ω | (t : ℝ≥0∞) < L ω})

variable {𝓖 : Filtration ℝ≥0 mΩ} {M : Set Ω} {Γ : Ω → ℝ≥0 → ℂ} {L : Ω → ℝ≥0∞}

/-- **The supported clock is adapted.** -/
theorem AObs.measurable_clock (ho : AObs 𝓖 M Γ L) (hg : ∀ ω ∈ M, IsAGood Γ L ω) (t : ℝ≥0) :
    Measurable[𝓖 t] (M.indicator (aClock Γ t)) :=
  @measurable_indicator_clock_of_prefix Ω (𝓖 t) M (𝓖.mono zero_le _ ho.initial) Γ (aClock Γ t) t
    (fun ω hω => (hg ω hω).cont) (ho.coordinates t)
    (fun ω hω => by rw [(hg ω hω).zero]; exact le_rfl) (fun ω hω => (hg ω hω).aClock_eq t)

/-- **The capacity-time filtration**: the time change of `𝓖` along the supported clock. -/
def aFilt (𝓖 : Filtration ℝ≥0 mΩ) (M : Set Ω) (Γ : Ω → ℝ≥0 → ℂ)
    (hQa : ∀ t, Measurable[𝓖 t] (M.indicator (aClock Γ t))) : Filtration ℝ≥0 mΩ :=
  timeChange 𝓖 (fun t => M.indicator (aClock Γ t)) hQa

/-- `𝓖 0`-events are `aFilt`-events at `0`. -/
theorem le_aFilt_zero (hQa : ∀ t, Measurable[𝓖 t] (M.indicator (aClock Γ t))) : 𝓖 0 ≤ aFilt 𝓖 M Γ hQa 0 :=
  le_timeChange_zero

/-! ### The capacity prefix reader -/

/-- **The chart path in capacity time, read from the observations through the physical line `t`.** -/
def aCapPrefix (M : Set Ω) (Γ : Ω → ℝ≥0 → ℂ) (L : Ω → ℝ≥0∞) (t q : ℝ≥0) (ω : Ω) : ℂ :=
  M.indicator (fun ω => Γ ω (min (invClock (fun s => ((M.indicator (aClock Γ (min s t)) ω : ℝ≥0) : ℝ))
    (M.indicator (fun ω => min (L ω) (t : ℝ≥0∞)) ω) q) t)) ω

theorem AObs.measurable_aCapPrefix (ho : AObs 𝓖 M Γ L) (hg : ∀ ω ∈ M, IsAGood Γ L ω) (t q : ℝ≥0) :
    Measurable[𝓖 t] (aCapPrefix M Γ L t q) := by
  classical
  let Γ' : Ω → ℝ≥0 → ℂ := fun ω s => M.indicator (fun ω => Γ ω (min s t)) ω
  have hc : ∀ ω, Continuous (Γ' ω) := by
    intro ω
    by_cases hω : ω ∈ M
    · have he : Γ' ω = fun s => Γ ω (min s t) := funext fun _ => indicator_of_mem hω _
      rw [he]
      exact (hg ω hω).cont.comp (continuous_id.min continuous_const)
    · have he : Γ' ω = fun _ => 0 := funext fun _ => indicator_of_notMem hω _
      rw [he]
      exact continuous_const
  have hC : ∀ s, Measurable[𝓖 t] fun ω => ((M.indicator (aClock Γ (min s t)) ω : ℝ≥0) : ℝ) := fun s =>
    (measurable_coe_nnreal_real.comp (ho.measurable_clock hg (min s t))).mono
      (𝓖.mono (min_le_right _ _)) le_rfl
  have hL := measurable_indicator_min_of_survival ho.initial ho.survival t
  have hi := @measurable_invClock_of_coordinates Ω (𝓖 t) _ _ hC hL q
  have h := @measurable_eval_of_continuous_coordinates Ω (𝓖 t) Γ' hc
    (fun s => ho.coordinates t (min s t) (min_le_right _ _)) _ hi
  convert h using 1
  funext ω
  by_cases hω : ω ∈ M
  · simp only [aCapPrefix, Γ', indicator_of_mem hω]
  · simp only [aCapPrefix, Γ', indicator_of_notMem hω]

omit mΩ in
/-- **On the live reached-capacity event, the prefix reader is the chart path in capacity time.** -/
theorem aCapPrefix_eq {ω : Ω} (hω : ω ∈ M) (hg : IsAGood Γ L ω) {q t : ℝ≥0}
    (hq : (q : ℝ≥0∞) < aLife Γ L ω) (hqt : q ≤ aClock Γ t ω) :
    aCapPrefix M Γ L t q ω = aPath Γ L ω q := by
  classical
  have hqC : (q : ℝ) ≤ chartClock (Γ ω) t := by
    rw [← hg.coe_aClock t]
    exact_mod_cast hqt
  obtain ⟨he, ht⟩ := invClock_min_eq hg.clock hq.le hqC
  have heC : (fun s => ((M.indicator (aClock Γ (min s t)) ω : ℝ≥0) : ℝ)) =
      fun s => chartClock (Γ ω) (min s t) := by
    funext s
    rw [indicator_of_mem hω, hg.coe_aClock]
  unfold aCapPrefix
  rw [indicator_of_mem hω, heC, indicator_of_mem hω, he, min_eq_left ht]
  rfl

/-- **Strict capacity survival through a reached capacity is observable at the physical line.** -/
theorem AObs.measurableSet_capacityCut (ho : AObs 𝓖 M Γ L) (hg : ∀ ω ∈ M, IsAGood Γ L ω) (q t : ℝ≥0) :
    MeasurableSet[𝓖 t] {ω | (q : ℝ≥0∞) < M.indicator (aLife Γ L) ω ∧ q ≤ M.indicator (aClock Γ t) ω} := by
  classical
  let Q := M.indicator (aClock Γ t)
  have he : {ω | (q : ℝ≥0∞) < M.indicator (aLife Γ L) ω ∧ q ≤ Q ω} =
      {ω | q < Q ω} ∪ ({ω | q = Q ω} ∩ (M ∩ {ω | (t : ℝ≥0∞) < L ω})) := by
    ext ω
    by_cases hω : ω ∈ M
    · have hQV := (hg ω hω).aClock_le_aLife t
      have hl := (hg ω hω).aClock_lt_aLife_iff (t := t)
      simp only [Q, indicator_of_mem hω, mem_ofPred_eq, mem_union, mem_inter_iff, hω, true_and]
      constructor
      · rintro ⟨hv, hq⟩
        rcases lt_or_eq_of_le hq with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr ⟨heq, hl.1 (heq ▸ hv)⟩
      · rintro (hlt | ⟨heq, ht⟩)
        · exact ⟨(ENNReal.coe_lt_coe.2 hlt).trans_le hQV, hlt.le⟩
        · exact ⟨heq.symm ▸ hl.2 ht, heq.le⟩
    · simp only [Q, indicator_of_notMem hω, mem_ofPred_eq, false_and, mem_union, not_lt_zero, mem_inter_iff,
        hω, or_self, and_false]
  rw [show {ω | (q : ℝ≥0∞) < M.indicator (aLife Γ L) ω ∧ q ≤ Q ω} = _ from he]
  have hQ := ho.measurable_clock hg t
  exact (measurableSet_lt measurable_const hQ).union
    ((measurableSet_eq_fun measurable_const hQ).inter (ho.survival t))

/-! ### The adapted driver -/

/-- **The driver is adapted before the supported capacity lifetime** in the capacity-time filtration (RETPLUMB's
`retKilledDriverObservable` for the abstract path). -/
theorem AObs.adaptedBefore_aDriver (ho : AObs 𝓖 M Γ L) (hg : ∀ ω ∈ M, IsAGood Γ L ω) :
    AdaptedBefore (aFilt 𝓖 M Γ (ho.measurable_clock hg)) (M.indicator (aLife Γ L)) (aDriver Γ L) := by
  classical
  have hW : ∀ ω ∈ M, IsAGen Γ L ω fun s => aDriver Γ L s ω := fun ω hω => isAGen_aDriver (hg ω hω).gen
  have hmem (ω : Ω) (q : ℝ≥0) (hq : (q : ℝ≥0∞) < M.indicator (aLife Γ L) ω) : ω ∈ M := by
    by_contra hω
    simp only [indicator_of_notMem hω, not_lt_zero] at hq
  apply adaptedBefore_timeChange_of_reaches (ho.measurable_clock hg)
  · intro ω s t hst
    by_cases hω : ω ∈ M
    · simp only [indicator_of_mem hω]
      rw [(hg ω hω).aClock_eq, (hg ω hω).aClock_eq]
      exact Real.toNNReal_le_toNNReal ((hg ω hω).mono hst)
    · simp only [indicator_of_notMem hω, le_refl]
  · intro ω q hq
    have hω := hmem ω q hq
    rw [indicator_of_mem hω] at hq
    obtain ⟨t, ht⟩ := (hg ω hω).exists_aClock_ge hq
    exact ⟨t, by simpa only [indicator_of_mem hω] using ht⟩
  · intro q t A hA
    let E := {ω | (q : ℝ≥0∞) < M.indicator (aLife Γ L) ω ∧ q ≤ M.indicator (aClock Γ t) ω}
    have hEM : E ⊆ M := fun ω hω => hmem ω q hω.1
    have hEV : ∀ ω ∈ E, (q : ℝ≥0∞) < aLife Γ L ω := fun ω hω => by
      simpa only [indicator_of_mem (hEM hω)] using hω.1
    have hEQ : ∀ ω ∈ E, q ≤ aClock Γ t ω := fun ω hω => by
      simpa only [indicator_of_mem (hEM hω)] using hω.2
    have hread := @measurableSet_driver_of_observed_prefix Ω (𝓖 t) E
      (ho.measurableSet_capacityCut hg q t) (aPath Γ L) (fun ω s => aCapPrefix M Γ L t s ω)
      (aDriver Γ L) (aLife Γ L) q (fun s => ho.measurable_aCapPrefix hg t s)
      (fun ω hω s hs => aCapPrefix_eq (hEM hω) (hg ω (hEM hω))
        ((ENNReal.coe_le_coe.2 hs).trans_lt (hEV ω hω)) (hs.trans (hEQ ω hω)))
      (fun ω hω => (hW ω (hEM hω)).1) (fun ω hω => (hW ω (hEM hω)).2.1)
      (fun ω hω => (hW ω (hEM hω)).2.2) hEV A hA
    convert hread using 1
    ext ω
    change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ _)
    exact and_right_comm

/-! ### The supported trace -/

/-- **The supported chart path in capacity time** (`0` off `M`). -/
def aTrace (M : Set Ω) (Γ : Ω → ℝ≥0 → ℂ) (L : Ω → ℝ≥0∞) (ω : Ω) (q : ℝ≥0) : ℂ :=
  M.indicator (fun ω => aPath Γ L ω q) ω

omit mΩ in
theorem aTrace_zero (hg : ∀ ω ∈ M, IsAGood Γ L ω) (ω : Ω) : aTrace M Γ L ω 0 = 0 := by
  by_cases hω : ω ∈ M
  · obtain ⟨W, hW⟩ := (hg ω hω).gen
    simp only [aTrace, indicator_of_mem hω]
    exact hW.2.2.1
  · simp only [aTrace, indicator_of_notMem hω]

omit mΩ in
theorem continuousOn_aTrace (hg : ∀ ω ∈ M, IsAGood Γ L ω) (ω : Ω) :
    ContinuousOn (aTrace M Γ L ω) {t | (t : ℝ≥0∞) ≤ M.indicator (aLife Γ L) ω} := by
  by_cases hω : ω ∈ M
  · obtain ⟨W, hW⟩ := (hg ω hω).gen
    have e : aTrace M Γ L ω = aPath Γ L ω := funext fun q => indicator_of_mem hω _
    rw [e, indicator_of_mem hω]
    exact hW.2.2.2.1
  · have e : aTrace M Γ L ω = fun _ => 0 := funext fun q => indicator_of_notMem hω _
    rw [e]
    exact continuousOn_const

omit mΩ in
theorem aTrace_of_mem {ω : Ω} (hω : ω ∈ M) : aTrace M Γ L ω = aPath Γ L ω :=
  funext fun _ => indicator_of_mem hω _

/-- The supported physical lifetime is measurable. -/
theorem AObs.measurable_indicator_L (ho : AObs 𝓖 M Γ L) : Measurable (M.indicator L) := by
  classical
  refine measurable_of_Ioi fun a => ?_
  induction a using ENNReal.recTopCoe with
  | top => simp only [Ioi_top, preimage_empty, MeasurableSet.empty]
  | coe s =>
    have he : M.indicator L ⁻¹' Ioi (s : ℝ≥0∞) = M ∩ {ω | (s : ℝ≥0∞) < L ω} := by
      ext ω
      by_cases hω : ω ∈ M <;> simp [hω]
    rw [he]
    exact 𝓖.le s _ (ho.survival s)

/-- **The supported trace has measurable coordinates.** -/
theorem AObs.measurable_aTrace (ho : AObs 𝓖 M Γ L) (hg : ∀ ω ∈ M, IsAGood Γ L ω) (q : ℝ≥0) :
    Measurable fun ω => aTrace M Γ L ω q := by
  classical
  have hM : MeasurableSet M := 𝓖.le 0 _ ho.initial
  let ΓM : Ω → ℝ≥0 → ℂ := fun ω s => M.indicator (fun ω => Γ ω s) ω
  have hc : ∀ ω, Continuous (ΓM ω) := by
    intro ω
    by_cases hω : ω ∈ M
    · have he : ΓM ω = Γ ω := funext fun _ => indicator_of_mem hω _
      rw [he]
      exact (hg ω hω).cont
    · have he : ΓM ω = fun _ => 0 := funext fun _ => indicator_of_notMem hω _
      rw [he]
      exact continuous_const
  have hm : ∀ s, Measurable fun ω => ΓM ω s := fun s =>
    (ho.coordinates s s le_rfl).mono (𝓖.le s) le_rfl
  have hC : ∀ s, Measurable fun ω => ((M.indicator (aClock Γ s) ω : ℝ≥0) : ℝ) := fun s =>
    measurable_coe_nnreal_real.comp ((ho.measurable_clock hg s).mono (𝓖.le s) le_rfl)
  have hi := measurable_invClock_of_coordinates hC ho.measurable_indicator_L q
  have h := measurable_eval_of_continuous_coordinates hc hm hi
  convert h.indicator hM using 1
  funext ω
  by_cases hω : ω ∈ M
  · have e : (fun s => ((aClock Γ s ω : ℝ≥0) : ℝ)) = chartClock (Γ ω) := by
      funext s
      rw [(hg ω hω).coe_aClock]
    simp only [aTrace, aPath, indicator_of_mem hω, ΓM]
    rw [e]
  · simp only [aTrace, indicator_of_notMem hω]

/-! ### The assembly -/

/-- **The A-stopped processes of a good observed chart path**: a globally continuous driver from `0`, adapted to the
capacity-time filtration `aFilt`, equal to `aDriver` before the supported capacity lifetime `M.indicator (aLife Γ L)`
(an `aFilt`-stopping time), and generating the supported trace `aTrace M Γ L` on `M`. -/
theorem AObs.exists_driver (ho : AObs 𝓖 M Γ L) (hg : ∀ ω ∈ M, IsAGood Γ L ω) :
    ∃ W : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun q => W q ω) ∧ (∀ ω, W 0 ω = 0) ∧
      StronglyAdapted (aFilt 𝓖 M Γ (ho.measurable_clock hg)) W ∧
      (∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < M.indicator (aLife Γ L) ω → W q ω = aDriver Γ L q ω) ∧
      (∀ t : ℝ≥0, MeasurableSet[aFilt 𝓖 M Γ (ho.measurable_clock hg) t]
        {ω | M.indicator (aLife Γ L) ω ≤ t}) ∧
      ∀ ω ∈ M, IsGeneratingTrace (fun q => W q ω) (M.indicator (aLife Γ L) ω) (aTrace M Γ L ω) := by
  have ha := ho.adaptedBefore_aDriver hg
  obtain ⟨W, hW0, hWc, hWa, he⟩ := exists_continuous_adapted_stopped continuous_aDriver aDriver_zero ha
  refine ⟨W, hWc, hW0, hWa, he, Ito.isStoppingTime_lifetime ha, fun ω hω => ?_⟩
  have hgen := (isAGen_aDriver (hg ω hω).gen).2.2
  have hV : M.indicator (aLife Γ L) ω = aLife Γ L ω := indicator_of_mem hω _
  rw [hV, aTrace_of_mem hω]
  refine StoppedK2.isGeneratingTrace_congr (fun q hq => (he ω q ?_).symm) hgen
  rw [hV]
  exact hq

end InteractingSLE.RLC.AStopProc

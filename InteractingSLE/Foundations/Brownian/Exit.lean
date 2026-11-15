import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Order.Compact

/-!
# Exit times of planar paths

Packet GEO-BM of the geometry foundation (`planning/INFRA-GEO.md` §3 "SLE", §4), deterministic
part. Infrastructure (textbook material, [Law05] Lawler, *Conformally Invariant Processes in the
Plane*, Ch. 2), not a frozen source-facing file.

* `exitTime D γ : ℝ≥0∞` is the first time the path `γ : ℝ≥0 → ℂ` is outside `D` (`⊤` if it never
  leaves `D`); `exitPoint D γ` is the position at that time.
* For an open `D` and a continuous `γ` the infimum is attained (`exists_eq_exitTime`,
  `exitPoint_not_mem`), `exitTime D γ ≤ t ↔ ∃ s ≤ t, γ s ∉ D` (`exitTime_le_coe_iff`), and the path
  stays in `D` before the exit time (`mem_of_lt_exitTime`).
* For a process with continuous paths, adapted to a filtration `𝓕`, the exit time from an open
  set is an `𝓕`-stopping time (`isStoppingTime_exitTime`): `{exitTime ≤ t}` is the countable
  intersection over `m` of the events "some time in a countable dense subset of `[0, t]` is within
  distance `1/(m+1)` of `Dᶜ`" (the complement is closed, so no right-continuity of `𝓕` is needed).
  The exit time and the exit point are measurable (`measurable_exitTime`, `measurable_exitPoint`).
-/

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

/-- First exit time of a path from `D`, valued in `ℝ≥0∞` (`∞` if it never exits). -/
def exitTime (D : Set ℂ) (γ : ℝ≥0 → ℂ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : γ t ∉ D), (t : ℝ≥0∞)

/-- The position of the path at its exit time from `D`. For a path that never leaves `D` this is
`γ 0` by the convention `(⊤ : ℝ≥0∞).toNNReal = 0` (as for Mathlib's `stoppedValue`); every
statement about `exitPoint` assumes `exitTime D γ < ⊤`. -/
def exitPoint (D : Set ℂ) (γ : ℝ≥0 → ℂ) : ℂ :=
  γ (exitTime D γ).toNNReal

variable {D D' : Set ℂ} {γ : ℝ≥0 → ℂ}

lemma exitTime_le_of_not_mem {t : ℝ≥0} (h : γ t ∉ D) : exitTime D γ ≤ t :=
  iInf₂_le t h

lemma mem_of_lt_exitTime {t : ℝ≥0} (h : (t : ℝ≥0∞) < exitTime D γ) : γ t ∈ D := by
  by_contra hn
  exact absurd (exitTime_le_of_not_mem hn) (not_le.2 h)

lemma exitTime_eq_top_iff : exitTime D γ = ⊤ ↔ ∀ t, γ t ∈ D := by
  constructor
  · intro h t
    exact mem_of_lt_exitTime (h ▸ ENNReal.coe_lt_top)
  · intro h
    refine eq_top_iff.2 (le_iInf₂ fun t ht => absurd (h t) ht)

lemma exitTime_lt_top_iff : exitTime D γ < ⊤ ↔ ∃ t, γ t ∉ D := by
  rw [lt_top_iff_ne_top, Ne, exitTime_eq_top_iff, not_forall]

lemma exitTime_mono (hDD' : D ⊆ D') : exitTime D γ ≤ exitTime D' γ :=
  le_iInf₂ fun t ht => iInf₂_le t fun h => ht (hDD' h)

lemma exitTime_eq_zero_of_not_mem (h : γ 0 ∉ D) : exitTime D γ = 0 :=
  le_antisymm (by simpa using exitTime_le_of_not_mem h) bot_le

lemma exitTime_univ : exitTime univ γ = ⊤ :=
  exitTime_eq_top_iff.2 fun _ => mem_univ _

/-- For an open set and a continuous path the infimum defining the exit time is attained. -/
lemma exists_eq_exitTime (hD : IsOpen D) (hγ : Continuous γ) (h : exitTime D γ ≠ ⊤) :
    ∃ t : ℝ≥0, exitTime D γ = t ∧ γ t ∉ D := by
  set S : Set ℝ≥0 := γ ⁻¹' Dᶜ with hS
  have hSc : IsClosed S := hD.isClosed_compl.preimage hγ
  have hSne : S.Nonempty := by
    obtain ⟨t, ht⟩ := exitTime_lt_top_iff.1 (lt_top_iff_ne_top.2 h)
    exact ⟨t, ht⟩
  have hmem : sInf S ∈ S := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  refine ⟨sInf S, le_antisymm (exitTime_le_of_not_mem hmem) ?_, hmem⟩
  exact le_iInf₂ fun t ht => ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow S) ht)

lemma exitTime_le_coe_iff (hD : IsOpen D) (hγ : Continuous γ) (t : ℝ≥0) :
    exitTime D γ ≤ t ↔ ∃ s ≤ t, γ s ∉ D := by
  constructor
  · intro h
    obtain ⟨s, hs, hsD⟩ := exists_eq_exitTime hD hγ (ne_top_of_le_ne_top ENNReal.coe_ne_top h)
    exact ⟨s, by rw [hs] at h; exact_mod_cast h, hsD⟩
  · rintro ⟨s, hst, hs⟩
    exact (exitTime_le_of_not_mem hs).trans (ENNReal.coe_le_coe.2 hst)

lemma exitTime_toNNReal_eq (h : exitTime D γ ≠ ⊤) :
    ((exitTime D γ).toNNReal : ℝ≥0∞) = exitTime D γ :=
  ENNReal.coe_toNNReal h

lemma exitPoint_not_mem (hD : IsOpen D) (hγ : Continuous γ) (h : exitTime D γ ≠ ⊤) :
    exitPoint D γ ∉ D := by
  obtain ⟨t, ht, htD⟩ := exists_eq_exitTime hD hγ h
  simpa [exitPoint, ht] using htD

lemma exitTime_pos (hD : IsOpen D) (hγ : Continuous γ) (h0 : γ 0 ∈ D) : 0 < exitTime D γ := by
  rcases eq_or_ne (exitTime D γ) ⊤ with h | h
  · simp [h]
  obtain ⟨t, ht, htD⟩ := exists_eq_exitTime hD hγ h
  rw [ht]
  rcases eq_or_ne t 0 with rfl | ht0
  · exact absurd h0 htD
  · exact_mod_cast pos_iff_ne_zero.2 ht0

/-- The exit point lies in the closure of `D` when the path starts in `D`. -/
lemma exitPoint_mem_closure (hD : IsOpen D) (hγ : Continuous γ) (h0 : γ 0 ∈ D)
    (h : exitTime D γ ≠ ⊤) : exitPoint D γ ∈ closure D := by
  obtain ⟨t, ht, -⟩ := exists_eq_exitTime hD hγ h
  have htpos : 0 < t := by
    have := exitTime_pos hD hγ h0
    rw [ht] at this
    exact_mod_cast this
  have hlim : Tendsto γ (𝓝[<] t) (𝓝 (γ t)) := (hγ.tendsto t).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] t, γ s ∈ D := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mem_of_lt_exitTime (by rw [ht]; exact_mod_cast hs)
  have hne : (𝓝[<] t).NeBot := by
    rw [← (nhdsWithin_Ioo_eq_nhdsLT htpos)]
    exact (mem_closure_iff_nhdsWithin_neBot).1
      (by rw [closure_Ioo htpos.ne]; exact right_mem_Icc.2 htpos.le)
  simp only [exitPoint, ht, ENNReal.toNNReal_coe]
  exact mem_closure_of_tendsto hlim hev

/-- The exit point of a continuous path started in an open set `D` lies on the frontier of `D`. -/
lemma exitPoint_mem_frontier (hD : IsOpen D) (hγ : Continuous γ) (h0 : γ 0 ∈ D)
    (h : exitTime D γ ≠ ⊤) : exitPoint D γ ∈ frontier D :=
  ⟨exitPoint_mem_closure hD hγ h0 h, by rw [hD.interior_eq]; exact exitPoint_not_mem hD hγ h⟩

/-! ### Measurability and the stopping-time property -/

/-- A countable subset of `[0, t]` that is dense in `[0, t]` (rational times and `t`). -/
def ratTimesLE (t : ℝ≥0) : Set ℝ≥0 :=
  insert t {s | s ≤ t ∧ ∃ q : ℚ, (q : ℝ).toNNReal = s}

lemma countable_ratTimesLE (t : ℝ≥0) : (ratTimesLE t).Countable := by
  refine Countable.insert t ?_
  refine ((Set.countable_range (fun q : ℚ => (q : ℝ).toNNReal)).mono ?_)
  rintro s ⟨-, q, rfl⟩
  exact ⟨q, rfl⟩

lemma le_of_mem_ratTimesLE {t s : ℝ≥0} (hs : s ∈ ratTimesLE t) : s ≤ t := by
  rcases hs with rfl | ⟨hs, -⟩
  · exact le_rfl
  · exact hs

lemma exists_mem_ratTimesLE_near {t s : ℝ≥0} (hst : s ≤ t) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q ∈ ratTimesLE t, dist q s < δ := by
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact ⟨s, mem_insert _ _, by simpa using hδ⟩
  · -- a rational time in `(s, min t (s + δ))`
    have hδ' : (0 : ℝ≥0) < δ.toNNReal := Real.toNNReal_pos.2 hδ
    have hlt' : s < min t (s + δ.toNNReal) := lt_min hlt (lt_add_of_pos_right s hδ')
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (NNReal.coe_lt_coe.2 hlt')
    have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg s).trans hq1.le
    have hq'eq : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = (q : ℝ) := Real.coe_toNNReal _ hq0
    refine ⟨(q : ℝ).toNNReal, Or.inr ⟨?_, q, rfl⟩, ?_⟩
    · have := hq2.le
      rw [← hq'eq] at this
      exact (NNReal.coe_le_coe.1 this).trans (min_le_left _ _)
    · rw [NNReal.dist_eq, hq'eq, abs_of_pos (by linarith)]
      have h2 : (q : ℝ) < ((s + δ.toNNReal : ℝ≥0) : ℝ) :=
        hq2.trans_le (NNReal.coe_le_coe.2 (min_le_right _ _))
      rw [NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at h2
      linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The event `{exitTime ≤ t}` through countably many times, for a continuous path and an open `D`
with nonempty complement. -/
lemma exitTime_le_coe_iff_forall_exists (hD : IsOpen D) (hDc : (Dᶜ).Nonempty) (hγ : Continuous γ)
    (t : ℝ≥0) :
    exitTime D γ ≤ t ↔
      ∀ m : ℕ, ∃ q ∈ ratTimesLE t, infDist (γ q) Dᶜ < 1 / ((m : ℝ) + 1) := by
  rw [exitTime_le_coe_iff hD hγ]
  constructor
  · rintro ⟨s, hst, hs⟩ m
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδγ⟩ := Metric.continuous_iff.1 hγ s _ hm
    obtain ⟨q, hq, hqs⟩ := exists_mem_ratTimesLE_near hst hδ
    exact ⟨q, hq, (infDist_le_dist_of_mem hs).trans_lt (hδγ q hqs)⟩
  · intro h
    -- the continuous function `r ↦ infDist (γ r) Dᶜ` attains its minimum on `[0, t]`
    obtain ⟨s, hs, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMinOn
      (nonempty_Icc.2 bot_le)
      ((continuous_infDist_pt (Dᶜ)).comp hγ).continuousOn
    refine ⟨s, hs.2, fun hsD => ?_⟩
    have hpos : 0 < infDist (γ s) Dᶜ := by
      have hnc : γ s ∉ closure Dᶜ := by rwa [hD.isClosed_compl.closure_eq, Set.notMem_compl_iff]
      rw [mem_closure_iff_infDist_zero hDc] at hnc
      exact lt_of_le_of_ne infDist_nonneg (Ne.symm hnc)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    obtain ⟨q, hq, hqD⟩ := h m
    have hle : infDist (γ s) Dᶜ ≤ infDist (γ q) Dᶜ :=
      hmin ⟨bot_le, le_of_mem_ratTimesLE hq⟩
    linarith

/-- The exit time of a continuous adapted process from an open set is a stopping time. -/
theorem isStoppingTime_exitTime {𝓕 : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℂ}
    (hZ : ∀ t, Measurable[𝓕 t] (Z t)) (hc : ∀ ω, Continuous (Z · ω)) (hD : IsOpen D) :
    IsStoppingTime 𝓕 (fun ω => exitTime D (Z · ω)) := by
  intro t
  rcases (Dᶜ).eq_empty_or_nonempty with hDc | hDc
  · have hDu : D = univ := by simpa using hDc
    have : {ω | (exitTime D (Z · ω) : WithTop ℝ≥0) ≤ t} = ∅ := by
      ext ω
      simp only [hDu, exitTime_univ, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact ENNReal.coe_lt_top
    change MeasurableSet[𝓕 t] {ω | (exitTime D (Z · ω) : WithTop ℝ≥0) ≤ t}
    rw [this]
    exact @MeasurableSet.empty _ (𝓕 t)
  have hset : {ω | (exitTime D (Z · ω) : WithTop ℝ≥0) ≤ t} =
      ⋂ m : ℕ, ⋃ q ∈ ratTimesLE t, {ω | infDist (Z q ω) Dᶜ < 1 / ((m : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
    exact exitTime_le_coe_iff_forall_exists hD hDc (hc ω) t
  change MeasurableSet[𝓕 t] {ω | (exitTime D (Z · ω) : WithTop ℝ≥0) ≤ t}
  rw [hset]
  refine MeasurableSet.iInter fun m => ?_
  refine MeasurableSet.biUnion (countable_ratTimesLE t) fun q hq => ?_
  have hq' : Measurable[𝓕 t] (Z q) := (hZ q).mono (𝓕.mono (le_of_mem_ratTimesLE hq)) le_rfl
  exact measurableSet_lt ((continuous_infDist_pt _).measurable.comp hq') measurable_const

/-- The exit time of a continuous process with measurable time sections is measurable. -/
theorem measurable_exitTime {Z : ℝ≥0 → Ω → ℂ} (hZ : ∀ t, Measurable (Z t))
    (hc : ∀ ω, Continuous (Z · ω)) (hD : IsOpen D) :
    Measurable (fun ω => exitTime D (Z · ω)) := by
  have hst := isStoppingTime_exitTime (𝓕 := Filtration.const ℝ≥0 mΩ le_rfl) hZ hc hD
  refine measurable_of_Iic fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe t => exact hst t

/-- The exit point of a continuous process with measurable time sections is measurable. -/
theorem measurable_exitPoint {Z : ℝ≥0 → Ω → ℂ} (hZ : ∀ t, Measurable (Z t))
    (hc : ∀ ω, Continuous (Z · ω)) (hD : IsOpen D) :
    Measurable (fun ω => exitPoint D (Z · ω)) := by
  have hj : Measurable (Function.uncurry fun (t : ℝ≥0) (ω : Ω) => Z t ω) :=
    measurable_uncurry_of_continuous_of_measurable hc hZ
  exact hj.comp (((measurable_exitTime hZ hc hD).ennreal_toNNReal).prodMk measurable_id)

end InteractingSLE

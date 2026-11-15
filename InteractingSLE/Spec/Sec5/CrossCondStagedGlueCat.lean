/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedMeanFlow
import InteractingSLE.Spec.Sec7.StripWallVersion
import InteractingSLE.Spec.Restart.StagedEntranceInst
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart

/-!
# Deterministic Loewner facts for a concatenation of finitely many pieces

Packet PROVE-STAGED5. The restart step of an extreme-angle schedule (`isEntranceHistoryLocal_schedule_step`) needs, at
every piece `k`, two deterministic facts about the trace `α` of the concatenated driver: the **join formula** (after the
start `S_k` of piece `k`, `α` is the image of the piece's own trace under the inverse of the chart of the earlier
pieces) and the **frontier** of that chart's domain (it lies on `α([0, S_k])`). PROVE-STAGEDLOC2 / PROVE-STRIPSYS28
proved both for two pieces (`StripWall.exists_wallVersions_twoAngle`, `Strip.frontier_recChart`); here for the
back-nested concatenation `catN w T n` of PROVE-CROSSCOND-STAGED2 (pieces `w 0, …, w n`, own times `T j`, cumulative
times `cumT T k = T 0 + ⋯ + T k`):

* `cumT_mono`, **`catN_of_le_cumT`** (the concatenation through `n` agrees with that through `k ≤ n` up to `cumT T k`),
  **`catN_congr_cumT`** (it only reads each piece on its own time interval);
* **`exists_isGeneratingTrace_catN`**: if every piece has a generating trace on `[0, ∞)` that stays in `ℍ`, so does the
  concatenation (iterated Loewner concatenation, `LoewnerConcat.isGeneratingTrace_catPath`);
* `isGeneratingTrace_catN_of_le`; **`trace_catN_zero`**, **`trace_catN_add`**: the join formula
  `α(cumT T k + u) = F_{cumT T k}(β(u))`, `0 < u ≤ T (k+1)`, `F` the centred inverse Loewner map of the concatenation
  through `k` and `β` the trace of piece `k + 1`;
* **`catChartN_inv_eq`**, **`dom_catChartN_eq`**, **`frontier_catChartN`**: the recentred Loewner chart of the
  concatenation through `k` has inverse `F_{cumT T k}` and its domain is a component of `ℍ ∖ α([0, cumT T k])` for any
  generating trace `α` of a continuous driver agreeing with the concatenation up to `cumT T k`, so its frontier in `ℍ`
  lies on `α([0, cumT T k])`.

All statements are deterministic. No probability, no Theorem 1.2/1.3 (R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.CrossCond.StagedGlue

open Sec7.StripSideHeightProb (catPath catPath_of_le catPath_zero continuous_catPath)
open InteractingSLE.Sec5.CrossCond.Staged (catN cumT catChartN iterChart cumT_succ cumT_zero continuous_catN
  catN_zero rpath_zero_of_zero continuous_rpath_of mem_dom_recenter_loewner_iff mem_dom_loewner_iff_mem_diff_hull)

section Cat

variable {w w' : ℕ → ℝ≥0 → ℝ} {T : ℕ → ℝ≥0}

theorem cumT_mono {k n : ℕ} (h : k ≤ n) : cumT T k ≤ cumT T n :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h))

/-- **The concatenation through piece `n` agrees with the concatenation through piece `k ≤ n` up to `cumT T k`.** -/
theorem catN_of_le_cumT {k n : ℕ} (hkn : k ≤ n) {t : ℝ≥0} (ht : t ≤ cumT T k) :
    catN w T n t = catN w T k t := by
  induction n with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.1 hkn
    rfl
  | succ n ih =>
    rcases Nat.of_le_succ hkn with h | h
    · change catPath (catN w T n) (cumT T n) (w (n + 1)) t = _
      rw [catPath_of_le (ht.trans (cumT_mono h)), ih h]
    · subst h
      rfl

/-- **The concatenation only reads each piece on its own time interval.** -/
theorem catN_congr_cumT : ∀ {k : ℕ}, (∀ j ≤ k, ∀ t ≤ T j, w j t = w' j t) →
    ∀ t ≤ cumT T k, catN w T k t = catN w' T k t
  | 0, h, t, ht => h 0 le_rfl t (by rwa [cumT_zero] at ht)
  | k + 1, h, t, ht => by
    have ih := catN_congr_cumT (k := k) fun j hj => h j (Nat.le_succ_of_le hj)
    change catPath (catN w T k) (cumT T k) (w (k + 1)) t = catPath (catN w' T k) (cumT T k) (w' (k + 1)) t
    unfold catPath
    split_ifs with htk
    · exact ih t htk
    · rw [ih (cumT T k) le_rfl, h (k + 1) le_rfl (t - cumT T k) ?_]
      rw [cumT_succ] at ht
      exact tsub_le_iff_left.2 ht

/-- **Iterated Loewner concatenation**: if every piece through `k` has a generating trace on `[0, ∞)` staying in `ℍ`
at positive times, the concatenation through `k` has a generating trace on `[0, ∞)`. -/
theorem exists_isGeneratingTrace_catN (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) :
    ∀ k, (∀ j ≤ k, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (w j) ⊤ η ∧ ∀ t, 0 < t → η t ∈ H) →
      ∃ α : ℝ≥0 → ℂ, IsGeneratingTrace (catN w T k) ⊤ α
  | 0, h => by
    obtain ⟨η, hη, -⟩ := h 0 le_rfl
    exact ⟨η, hη⟩
  | k + 1, h => by
    obtain ⟨α, hα⟩ := exists_isGeneratingTrace_catN hc h0 k fun j hj => h j (Nat.le_succ_of_le hj)
    obtain ⟨η, hη, hH⟩ := h (k + 1) le_rfl
    exact ⟨_, LoewnerConcat.isGeneratingTrace_catPath (continuous_catN hc h0 k) (catN_zero h0 k) (hc (k + 1))
      (h0 (k + 1)) (IsGeneratingTrace.mono_horizon hα le_top) hη hH⟩

/-- A generating trace of the concatenation through `n` generates the concatenation through `k ≤ n` up to
`cumT T k`. -/
theorem isGeneratingTrace_catN_of_le {k n : ℕ} (hkn : k ≤ n) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (catN w T n) ⊤ α) : IsGeneratingTrace (catN w T k) (cumT T k) α :=
  IsGeneratingTrace.of_eqOn_lt hα fun _ ht => (catN_of_le_cumT hkn (ENNReal.coe_lt_coe.1 ht).le).symm

/-- **The first piece**: before `T 0` a generating trace of the concatenation is the trace of the first piece. -/
theorem trace_catN_zero (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) {n : ℕ} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (catN w T n) ⊤ α) {β : ℝ≥0 → ℂ} (hβ : IsGeneratingTrace (w 0) ⊤ β) {u : ℝ≥0}
    (hu : u ≤ T 0) : α u = β u := by
  have hle : u ≤ cumT T 0 := by rw [cumT_zero]; exact hu
  rw [← LP.traceAt_eq_of_isGeneratingTrace hα (continuous_catN hc h0 n).continuousOn (catN_zero h0 n)
    ENNReal.coe_lt_top, LP.traceAt_congr fun r hr => catN_of_le_cumT (Nat.zero_le n) (hr.trans hle)]
  exact LP.traceAt_eq_of_isGeneratingTrace hβ (hc 0).continuousOn (h0 0) ENNReal.coe_lt_top

/-- **The join formula**: after the end `cumT T k` of the pieces `0, …, k`, a generating trace of the concatenation
is the image of the trace of piece `k + 1` under the centred inverse Loewner map of the concatenation through `k`, as
long as piece `k + 1` runs. -/
theorem trace_catN_add (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) {n k : ℕ} (hkn : k + 1 ≤ n)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (catN w T n) ⊤ α) {β : ℝ≥0 → ℂ}
    (hβ : IsGeneratingTrace (w (k + 1)) ⊤ β) (hH : ∀ u, 0 < u → β u ∈ H) {u : ℝ≥0} (hu : 0 < u)
    (huT : u ≤ T (k + 1)) :
    α (cumT T k + u) = fwdMapInv (Ito.rpath (catN w T k)) (cumT T k) (β u) := by
  have hJ := LoewnerConcat.isGeneratingTrace_catPath (continuous_catN hc h0 k) (catN_zero h0 k) (hc (k + 1))
    (h0 (k + 1)) (isGeneratingTrace_catN_of_le (by omega) hα) hβ hH
  have hle : cumT T k + u ≤ cumT T (k + 1) := by rw [cumT_succ]; exact add_le_add le_rfl huT
  have e1 : α (cumT T k + u) = LP.traceAt (cumT T k + u) (catN w T n) :=
    (LP.traceAt_eq_of_isGeneratingTrace hα (continuous_catN hc h0 n).continuousOn (catN_zero h0 n)
      ENNReal.coe_lt_top).symm
  have e2 : LP.traceAt (cumT T k + u) (catN w T n) = LP.traceAt (cumT T k + u) (catN w T (k + 1)) :=
    LP.traceAt_congr fun r hr => catN_of_le_cumT hkn (hr.trans hle)
  have e3 : LP.traceAt (cumT T k + u) (catN w T (k + 1)) =
      LoewnerConcat.joinedTrace (catN w T k) α (cumT T k) β (cumT T k + u) :=
    LP.traceAt_eq_of_isGeneratingTrace hJ (continuous_catN hc h0 (k + 1)).continuousOn (catN_zero h0 (k + 1))
      ENNReal.coe_lt_top
  rw [e1, e2, e3, Sec7.StripWall.joinedTrace_of_lt (continuous_catN hc h0 k) (catN_zero h0 k) hH
    (lt_add_of_pos_right _ hu), add_tsub_cancel_left]

/-- **The inverse of the recentred chart of the concatenation** (root `0`) is the centred inverse Loewner map. -/
theorem catChartN_inv_eq (k : ℕ) (y : ℂ) :
    (catChartN 0 w T k).2.1 y = fwdMapInv (Ito.rpath (catN w T k)) (cumT T k) y := by
  change fwdMapInv (Ito.rpath (catN w T k)) (cumT T k) y + ((0 : ℝ) : ℂ) = _
  rw [Complex.ofReal_zero, add_zero]

/-- **The domain of the recentred chart of the concatenation is a component of `ℍ ∖ α([0, cumT T k])`**, for every
generating trace `α` (on `[0, ∞)`) of a continuous driver `V` that agrees with the concatenation through `k` up to
`cumT T k`. -/
theorem dom_catChartN_eq (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) (k : ℕ) {V : ℝ≥0 → ℝ}
    (hV : Continuous V) (hVk : ∀ t ≤ cumT T k, V t = catN w T k t) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace V ⊤ α) :
    ∃ z₀, ((catChartN 0 w T k).dom : Set ℂ) = connectedComponentIn (H \ α '' Icc 0 (cumT T k)) z₀ := by
  have hW := continuous_rpath_of (continuous_catN (T := T) hc h0 k)
  have hW0 := rpath_zero_of_zero (catN_zero (T := T) h0 k)
  obtain ⟨⟨z₀, -, hcomp⟩, -⟩ := hα.2.2 (cumT T k) ENNReal.coe_lt_top
  have hK : fwdHull (fun s : ℝ => V s.toNNReal) (cumT T k) = fwdHull (Ito.rpath (catN w T k)) (cumT T k) :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hV.comp continuous_real_toNNReal) hW (cumT T k).coe_nonneg
      fun r hr => hVk _ (Real.toNNReal_le_iff_le_coe.2 hr.2)
  refine ⟨z₀, ?_⟩
  ext z
  rw [SetLike.mem_coe]
  unfold catChartN
  rw [mem_dom_recenter_loewner_iff 0 hW hW0 (cumT T k).coe_nonneg, Complex.ofReal_zero, sub_zero,
    mem_dom_loewner_iff_mem_diff_hull hW hW0 (cumT T k).coe_nonneg, ← hK, ← hcomp]

/-- **The frontier of the chart's domain lies on the trace**: a point of `ℍ` in the closure of the domain of the
recentred chart of the concatenation through `k` but outside it lies on `α([0, cumT T k])`. -/
theorem frontier_catChartN (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) (k : ℕ) {V : ℝ≥0 → ℝ}
    (hV : Continuous V) (hVk : ∀ t ≤ cumT T k, V t = catN w T k t) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace V ⊤ α) :
    ∀ z ∈ H, z ∈ closure ((catChartN 0 w T k).dom : Set ℂ) → z ∉ (catChartN 0 w T k).dom →
      z ∈ α '' Icc 0 (cumT T k) := by
  obtain ⟨z₀, hdom⟩ := dom_catChartN_eq hc h0 k hV hVk hα
  have hK : IsCompact (α '' Icc 0 (cumT T k)) :=
    isCompact_Icc.image_of_continuousOn (hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  exact Restart.StagedEntrance.mem_of_mem_closure_dom hK.isClosed hdom

end Cat

end InteractingSLE.Sec5.CrossCond.StagedGlue

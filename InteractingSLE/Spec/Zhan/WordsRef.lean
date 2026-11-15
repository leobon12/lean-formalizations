/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsCode
import InteractingSLE.Spec.Zhan.SeparatedGroups
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Spec.Zhan.Aux7
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# The reference word: all weights moved onto the outermost marks

Packet PROVE-ZHAN-B4. The reference of the whole-tail comparison (Astra §3, "Chordal transience for an arbitrary
finite word", L1585–L1615: "delete only the exponentially decaying … coth errors, adding those finite … weights to
the … endpoint. The reference, mapped back, is the original … word with one … group of weight `S` at the original
outermost mark") keeps the positions of the word and moves every weight of a side onto its outermost mark
(`outerW`). For `0 < κ ≤ 4` this word is admissible (the moved inner marks have weight `0 ≥ κ/2 − 2`), and an
evolution of it is, after relabelling every mark of a side as its outermost mark, an evolution of the two-group word
of PROVE-ZHAN-B3 (`IsIntegratedSLEEvolution.relabelOuter`). Hence:

* `IsIntegratedSLEEvolution.ae_traceEvent_outerW`: every evolution of the reference word has, almost surely,
  infinite lifetime and a transient continuous generating trace;
* `codeLaw_outerW_lifetime`, `codeLaw_outerW_lateSet_tendsto_zero`: the canonical-law inputs of the whole-tail
  comparison (`ae_tendsto_of_changeEnergy`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

variable {n nL nR : ℕ}

/-- The last index `n − 1` of `Fin n`, for `n > 0` (witnessed by any index). -/
def lastOf (i : Fin n) : Fin n := ⟨n - 1, Nat.sub_lt (Fin.pos i) Nat.one_pos⟩

theorem lastOf_eq (i j : Fin n) : lastOf i = lastOf j := rfl

theorem le_lastOf (i : Fin n) : i ≤ lastOf i := Fin.le_def.2 (by simp only [lastOf]; omega)

theorem eq_lastOf_iff {i : Fin n} : i = lastOf i ↔ (i : ℕ) + 1 = n := by
  rw [Fin.ext_iff]; simp only [lastOf]; omega

/-- Every weight of a side moved onto its outermost (last) mark. -/
def outerW (ρ : Fin n → ℝ) : Fin n → ℝ := fun i => if (i : ℕ) + 1 = n then ∑ j, ρ j else 0

/-- Every position of a side moved to its outermost (last) position. -/
def outerPos (x : Fin n → ℝ) : Fin n → ℝ := fun i => x (lastOf i)

theorem outerW_of_ne {ρ : Fin n → ℝ} {i : Fin n} (hi : i ≠ lastOf i) : outerW ρ i = 0 := by
  simp only [outerW, ite_eq_right_iff]
  exact fun h => absurd (eq_lastOf_iff.2 h) hi

theorem sum_outerW (ρ : Fin n → ℝ) : ∑ i, outerW ρ i = ∑ i, ρ i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_eq_single ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩]
    · simp only [outerW, ite_eq_left_iff]
      intro h; exact absurd (by omega) h
    · intro i _ hi
      exact outerW_of_ne fun h => hi (h.trans rfl)
    · intro h; exact absurd (Finset.mem_univ _) h

/-- With weights on the outermost marks only, the drift of mark `i` is that of the outermost mark. -/
theorem outerW_div_eq {ρ : Fin n → ℝ} (i : Fin n) (f : Fin n → ℝ) :
    outerW ρ i / f i = outerW ρ i / f (lastOf i) := by
  by_cases hi : i = lastOf i
  · rw [← hi]
  · rw [outerW_of_ne hi, zero_div, zero_div]

/-- The threshold condition never holds for a word whose marks coincide on each side and whose side totals exceed
`−2`. -/
theorem not_thresholdCondition_of_const {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hSL : -2 < ∑ i, ρL i)
    (hSR : -2 < ∑ i, ρR i) (w : ℝ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (hL : ∀ i j, vL i = vL j)
    (hR : ∀ i j, vR i = vR j) : ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  unfold ForceWord.ThresholdCondition
  push Not
  constructor
  · by_cases h : ∃ i, vL i = w
    · obtain ⟨i, hi⟩ := h
      rw [Finset.filter_true_of_mem fun k _ => (hL k i).trans hi]
      exact hSL
    · push Not at h
      rw [Finset.filter_false_of_mem fun k _ => h k, Finset.sum_empty]
      norm_num
  · by_cases h : ∃ i, vR i = w
    · obtain ⟨i, hi⟩ := h
      rw [Finset.filter_true_of_mem fun k _ => (hR k i).trans hi]
      exact hSR
    · push Not at h
      rw [Finset.filter_false_of_mem fun k _ => h k, Finset.sum_empty]
      norm_num

/-! ### Relabelling every mark of a side as its outermost mark -/

/-- **Relabelling, pathwise.** A path of a word whose weights sit on the outermost marks only, with infinite
lifetime and total side weights `> −2`, is a path of the two-group word at the outermost positions. -/
theorem IsIntegratedSLEPath.relabelOuter {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (h : IsIntegratedSLEPath a xL xR (outerW ρL) (outerW ρR) w vL vR b ⊤) (hSL : -2 < ∑ i, ρL i)
    (hSR : -2 < ∑ i, ρR i) :
    IsIntegratedSLEPath a (outerPos xL) (outerPos xR) (outerW ρL) (outerW ρR) w
      (fun i => vL (lastOf i)) (fun j => vR (lastOf j)) b ⊤ := by
  obtain ⟨h0, hL0, hR0, hcw, hcL, hcR, -, hLw, hwR, -, hiL, hiR, hweq, hLeq, hReq, hcolL, hcolR, -, -, -⟩ := h
  have hsL : ∀ t : ℝ≥0, (∑ i, ∫ s in (0 : ℝ)..t, outerW ρL i / (w s.toNNReal - vL i s.toNNReal)) =
      ∑ i, ∫ s in (0 : ℝ)..t, outerW ρL i / (w s.toNNReal - vL (lastOf i) s.toNNReal) := fun t =>
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s _ =>
      outerW_div_eq i (fun k => w s.toNNReal - vL k s.toNNReal)
  have hsR : ∀ t : ℝ≥0, (∑ i, ∫ s in (0 : ℝ)..t, outerW ρR i / (w s.toNNReal - vR i s.toNNReal)) =
      ∑ i, ∫ s in (0 : ℝ)..t, outerW ρR i / (w s.toNNReal - vR (lastOf i) s.toNNReal) := fun t =>
    Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s _ =>
      outerW_div_eq i (fun k => w s.toNNReal - vR k s.toNNReal)
  refine ⟨h0, fun i => hL0 _, fun j => hR0 _, hcw, fun i => hcL _, fun j => hcR _,
    fun _ _ _ _ _ => le_of_eq rfl, fun t ht i => hLw t ht _, fun t ht j => hwR t ht _,
    fun _ _ _ _ _ => le_of_eq rfl, fun t ht i => hiL t ht _, fun t ht j => hiR t ht _,
    fun t ht => by rw [hweq t ht, hsL t, hsR t], fun t ht i => hLeq t ht _, fun t ht j => hReq t ht _,
    fun i => hcolL _, fun j => hcolR _,
    fun t _ => not_thresholdCondition_of_const (by rwa [sum_outerW]) (by rwa [sum_outerW]) _
      (fun _ _ => rfl) (fun _ _ => rfl),
    fun h => absurd h ENNReal.top_ne_zero, fun T _ hT => absurd hT ENNReal.coe_ne_top⟩

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Relabelling an evolution** whose weights sit on the outermost marks (infinite lifetime almost surely). -/
theorem IsIntegratedSLEEvolution.relabelOuter
    (hE : IsIntegratedSLEEvolution κ xL xR (outerW ρL) (outerW ρR) P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hSL : -2 < ∑ i, ρL i) (hSR : -2 < ∑ i, ρR i) :
    IsIntegratedSLEEvolution κ (outerPos xL) (outerPos xR) (outerW ρL) (outerW ρR) P 𝓕 W
      (fun i => VL (lastOf i)) (fun j => VR (lastOf j)) B ζ := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  refine ⟨hB, hW, fun i => hVL _, fun j => hVR _, ?_⟩
  filter_upwards [hpath, hζ] with ω hp hζω
  rw [hζω] at hp ⊢
  exact Zhan.IsIntegratedSLEPath.relabelOuter hp hSL hSR

/-! ### Admissibility -/

theorem isOrderedForceWord_outerPos (hF : IsOrderedForceWord xL xR) :
    IsOrderedForceWord (outerPos xL) (outerPos xR) :=
  ⟨fun _ _ _ => le_of_eq rfl, fun _ => hF.2.1 _, fun _ _ _ => le_of_eq rfl, fun _ => hF.2.2.2 _⟩

/-- The whole left side lies right of `x` when the outermost left mark does. -/
theorem filter_lt_eq_univ (hF : IsOrderedForceWord xL xR) {x : ℝ} {i : Fin nL} (hx : x < xL (lastOf i)) :
    (Finset.univ.filter fun k => x < xL k) = Finset.univ := by
  refine Finset.filter_true_of_mem fun k _ => lt_of_lt_of_le hx ?_
  rw [lastOf_eq i k]
  exact hF.1 (le_lastOf k)

/-- The whole right side lies left of `x` when the outermost right mark does. -/
theorem filter_le_eq_univ (hF : IsOrderedForceWord xL xR) {x : ℝ} {j : Fin nR} (hx : xR (lastOf j) ≤ x) :
    (Finset.univ.filter fun k => xR k ≤ x) = Finset.univ := by
  refine Finset.filter_true_of_mem fun k _ => le_trans ?_ hx
  rw [lastOf_eq j k]
  exact hF.2.2.1 (le_lastOf k)

/-- The whole left weight is admissible. -/
theorem le_sum_left (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (i : Fin nL) : κ / 2 - 2 ≤ ∑ k, ρL k := by
  have hx : xL (lastOf i) - 1 < xL (lastOf i) := by linarith
  have h := hadm.1 (xL (lastOf i) - 1) (by linarith [hxL (lastOf i)]) ⟨lastOf i, hx⟩
  rwa [filter_lt_eq_univ hF hx] at h

/-- The whole right weight is admissible. -/
theorem le_sum_right (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxR : ∀ j, 0 < xR j) (j : Fin nR) : κ / 2 - 2 ≤ ∑ k, ρR k := by
  have h := hadm.2 (xR (lastOf j)) (hxR _).le ⟨lastOf j, le_rfl⟩
  rwa [filter_le_eq_univ hF le_rfl] at h

theorem neg_two_lt_sum_left (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) : -2 < ∑ k, ρL k := by
  rcases Nat.eq_zero_or_pos nL with h0 | hn
  · subst h0; simp
  · linarith [le_sum_left hF hadm hxL ⟨0, hn⟩]

theorem neg_two_lt_sum_right (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxR : ∀ j, 0 < xR j) : -2 < ∑ k, ρR k := by
  rcases Nat.eq_zero_or_pos nR with h0 | hn
  · subst h0; simp
  · linarith [le_sum_right hF hadm hxR ⟨0, hn⟩]

/-- **The reference word is admissible for `κ ≤ 4`**: its inner marks have weight `0 ≥ κ/2 − 2`. -/
theorem hasAdmissiblePartialSums_outerW (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) :
    Sec4.HasAdmissiblePartialSums κ (outerW ρL) (outerW ρR) xL xR := by
  have h0 : κ / 2 - 2 ≤ 0 := by linarith
  refine ⟨fun x hx ⟨i, hi⟩ => ?_, fun x hx ⟨j, hj⟩ => ?_⟩
  · by_cases hlast : x < xL (lastOf i)
    · rw [filter_lt_eq_univ hF hlast, sum_outerW]
      exact le_sum_left hF hadm hxL i
    · rw [Finset.sum_eq_zero fun k hk => outerW_of_ne fun hke => ?_]
      · exact h0
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [hke, lastOf_eq k i] at hk
        exact hlast hk
  · by_cases hlast : xR (lastOf j) ≤ x
    · rw [filter_le_eq_univ hF hlast, sum_outerW]
      exact le_sum_right hF hadm hxR j
    · rw [Finset.sum_eq_zero fun k hk => outerW_of_ne fun hke => ?_]
      · exact h0
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [hke, lastOf_eq k j] at hk
        exact hlast hk

/-! ### Transience of the reference word -/

/-- **The reference word is transient** (`0 < κ ≤ 4`): every evolution of the word with all weights moved onto the
outermost marks has, almost surely, infinite lifetime and the trace event (a continuous generating trace on
`[0, ∞)`, tending to `∞`). Relabelled, it is an evolution of a two-group word (PROVE-ZHAN-B3). -/
theorem IsIntegratedSLEEvolution.ae_traceEvent_outerW [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hn : 0 < nL + nR)
    (hE : IsIntegratedSLEEvolution κ xL xR (outerW ρL) (outerW ρR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ TraceEvent (fun t => W t ω) (ζ ω) := by
  have hadm' := hasAdmissiblePartialSums_outerW hκ4 hF hadm hxL hxR
  have h23 := hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ hF hadm' hxL hxR
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := h23.mono fun _ h => h.1
  have hE' := IsIntegratedSLEEvolution.relabelOuter hE hζ (neg_two_lt_sum_left hκ hF hadm hxL)
    (neg_two_lt_sum_right hκ hF hadm hxR)
  have hFo := isOrderedForceWord_outerPos hF
  have hadmo : Sec4.HasAdmissiblePartialSums κ (outerW ρL) (outerW ρR) (outerPos xL) (outerPos xR) :=
    hasAdmissiblePartialSums_of_ties hF hFo hadm' (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have htr := Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_groups hκ hκ4 hFo hadmo
    (fun i => hxL _) (fun j => hxR _) (fun _ _ => rfl) (fun _ _ => rfl) hn hE'
  filter_upwards [h23, htr] with ω h ht
  obtain ⟨hζω, η, hη⟩ := h
  exact ⟨hζω, η, hζω ▸ hη, fun _ => ht η hη⟩

/-- The canonical law of the reference word from the start `(xL, xR)` has infinite lifetime with probability one. -/
theorem codeLaw_outerW_lifetime (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) :
    codeLaw κ (outerW ρL) (outerW ρR) {x | cζ x = ⊤} (xL, xR) = 1 := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    Sec2.Assembly2.exists_isIntegratedSLEEvolution_of_ordered (ρL := outerW ρL) (ρR := outerW ρR) hκ hF
  have hadm' := hasAdmissiblePartialSums_outerW hκ4 hF hadm hxL hxR
  exact codeLaw_lifetime_eq_top hκ (fun i j => (hxL i).trans (hxR j)) hE'
    ((hE'.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ hF hadm' hxL hxR).mono
      fun _ h => h.1)

/-- Late returns of the canonical reference trace are rare. -/
theorem codeLaw_outerW_lateSet_tendsto_zero (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j)
    (hn : 0 < nL + nR) (R : ℝ) :
    Tendsto (fun k => codeLaw κ (outerW ρL) (outerW ρR) (lateSet k R) (xL, xR)) atTop (𝓝 0) := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    Sec2.Assembly2.exists_isIntegratedSLEEvolution_of_ordered (ρL := outerW ρL) (ρR := outerW ρR) hκ hF
  exact codeLaw_lateSet_tendsto_zero hκ (fun i j => (hxL i).trans (hxR j)) hE'
    ((IsIntegratedSLEEvolution.ae_traceEvent_outerW hκ hκ4 hF hadm hxL hxR hn hE').mono fun _ h => h.2) R

end InteractingSLE.Zhan

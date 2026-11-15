/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueChain
import InteractingSLE.Spec.Sec5.Prop59PiecesTrace

/-!
# Proposition 5.9 at depth `ℓ`: the joined staged driver is the continued driver

Packet PROVE-STAGED-DEPTH (S2, bookkeeping). Two descriptions of the driver of a staged path along a fixed schedule
are in use: PROVE-STAGED5's `StagedGlue.joinW` (the front-nested concatenation `catN` of the pieces, used by the
mean side of S2) and PROP513's `Prop513Schedule.continuedDriver` (the back-nested concatenation, used by PIECES' code
paths and by the transience of the staged trace, `continuedDriver_trace_transient`). They are the same function:

* `catPath_assoc`: concatenation of drivers is associative (the middle driver starting at `0`);
* `catN_succ_eq_catPath`: `catN` peels its first piece off;
* **`continuedDriver_eq_catN`**, **`joinW_eq_continuedDriver`**: the two concatenations agree;
* **`IsGoodSched.exists_properArc_joinW`**: when every piece of the schedule is a good path, the joined driver has a
  generating trace that is a simple proper arc.

Deterministic helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Sec5.CrossCond.StagedDepth

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue
open Theorem14.GW2Schedule (schedTime schedDelta)
open Sec7.StripSideHeightProb (catPath catPath_of_le)
open InteractingSLE.Sec5.CrossCond.Staged (catN cumT cumT_zero catN_zero)

/-! ### Concatenation is associative -/

section Assoc

/-- **Concatenation of drivers is associative** when the middle driver starts at `0`. -/
theorem catPath_assoc (a b c : ℝ≥0 → ℝ) (T₀ T₁ : ℝ≥0) (hb : b 0 = 0) :
    catPath (catPath a T₀ b) (T₀ + T₁) c = catPath a T₀ (catPath b T₁ c) := by
  funext t
  simp only [catPath]
  by_cases h0 : t ≤ T₀
  · have h1 : t ≤ T₀ + T₁ := h0.trans le_self_add
    simp only [h1, h0, ↓reduceIte]
  · by_cases h1 : t ≤ T₀ + T₁
    · have h2 : t - T₀ ≤ T₁ := tsub_le_iff_left.2 h1
      simp only [h1, h0, h2, ↓reduceIte]
    · have h2 : ¬ t - T₀ ≤ T₁ := fun h => h1 (tsub_le_iff_left.1 h)
      simp only [h1, h0, h2, ↓reduceIte, add_tsub_cancel_left, tsub_add_eq_tsub_tsub]
      by_cases hT : T₁ = 0
      · subst hT
        simp only [add_zero, le_refl, ↓reduceIte, hb]
        ring
      · have h3 : ¬ T₀ + T₁ ≤ T₀ := fun h => hT (le_antisymm (by simpa using h) (zero_le))
        simp only [h3, ↓reduceIte]
        ring

end Assoc

/-! ### `catN` peels its first piece off -/

section Peel

/-- The cumulative time after the first piece. -/
theorem cumT_succ_eq_add (T : ℕ → ℝ≥0) (k : ℕ) : cumT T (k + 1) = T 0 + cumT (fun i => T (i + 1)) k := by
  simp only [cumT]
  rw [Finset.sum_range_succ']
  ring

/-- **`catN` peels its first piece off**: the concatenation of pieces `0, …, k + 1` is the first piece followed by the
concatenation of pieces `1, …, k + 1`. -/
theorem catN_succ_eq_catPath (w : ℕ → ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) (h0 : ∀ j, w j 0 = 0) :
    ∀ k, catN w T (k + 1) = catPath (w 0) (T 0) (catN (fun i => w (i + 1)) (fun i => T (i + 1)) k)
  | 0 => by
    change catPath (catN w T 0) (cumT T 0) (w 1) = catPath (w 0) (T 0) (w (0 + 1))
    rw [cumT_zero]
    rfl
  | k + 1 => by
    change catPath (catN w T (k + 1)) (cumT T (k + 1)) (w (k + 1 + 1)) =
      catPath (w 0) (T 0) (catPath (catN (fun i => w (i + 1)) (fun i => T (i + 1)) k)
        (cumT (fun i => T (i + 1)) k) (w (k + 1 + 1)))
    rw [catN_succ_eq_catPath w T h0 k, cumT_succ_eq_add]
    exact catPath_assoc _ _ _ _ _ (catN_zero (fun i => h0 (i + 1)) k)

end Peel

/-! ### The two concatenations agree -/

section Cont

variable {Ω : Type*}

/-- `catN` only reads the pieces up to its index. -/
theorem catN_congr_le (w w' : ℕ → ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) :
    ∀ k, (∀ i ≤ k, w i = w' i) → catN w T k = catN w' T k
  | 0, h => h 0 le_rfl
  | k + 1, h => by
    change catPath (catN w T k) (cumT T k) (w (k + 1)) = catPath (catN w' T k) (cumT T k) (w' (k + 1))
    rw [catN_congr_le w w' T k fun i hi => h i (by omega), h (k + 1) le_rfl]

/-- **The continued driver is the front-nested concatenation** of its pieces, with the own times of the schedule
list (`schedDelta a l`). -/
theorem continuedDriver_eq_catN (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) (h0 : ∀ j, (E j ω).1 0 = 0) :
    ∀ (l : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0), l ≠ [] →
      continuedDriver E j a l ω =
        catN (fun i => (E (j + i) ω).1) (fun i => (schedDelta a l i).toNNReal) (l.length - 1)
  | [], _, _, hl => absurd rfl hl
  | [_], j, _, _ => rfl
  | p :: q :: l, j, a, _ => by
    have ih := continuedDriver_eq_catN E ω h0 (q :: l) (j + 1) p.2 (List.cons_ne_nil _ _)
    change catPath (E j ω).1 (p.2 - a) (continuedDriver E (j + 1) p.2 (q :: l) ω) = _
    rw [ih]
    have hlen : (p :: q :: l).length - 1 = (q :: l).length - 1 + 1 := by simp
    rw [hlen, catN_succ_eq_catPath _ _ (fun i => h0 (j + i))]
    have hw : (fun i => (E (j + (i + 1)) ω).1) = fun i => (E (j + 1 + i) ω).1 := by
      funext i; rw [Nat.add_right_comm, Nat.add_assoc]
    have hT : (fun i => (schedDelta a (p :: q :: l) (i + 1)).toNNReal) =
        fun i => (schedDelta p.2 (q :: l) i).toNNReal := by
      funext i
      cases i <;> rfl
    have hT0 : (schedDelta a (p :: q :: l) 0).toNNReal = p.2 - a := by
      simp only [schedDelta, ENNReal.toNNReal_coe]
      rfl
    simp only [Nat.add_zero] at hw hT ⊢
    rw [hw, hT, hT0]

/-- **The joined driver of a schedule is its continued driver** (pieces starting at `0`). -/
theorem joinW_eq_continuedDriver (s : Schedule) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω)
    (h0 : ∀ j, (E j ω).1 0 = 0) : joinW s E ω = continuedDriver E 0 0 (scheduleList s) ω := by
  have hne : scheduleList s ≠ [] := fun h => s.2.1 (List.map_eq_nil_iff.1 h)
  rw [continuedDriver_eq_catN E ω h0 (scheduleList s) 0 0 hne, joinW, schedL_eq]
  refine catN_congr_le _ _ _ _ (fun i hi => ?_)
  have hi' : i < schedL s := by rw [schedL_eq]; have := List.length_pos_of_ne_nil hne; omega
  simp only [pieceW_of_lt s E ω hi', Nat.zero_add]

end Cont

/-! ### The staged trace is a simple proper arc -/

section Arc

variable {Ω : Type*}

/-- The joined driver of a schedule as a process on `Ω`. -/
def joinProc (s : Schedule) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ≥0 → Ω → ℝ := fun t ω => joinW s E ω t

/-- **The staged trace is a simple proper arc** when every piece of the schedule is a regular good path: the joined
driver is continuous from `0`, and the flow trace `seedLine ⊤ (joinProc s E) ω` of WangWu's image word is a proper arc
and a Loewner trace of the joined driver. -/
theorem properArc_seedLine_joinProc (s : Schedule) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}
    (hreg : ∀ j, IsRegularDriver (E j ω)) (hg : ∀ k < schedL s, E k ω ∈ Sec7.StripWall.goodPathSet) :
    Continuous (joinW s E ω) ∧ joinW s E ω 0 = 0 ∧
      WangWu.IsProperArc (WangWu.seedLine (fun _ => ⊤) (joinProc s E) ω) ∧
      IsLoewnerTrace (fun r : ℝ => joinW s E ω r.toNNReal) (WangWu.seedLine (fun _ => ⊤) (joinProc s E) ω) := by
  have hne : scheduleList s ≠ [] := fun h => s.2.1 (List.map_eq_nil_iff.1 h)
  have h0 : ∀ j, (E j ω).1 0 = 0 := fun j => (hreg j).2.1
  have hgp : ∀ i, 0 ≤ i → i < 0 + (scheduleList s).length → Prop59Pieces.GoodPieces E ω i := fun i _ hi =>
    Prop59Pieces.goodPieces_of_mem (hreg i) (hg i (by rw [schedL_eq]; omega))
  obtain ⟨hc, hz, η, hη, hinj, hH, ht⟩ :=
    Prop59Pieces.continuedDriver_trace_transient E ω 0 0 (scheduleList s) hne hgp
  have hjw := joinW_eq_continuedDriver s E ω h0
  rw [← hjw] at hc hz hη
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  have hseq : WangWu.seedLine (fun _ => ⊤) (joinProc s E) ω = fun u : ℝ => η u.toNNReal := by
    funext u
    have hk : (fun t => InteractingSLE.killedProc (fun _ => ⊤) (joinProc s E) t ω) = joinW s E ω :=
      funext fun t => InteractingSLE.killedProc_of_eq_top (ζ := fun _ => ⊤) (X := joinProc s E) (ω := ω) rfl t
    simp only [WangWu.seedLine, hk]
    exact LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn hz ENNReal.coe_lt_top
  refine ⟨hc, hz, ?_, ?_⟩
  · rw [hseq]
    exact WangWu.isProperArc_of_injective hηc hη.1 hinj hH ht
  · rw [hseq]
    exact isLoewnerTrace_of_isGeneratingTrace hη

end Arc

end InteractingSLE.Sec5.CrossCond.StagedDepth

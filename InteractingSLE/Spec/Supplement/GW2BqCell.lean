/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BpCore

/-!
# The near exit with a record-dependent buffer, over countably many cells

Packet PROVE-GW2-BUF (round 14). Round 13 found that the exit of `nearBuffer f n` itself fires at time `0` when
`n ≤ max |label|` (the buffer's box bounds the labels too). The near exit therefore leaves a larger buffer that always
contains the initial state:

* the cell `(K, R, k)`: shape `K`, box radius `R : ℕ`, far level `(1/2)^k`;
* `cellBuf (K, R, k)`: the buffer of the shape `K` (orientation and controlled labels as `bufOfShape`) with radius
  `R` and level `(1/2)^k`.

Results:
* **`bufOfShape_subset_cellBuf`**: if `n ≤ R` and `(1/2)^k ≤ 1/(n+1)` then `bufOfShape K n ⊆ cellBuf (K, R, k)`.
  So leaving the cell buffer leaves `nearBuffer`.
* `cellStopF`, **`cellStop`**: the exit rule of the record's cell (labels padded by `0`), with `measurable_cellStop`,
  `isPathRule_cellStop` and `cellStop_eq` (it is round 7's `exitRule` at each record).
* **`exit_spec_cell`**: if the record's cell has the near family's shape and labels, contains `nearBuffer f n`, and
  contains the initial comparison state, then the exit `τ` satisfies `0 < τ ≤ c`, and for `τ < c` the image state with
  `f`'s labels at `a τ` is outside `nearBuffer f n`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach

/-- A near exit cell: a shape, a box radius and a far level index. -/
abbrev NearCell := NearShape × ℕ × ℕ

/-- **The buffer of a cell**: the shape's orientation and controlled labels, radius `R`, level `(1/2)^k`. -/
def cellBuf (K : NearCell) : Set (ℝ × (Fin K.1.1 → ℝ) × (Fin K.1.2.1 → ℝ)) :=
  if K.1.2.2.2.2 then {p | InBuffer K.1.2.2.1 (K.1.2.1 - 1) (K.2.1 : ℝ) ((1 / 2 : ℝ) ^ K.2.2) p}
  else {p | InBuffer (K.1.1 - 1) K.1.2.2.2.1 (K.2.1 : ℝ) ((1 / 2 : ℝ) ^ K.2.2) p}

theorem inBuffer_mono {nL nR : ℕ} {mL mR : ℕ} {R R' g g' : ℝ} (hR : R ≤ R') (hg : g' ≤ g)
    {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (h : InBuffer mL mR R g p) : InBuffer mL mR R' g' p :=
  ⟨⟨lt_of_lt_of_le h.1.1 hR, fun i => lt_of_lt_of_le (h.1.2.1 i) hR, fun j => lt_of_lt_of_le (h.1.2.2 j) hR⟩,
    fun j hj => lt_of_le_of_lt hg (h.2.1 j hj), fun i hi => lt_of_le_of_lt hg (h.2.2 i hi)⟩

/-- **Leaving the cell buffer leaves the near buffer.** -/
theorem bufOfShape_subset_cellBuf (K : NearShape) {n R k : ℕ} (hR : n ≤ R)
    (hk : (1 / 2 : ℝ) ^ k ≤ 1 / ((n : ℝ) + 1)) : bufOfShape K n ⊆ cellBuf (K, R, k) := by
  intro p hp
  unfold bufOfShape at hp
  unfold cellBuf
  have hR' : (n : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  split_ifs at hp ⊢ with h
  · exact inBuffer_mono hR' hk hp
  · exact inBuffer_mono hR' hk hp

theorem isOpen_cellBuf (K : NearCell) : IsOpen (cellBuf K) := by
  unfold cellBuf
  split_ifs
  · exact isOpen_setOf_inBuffer _ _ _ _
  · exact isOpen_setOf_inBuffer _ _ _ _

theorem compl_cellBuf_nonempty (K : NearCell) : (cellBuf K)ᶜ.Nonempty := by
  refine ⟨(((K.2.1 : ℕ) : ℝ) + 1, fun _ => 0, fun _ => 0), fun h => ?_⟩
  have hbox : |((K.2.1 : ℕ) : ℝ) + 1| < (K.2.1 : ℝ) := by
    unfold cellBuf at h
    split_ifs at h
    · exact h.1.1
    · exact h.1.1
  rw [abs_of_pos (by positivity)] at hbox
  linarith

/-! ### The exit over cells -/

/-- The near exit at a given cell, uncurried. -/
def cellStopF (posL posR : RecData → ℕ → ℝ) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0)
    (q : (RecData × (ℝ≥0 → ℝ)) × NearCell) : ℝ≥0∞ :=
  exitRuleRec (nL := q.2.1.1) (nR := q.2.1.2.1) (fun r i => posL r i) (fun r j => posR r j) (cellBuf q.2) a b c q.1

/-- **The near exit of the record's cell.** -/
def cellStop (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) :
    RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
  fun p => cellStopF posL posR a b c (p, cell p.1)

theorem measurable_cellStopF {posL posR : RecData → ℕ → ℝ} (hL : Measurable posL) (hR : Measurable posR)
    (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) : Measurable (cellStopF posL posR a b c) := by
  refine measurable_from_prod_countable_left fun K => ?_
  show Measurable (exitRuleRec (nL := K.1.1) (nR := K.1.2.1) (fun r i => posL r i) (fun r j => posR r j)
    (cellBuf K) a b c)
  exact measurable_exitRuleRec (measurable_pi_iff.2 fun i => (measurable_pi_apply (i : ℕ)).comp hL)
    (measurable_pi_iff.2 fun j => (measurable_pi_apply (j : ℕ)).comp hR) (cellBuf K) a b c

theorem measurable_cellStop {cell : RecData → NearCell} (hcell : Measurable cell) {posL posR : RecData → ℕ → ℝ}
    (hL : Measurable posL) (hR : Measurable posR) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) :
    Measurable (cellStop cell posL posR a b c) :=
  (measurable_cellStopF hL hR a b c).comp (measurable_id.prodMk (hcell.comp measurable_fst))

theorem isPathRule_cellStop (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ) {a : ℝ≥0} (ha : 0 < a)
    (b : ℝ) (c : ℝ≥0) : IsPathRule (cellStop cell posL posR a b c) := fun r w w' h =>
  isPathRule_exitRuleRec (nL := (cell r).1.1) (nR := (cell r).1.2.1) (fun r i => posL r i) (fun r j => posR r j)
    (cellBuf (cell r)) ha b c r w w' h

theorem cellStop_eq (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ) (a : ℝ≥0) (b : ℝ) (c : ℝ≥0)
    (r : RecData) (w : ℝ≥0 → ℝ) :
    cellStop cell posL posR a b c (r, w) =
      exitRule (fun i : Fin (cell r).1.1 => posL r i) (fun j : Fin (cell r).1.2.1 => posR r j) (cellBuf (cell r))
        a b c (r, w) :=
  exitRuleRec_eq _ _ _ a b c r w

/-- **Transport across a shape equality for cell buffers.** -/
theorem imgState_mem_cellBuf_transport {K K' : NearShape} (h : K = K') (R k : ℕ) (L : Fin K.1 → ℝ)
    (Rt : Fin K.2.1 → ℝ) (L' : Fin K'.1 → ℝ) (R' : Fin K'.2.1 → ℝ)
    (hL : ∀ i : Fin K.1, L i = L' (Fin.cast (congrArg (fun K : NearShape => K.1) h) i))
    (hR : ∀ j : Fin K.2.1, Rt j = R' (Fin.cast (congrArg (fun K : NearShape => K.2.1) h) j))
    (w : ℝ≥0 → ℝ) (t : ℝ≥0) :
    GW2Sdg.imgState L Rt w t ∈ cellBuf (K, R, k) ↔ GW2Sdg.imgState L' R' w t ∈ cellBuf (K', R, k) := by
  subst h
  have e1 : L = L' := funext fun i => by rw [hL i]; rfl
  have e2 : Rt = R' := funext fun j => by rw [hR j]; rfl
  rw [e1, e2]

/-- **The exit of the record's cell, for the near family.** -/
theorem exit_spec_cell {κ : ℝ} (f : NearCrossingFamily.{u} κ) (n : ℕ) (cell : RecData → NearCell)
    (posL posR : RecData → ℕ → ℝ) (y : RecData) (hsh : famShapeB f = (cell y).1)
    (hL : ∀ i : Fin f.nL, f.xL i = posL y i) (hR : ∀ j : Fin f.nR, f.xR j = posR y j)
    (hsub : bufOfShape (famShapeB f) n ⊆ cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    (a : ℝ≥0) (b : ℝ) {c : ℝ≥0} (hc : 0 < c) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath a b w) 0 ∈ cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2)) :
    ∃ τ : ℝ≥0, cellStop cell posL posR a b c (y, w) = τ ∧ 0 < τ ∧ τ ≤ c ∧
      (τ < c → GW2Sdg.imgState f.xL f.xR (scaledPath a b w) (a * τ) ∉ nearBuffer f n) := by
  set K := cell y with hK
  have hKeq : K = ((cell y).1, (cell y).2.1, (cell y).2.2) := rfl
  have htr : ∀ t : ℝ≥0, (GW2Sdg.imgState (fun i : Fin K.1.1 => posL y i) (fun j : Fin K.1.2.1 => posR y j)
      (scaledPath a b w) t ∈ cellBuf K ↔
      GW2Sdg.imgState f.xL f.xR (scaledPath a b w) t ∈ cellBuf (famShapeB f, K.2.1, K.2.2)) := fun t => by
    refine imgState_mem_cellBuf_transport hsh.symm K.2.1 K.2.2 _ _ f.xL f.xR (fun i => ?_) (fun j => ?_) _ t
    · have hn : f.nL = K.1.1 := congrArg (fun K : NearShape => K.1) hsh
      exact (hL ⟨(i : ℕ), by rw [hn]; exact i.2⟩).symm
    · have hn : f.nR = K.1.2.1 := congrArg (fun K : NearShape => K.2.1) hsh
      exact (hR ⟨(j : ℕ), by rw [hn]; exact j.2⟩).symm
  obtain ⟨τ, hτ, hτ0, hτc, hout⟩ := exitRule_spec (fun i : Fin K.1.1 => posL y i)
    (fun j : Fin K.1.2.1 => posR y j) (isOpen_cellBuf K) (compl_cellBuf_nonempty K) a b hc y hw ((htr 0).2 h0)
  refine ⟨τ, ?_, hτ0, hτc, fun hlt hin => hout hlt ((htr _).2 (hsub ?_))⟩
  · rw [cellStop_eq]
    exact hτ
  · rw [← nearBuffer_eq_bufOfShape]
    exact hin

end InteractingSLE.Theorem14.GW2Bh

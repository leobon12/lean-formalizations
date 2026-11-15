/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalCarrier
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The initial code of an A-stopped model: the word and two chart segments

Packet PROVE-T15-ASTOP2. Theorem 1.5's leaf 3 stops a retained continuation at its first new contact with the retained
union `A = η₁[0,u] ∪ η₂[0,r]` only (Lemma G7, supplement p. 497). In the retained chart the part of the boundary that
belongs to `A` is a union of at most two closed real segments (one per prefix; one segment when the two hulls touch),
`I_A`, and the A-stop is the first positive time at which the chart path meets `I_A` (or the continuation's original
end). PROVE-T15-ASTOP's stopped K2 allows the announcing stops to read a real code known at time `0`
(`OrdAStop.drivingSupCode`); this file fixes that code:

* `aStopSet q`: the union of the two segments with end points `q = (a₁, b₁, a₂, b₂)` (always nonempty and compact,
  whatever the order of the end points); `lipschitzWith_infDist_aStopSet`: `(z, q) ↦ dist(z, aStopSet q)` is
  `2`-Lipschitz (through the Hausdorff distance), hence measurable;
* `CodeSpace = BoundaryWord × Ends` and a Borel isomorphism `codeEquiv : CodeSpace ≃ᵐ ℝ` (Borel isomorphism theorem);
  the word is in the code so that the force positions of the word are known to the enlarged filtration at time `0`;
* `codeJ c = aStopSet (codeEquiv.symm c).2`, `codeWord c = (codeEquiv.symm c).1`, with `isClosed_codeJ`,
  `measurable_infDist_codeJ` (exactly the hypotheses of `OrdAStop.exists_isAnnouncingSeq_aStop`) and the decoding
  identities `codeJ_codeEquiv`, `codeWord_codeEquiv`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdModel

open Restart

/-! ### Two chart segments -/

/-- The four chart end points `(a₁, b₁, a₂, b₂)` of the two segments of the A-set. -/
abbrev Ends : Type := ℝ × ℝ × ℝ × ℝ

/-- The point of the segment from `a` to `b` with parameter `x`. -/
def segPt (a b x : ℝ) : ℂ := ((a + x * (b - a) : ℝ) : ℂ)

/-- The real segment from `a` to `b`, as a subset of `ℂ` (parametrised over `[0, 1]`). -/
def seg (a b : ℝ) : Set ℂ := segPt a b '' Icc 0 1

/-- **The A-set coded by four end points**: the union of the real segments `[a₁, b₁]` and `[a₂, b₂]`. -/
def aStopSet (q : Ends) : Set ℂ := seg q.1 q.2.1 ∪ seg q.2.2.1 q.2.2.2

theorem continuous_segPt (a b : ℝ) : Continuous (segPt a b) :=
  Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.mul continuous_const))

theorem isCompact_seg (a b : ℝ) : IsCompact (seg a b) := isCompact_Icc.image (continuous_segPt a b)

theorem seg_nonempty (a b : ℝ) : (seg a b).Nonempty :=
  ⟨_, mem_image_of_mem _ (left_mem_Icc.2 zero_le_one)⟩

theorem isCompact_aStopSet (q : Ends) : IsCompact (aStopSet q) :=
  (isCompact_seg _ _).union (isCompact_seg _ _)

theorem isClosed_aStopSet (q : Ends) : IsClosed (aStopSet q) := (isCompact_aStopSet q).isClosed

theorem aStopSet_nonempty (q : Ends) : (aStopSet q).Nonempty := (seg_nonempty _ _).mono subset_union_left

/-- Points with the same parameter on two segments are within the larger end-point displacement. -/
theorem dist_segPt_le (a b a' b' : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    dist (segPt a b x) (segPt a' b' x) ≤ max |a - a'| |b - b'| := by
  rw [segPt, segPt, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
  have e : a + x * (b - a) - (a' + x * (b' - a')) = (1 - x) * (a - a') + x * (b - b') := by ring
  have h1 : 0 ≤ 1 - x := sub_nonneg.2 hx.2
  rw [e]
  calc |(1 - x) * (a - a') + x * (b - b')| ≤ |(1 - x) * (a - a')| + |x * (b - b')| := abs_add_le _ _
    _ = (1 - x) * |a - a'| + x * |b - b'| := by rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg hx.1]
    _ ≤ (1 - x) * max |a - a'| |b - b'| + x * max |a - a'| |b - b'| := by
      gcongr
      · exact le_max_left _ _
      · exact hx.1
      · exact le_max_right _ _
    _ = max |a - a'| |b - b'| := by ring

theorem abs_sub_le_dist_ends₁ (q q' : Ends) : |q.1 - q'.1| ≤ dist q q' := by
  rw [← Real.dist_eq, Prod.dist_eq]
  exact le_max_left _ _

theorem abs_sub_le_dist_ends₂ (q q' : Ends) : |q.2.1 - q'.2.1| ≤ dist q q' := by
  rw [← Real.dist_eq, Prod.dist_eq, Prod.dist_eq]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem abs_sub_le_dist_ends₃ (q q' : Ends) : |q.2.2.1 - q'.2.2.1| ≤ dist q q' := by
  rw [← Real.dist_eq, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem abs_sub_le_dist_ends₄ (q q' : Ends) : |q.2.2.2 - q'.2.2.2| ≤ dist q q' := by
  rw [← Real.dist_eq, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
  exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

/-- Every point of `aStopSet q` has a point of `aStopSet q'` within `dist q q'`. -/
theorem exists_mem_aStopSet_dist_le (q q' : Ends) {z : ℂ} (hz : z ∈ aStopSet q) :
    ∃ y ∈ aStopSet q', dist z y ≤ dist q q' := by
  rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · refine ⟨segPt q'.1 q'.2.1 x, Or.inl (mem_image_of_mem _ hx), ?_⟩
    exact (dist_segPt_le _ _ _ _ hx).trans (max_le (abs_sub_le_dist_ends₁ q q') (abs_sub_le_dist_ends₂ q q'))
  · refine ⟨segPt q'.2.2.1 q'.2.2.2 x, Or.inr (mem_image_of_mem _ hx), ?_⟩
    exact (dist_segPt_le _ _ _ _ hx).trans (max_le (abs_sub_le_dist_ends₃ q q') (abs_sub_le_dist_ends₄ q q'))

/-- The Hausdorff distance between two coded A-sets is at most the distance of the codes. -/
theorem hausdorffDist_aStopSet_le (q q' : Ends) : hausdorffDist (aStopSet q) (aStopSet q') ≤ dist q q' :=
  hausdorffDist_le_of_mem_dist dist_nonneg (fun _ hz => exists_mem_aStopSet_dist_le q q' hz)
    (fun _ hz => by
      obtain ⟨y, hy, hd⟩ := exists_mem_aStopSet_dist_le q' q hz
      exact ⟨y, hy, hd.trans (dist_comm q' q).le⟩)

theorem hausdorffEDist_aStopSet_ne_top (q q' : Ends) : hausdorffEDist (aStopSet q) (aStopSet q') ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded (aStopSet_nonempty q) (aStopSet_nonempty q')
    (isCompact_aStopSet q).isBounded (isCompact_aStopSet q').isBounded

/-- **The distance to the coded A-set is `2`-Lipschitz in the point and the code.** -/
theorem lipschitzWith_infDist_aStopSet : LipschitzWith 2 fun p : ℂ × Ends => infDist p.1 (aStopSet p.2) := by
  refine LipschitzWith.of_dist_le_mul fun p p' => ?_
  obtain ⟨z, q⟩ := p
  obtain ⟨z', q'⟩ := p'
  have h1 : |infDist z (aStopSet q) - infDist z' (aStopSet q)| ≤ dist z z' := by
    rw [abs_sub_le_iff]
    constructor
    · linarith [infDist_le_infDist_add_dist (x := z) (y := z') (s := aStopSet q)]
    · linarith [infDist_le_infDist_add_dist (x := z') (y := z) (s := aStopSet q), dist_comm z z']
  have h2 : |infDist z' (aStopSet q) - infDist z' (aStopSet q')| ≤ dist q q' := by
    rw [abs_sub_le_iff]
    have ha := infDist_le_infDist_add_hausdorffDist (x := z') (hausdorffEDist_aStopSet_ne_top q' q)
    have hb := infDist_le_infDist_add_hausdorffDist (x := z') (hausdorffEDist_aStopSet_ne_top q q')
    have hc := hausdorffDist_aStopSet_le q q'
    have hd := hausdorffDist_aStopSet_le q' q
    rw [dist_comm q' q] at hd
    constructor <;> linarith
  have hz : dist z z' ≤ dist (z, q) (z', q') := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hq : dist q q' ≤ dist (z, q) (z', q') := by rw [Prod.dist_eq]; exact le_max_right _ _
  rw [Real.dist_eq]
  calc |infDist z (aStopSet q) - infDist z' (aStopSet q')|
      ≤ |infDist z (aStopSet q) - infDist z' (aStopSet q)| +
          |infDist z' (aStopSet q) - infDist z' (aStopSet q')| := abs_sub_le _ _ _
    _ ≤ dist (z, q) (z', q') + dist (z, q) (z', q') := add_le_add (h1.trans hz) (h2.trans hq)
    _ = ((2 : ℝ≥0) : ℝ) * dist (z, q) (z', q') := by push_cast; ring

theorem continuous_infDist_aStopSet : Continuous fun p : ℂ × Ends => infDist p.1 (aStopSet p.2) :=
  lipschitzWith_infDist_aStopSet.continuous

/-! ### The code -/

/-- The data read by the code: the word and the four end points. -/
abbrev CodeSpace : Type := BoundaryWord × Ends

instance : StandardBorelSpace CodeSpace := StandardBorelSpace.prod

theorem not_countable_codeSpace : ¬Countable CodeSpace := not_countable_iff.2 inferInstance

/-- **The code**: a Borel isomorphism of the code space with `ℝ` (Borel isomorphism theorem). -/
def codeEquiv : CodeSpace ≃ᵐ ℝ :=
  PolishSpace.measurableEquivOfNotCountable not_countable_codeSpace (not_countable_iff.2 inferInstance)

/-- The A-set decoded from a code. -/
def codeJ (c : ℝ) : Set ℂ := aStopSet (codeEquiv.symm c).2

/-- The word decoded from a code. -/
def codeWord (c : ℝ) : BoundaryWord := (codeEquiv.symm c).1

theorem codeJ_codeEquiv (w : BoundaryWord) (q : Ends) : codeJ (codeEquiv (w, q)) = aStopSet q := by
  simp only [codeJ, MeasurableEquiv.symm_apply_apply]

theorem codeWord_codeEquiv (w : BoundaryWord) (q : Ends) : codeWord (codeEquiv (w, q)) = w := by
  simp only [codeWord, MeasurableEquiv.symm_apply_apply]

theorem isClosed_codeJ (c : ℝ) : IsClosed (codeJ c) := isClosed_aStopSet _

theorem measurable_codeWord : Measurable codeWord := measurable_fst.comp codeEquiv.symm.measurable

/-- **The distance to the decoded A-set is jointly measurable** (the hypothesis of
`OrdAStop.exists_isAnnouncingSeq_aStop`). -/
theorem measurable_infDist_codeJ : Measurable fun p : ℂ × ℝ => infDist p.1 (codeJ p.2) := by
  have hr : Measurable fun p : ℂ × ℝ => (p.1, (codeEquiv.symm p.2).2) :=
    measurable_fst.prodMk (measurable_snd.comp (codeEquiv.symm.measurable.comp measurable_snd))
  have h := continuous_infDist_aStopSet.measurable.comp hr
  exact h

end InteractingSLE.RLC.OrdModel

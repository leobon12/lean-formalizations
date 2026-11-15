/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactBdryChart
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Spec.Dimension.ForceGaps
import InteractingSLE.Spec.Sec2.MartingaleFinalImage

/-!
# Aux. 79 at the later first-contact lines: the real flow of the force data

Packet PROVE-FCAUX79. Generic facts on the centred real Loewner flow of a continuous driver `w` and the flowed force
datum `forceBoundaryData κ ρL ρR (V̂^L_t) (V̂^R_t)` with the geometric images `V̂^R_t = rightImg w (x^R) t − w_t`,
`V̂^L_t = −rightImg (−w) (−x^L) t − w_t`:

* right of the image of `0⁺` (left of the image of `0⁻`) the flowed datum at `g_t(x) − w_t` is the initial datum at
  `x` (`forceBoundaryData_flow_right`, `_left`); between the two images it is `±λ` (`forceBoundaryData_flow_slit_*`);
* every value above the image of `0⁺` is the image of an alive point (`exists_alive_gImg_eq`, and its mirror);
* forward solutions from real points are the real flows (`isForwardSol_real_cases`, `isForwardSol_of_isPosSol`).

**Provenance.** `gImg_lt_gImg`, `rightImg_le_gImg_iff`, `exists_alive_gImg_eq`, `isForwardSol_real_cases` and the four
`forceBoundaryData_flow_*` lemmas are copies of the same-named lemmas of PROVE-RETAUX79B's in-flight
`Spec/Restart/RetAux79Zone.lean` (namespace `Restart.RetAux79`), which is not landed and cannot be imported; they
should be deduplicated when that file lands.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart.FCAux79

open MartChar.RealFlow

variable {w : ℝ → ℝ}

/-- `y ↦ g_t(y)` is strictly increasing from an alive point. -/
theorem gImg_lt_gImg (hw : Continuous w) {x x' t : ℝ} (ht : 0 ≤ t) (hx : Alive w x t) (hxx : x < x') :
    gImg w x t < gImg w x' t := by
  have h := (cflow_lt_and_sub_le hw hx hxx ht ⟨ht, le_rfl⟩).1
  simp only [gImg]
  linarith

/-- **The image of a mark `z ≠ x` is at most `g_t(x)` iff `z < x`** (`x` alive). -/
theorem rightImg_le_gImg_iff (hw : Continuous w) {x z t : ℝ} (ht : 0 ≤ t) (hx : Alive w x t) (hzx : z ≠ x) :
    rightImg w z t ≤ gImg w x t ↔ z < x := by
  refine ⟨fun h => ?_, fun h => rightImg_le_gImg hw ht h hx⟩
  by_contra hle
  have hxz : x < z := lt_of_le_of_ne (not_lt.1 hle) (Ne.symm hzx)
  have hxx' : x < (x + z) / 2 := by linarith
  have hx'z : (x + z) / 2 < z := by linarith
  have hx' : Alive w ((x + z) / 2) t := hx.of_le hw hxx'.le ht
  have h1 : gImg w ((x + z) / 2) t ≤ rightImg w z t :=
    le_csInf (imgSet_nonempty hw z ht) fun _ ⟨y, hzy, _, hg⟩ =>
      hg ▸ (gImg_lt_gImg hw ht hx' (hx'z.trans hzy)).le
  have h2 := gImg_lt_gImg hw ht hx hxx'
  linarith

/-- **Every value above the image of `0⁺` is the image of an alive positive point.** -/
theorem exists_alive_gImg_eq (hw : Continuous w) {t M : ℝ} (ht : 0 ≤ t) (hM : rightImg w 0 t < M) :
    ∃ x, 0 < x ∧ Alive w x t ∧ gImg w x t = M := by
  obtain ⟨y₀, hy₀0, hy₀, hg₀⟩ := exists_lt_of_rightImg_lt hw ht hM
  have hy₀M : y₀ ≤ M := (hy₀.le_gImg hw ht).trans hg₀.le
  have hcont : ContinuousOn (fun y => gImg w y t) (Icc y₀ M) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun c hc d hd => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_gImg_sub_le hw ht (hy₀.of_le hw hd.1 ht) (hy₀.of_le hw hc.1 ht)
  have hMg : M ≤ gImg w M t := (hy₀.of_le hw hy₀M ht).le_gImg hw ht
  obtain ⟨x, hx, hxg⟩ := intermediate_value_Icc hy₀M hcont ⟨hg₀.le, hMg⟩
  exact ⟨x, hy₀0.trans_le hx.1, hy₀.of_le hw hx.1 ht, hxg⟩

/-- **Forward solutions from real points** are the real flows of alive points: from `x > 0` the value at `t` is
`g_t(x) − w_t`, from `x < 0` it is `−g̃_t(−x) − w_t` for the reflected driver. -/
theorem isForwardSol_real_cases (hw : Continuous w) (hw0 : w 0 = 0) {x t : ℝ} (ht : 0 ≤ t) {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol w (x : ℂ) t u) :
    (0 < x ∧ Alive w x t ∧ u t = ((gImg w x t - w t : ℝ) : ℂ)) ∨
      (x < 0 ∧ Alive (fun s => -w s) (-x) t ∧ u t = ((-gImg (fun s => -w s) (-x) t - w t : ℝ) : ℂ)) := by
  have h0 := hu.2 0 ⟨le_rfl, ht⟩
  have hx0 : x ≠ 0 := by
    intro hx
    apply h0.1
    rw [h0.2, hx, hw0]
    simp
  have him : (u t).im = 0 := im_eq_zero_of_isForwardSol_real hw hu ⟨ht, le_rfl⟩
  have hut : u t = (((u t).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · right
    have hu' := QuantumZipper.RS.isForwardSol_neg hu
    have e : -((x : ℝ) : ℂ) = ((-x : ℝ) : ℂ) := by push_cast; ring
    rw [e] at hu'
    have hwn : Continuous fun s => -w s := hw.neg
    have hP := WangWu.isPosSol_of_isForwardSol hwn (by simp [hw0]) (neg_pos.2 hx) hu'
    have hc := cflow_eq_of_isPosSol hwn hP ⟨ht, le_rfl⟩
    refine ⟨hx, ⟨_, hP⟩, ?_⟩
    rw [hut]
    congr 1
    simp only [gImg, hc, neg_re]
    ring
  · left
    have hP := WangWu.isPosSol_of_isForwardSol hw hw0 hx hu
    have hc := cflow_eq_of_isPosSol hw hP ⟨ht, le_rfl⟩
    refine ⟨hx, ⟨_, hP⟩, ?_⟩
    rw [hut]
    congr 1
    simp only [gImg, hc]
    ring

/-- **A positive solution is a forward solution** from its real starting point (`w 0 = 0`), with value
`g_t(y) − w_t` at `t`. -/
theorem exists_isForwardSol_of_alive (hw : Continuous w) (hw0 : w 0 = 0) {y t : ℝ} (ht : 0 ≤ t)
    (hy : Alive w y t) : ∃ u, QuantumZipper.IsForwardSol w (y : ℂ) t u ∧ u t = ((gImg w y t - w t : ℝ) : ℂ) := by
  obtain ⟨X, hX⟩ := hy
  have hX0 : X 0 = y := by
    have := (hX.2 0 ⟨le_rfl, ht⟩).2
    simpa [hw0] using this
  have hsol := InteractingSLE.isForwardSol_ofReal (W := w) hw0 hX.1 (fun s hs => (hX.2 s hs).1.ne')
    fun s hs => by
      rw [(hX.2 s hs).2, hX0, hw0]
      ring
  rw [hX0] at hsol
  refine ⟨_, hsol, ?_⟩
  have hc := cflow_eq_of_isPosSol hw hX ⟨ht, le_rfl⟩
  simp only [gImg, hc]
  push_cast
  ring

section Force

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **Right of the image of `0⁺` the flowed force datum is the initial one**: at `g_t(x) − w_t`, `x > 0` alive and
no right mark at `x`, it is the force datum of the initial marks at `x`. -/
theorem forceBoundaryData_flow_right (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx0 : 0 < x)
    (hx : Alive w x t) (hxR : ∀ j, xR j ≠ x) :
    forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) t - w t)
        (fun j => rightImg w (xR j) t - w t) (gImg w x t - w t) = forceBoundaryData κ ρL ρR xL xR x := by
  have hpos : 0 < gImg w x t - w t := by linarith [hx.lt_gImg hw ⟨ht, le_rfl⟩]
  have h1 : ¬ (gImg w x t - w t < 0) := not_lt.2 hpos.le
  have h2 : ¬ (x < 0) := not_lt.2 hx0.le
  unfold forceBoundaryData
  simp only [h1, h2, ↓reduceIte]
  congr 3
  refine Finset.filter_congr fun j _ => ?_
  rw [sub_le_sub_iff_right, rightImg_le_gImg_iff hw ht hx (hxR j)]
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (hxR j)⟩

/-- **Left of the image of `0⁻` the flowed force datum is the initial one** (mirror of
`forceBoundaryData_flow_right`; `x > 0` alive for the reflected driver, the point is `−x`). -/
theorem forceBoundaryData_flow_left (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx0 : 0 < x)
    (hx : Alive (fun s => -w s) x t) (hxL : ∀ i, -xL i ≠ x)
    (hy : ∀ i, -gImg (fun s => -w s) x t - w t ≠ -rightImg (fun s => -w s) (-xL i) t - w t) :
    forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) t - w t)
        (fun j => rightImg w (xR j) t - w t) (-gImg (fun s => -w s) x t - w t) =
      forceBoundaryData κ ρL ρR xL xR (-x) := by
  have hwn : Continuous fun s => -w s := hw.neg
  have hneg : -gImg (fun s => -w s) x t - w t < 0 := by
    have := hx.lt_gImg hwn ⟨ht, le_rfl⟩
    linarith
  have h2 : -x < 0 := neg_lt_zero.2 hx0
  unfold forceBoundaryData
  simp only [hneg, h2, ↓reduceIte]
  congr 3
  refine Finset.filter_congr fun i _ => ?_
  have key := rightImg_le_gImg_iff hwn ht hx (hxL i)
  constructor
  · intro h
    have h' : rightImg (fun s => -w s) (-xL i) t ≤ gImg (fun s => -w s) x t := by linarith
    have := key.1 h'
    linarith
  · intro h
    have h' := key.2 (by linarith)
    exact lt_of_le_of_ne (by linarith) (hy i)

/-- **On the image of the right side of the trace** (`0 ≤ y < V̂^{0,R}`) the flowed force datum is `λ`. -/
theorem forceBoundaryData_flow_slit_right (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) (hxR : ∀ j, 0 ≤ xR j) {y : ℝ}
    (hy0 : 0 ≤ y) (hy : y < rightImg w 0 t - w t) :
    forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) t - w t)
        (fun j => rightImg w (xR j) t - w t) y = Real.pi / Real.sqrt κ := by
  have h1 : ¬ (y < 0) := not_lt.2 hy0
  unfold forceBoundaryData
  simp only [h1, ↓reduceIte]
  have he : Finset.univ.filter (fun j => rightImg w (xR j) t - w t ≤ y) = ∅ := by
    refine Finset.filter_false_of_mem fun j _ h => ?_
    have := rightImg_mono_index hw ht (hxR j)
    linarith
  rw [he, Finset.sum_empty, add_zero, mul_one]

/-- **On the image of the left side of the trace** (`V̂^{0,L} < y < 0`) the flowed force datum is `−λ`. -/
theorem forceBoundaryData_flow_slit_left (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) (hxL : ∀ i, xL i ≤ 0) {y : ℝ}
    (hy0 : y < 0) (hy : -rightImg (fun s => -w s) 0 t - w t < y) :
    forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -w s) (-xL i) t - w t)
        (fun j => rightImg w (xR j) t - w t) y = -(Real.pi / Real.sqrt κ) := by
  unfold forceBoundaryData
  simp only [hy0, ↓reduceIte]
  have he : Finset.univ.filter (fun i => y < -rightImg (fun s => -w s) (-xL i) t - w t) = ∅ := by
    refine Finset.filter_false_of_mem fun i _ h => ?_
    have := rightImg_mono_index (w := fun s => -w s) hw.neg ht (neg_nonneg.2 (hxL i))
    linarith
  rw [he, Finset.sum_empty, add_zero, mul_one]

end Force

end Restart.FCAux79

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WmMap
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalWord
import InteractingSLE.Spec.Supplement.SB2WdLaunch
import InteractingSLE.Spec.Supplement.Aux10FullLocal

/-!
# GW2's stage word map, part 4: the label positions (D12 item 3)

Packet PROVE-GW2-GEOM2 (round 7; DECISIONS-FABLE-3 D12 item 3: "the far labels are the chart images of the physical
marks, and the boundary map is monotone on each real ray … one lemma: positions of the root word's labels as `relBdry`
values and tail-junction positions `markPos`/`markPosL`"). The root word's labels are returned positions: the mark
`p` of the original word (read in the infinity-source chart) carried by the counterflow to `markPos U s p` (`p > 0`)
or `markPosL U s p` (`p < 0`), returned through `R(z) = −1/z`, and re-centred at the root.

* `labelR U s p = −(markPos U s p)⁻¹`, `labelL U s p = −(markPosL U s p)⁻¹`;
* **`mem_jumps_rootWord`**: every label of `rootWord κ c′ x r` is the root `−rootOff x r`, a returned left mark
  `labelL U s (xL′ i) − rootOff`, or a returned right mark `labelR U s (xR′ j) − rootOff` (`xL′`, `xR′` the flow-line
  marks of `c′`); **`labelL_mem_jumps_rootWord`**, **`labelR_mem_jumps_rootWord`**: and each of these is a label;
* **the tail junctions** `labelR U s 0 − rootOff` (the seed's right side, leftmost) and `labelL U s 0 − rootOff` (the
  seed's left side, rightmost) are labels and bound all labels (`rootWord_label_bounds`): beyond them the root word has
  its far heights (`GW2WmFar`);
* **`labelR_eq_relBdry`**, **`labelL_eq_relBdry`**: at an untouched physical point `y` (left resp. right of the
  root), the returned mark of `−1/y` IS the boundary chart image `Re relBdry U s y` (`markPos` is the real forward
  map at an alive point; `GW2Sf.relBdry_of_real`);
* **`monotoneOn_labelR`**, **`monotoneOn_labelL`**, **`monotoneOn_labelR_phys`**, **`monotoneOn_labelL_phys`**: the
  returned positions are monotone on each real ray, in the original-word coordinate and in the physical coordinate.

The labels of the later stage words are the earlier labels carried by the pieces' mark flows
(`Sec5.CrossCond.StagedFinal.mem_jumps_stopWord`: every label of `stopWord κ (c, θ, r)` is `markPosL r (xL i)`, `0`, or
`markPos r (xR j)`). Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC fwdMap IsForwardSol)

namespace InteractingSLE.Theorem14.GW2Wm

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSysField GW2JointKernel

/-! ### Mark positions at alive points -/

section Alive

variable {w : ℝ → ℝ} {T : ℝ}

/-- At an alive positive point the right mark position is the real forward map. -/
theorem markPos_eq_re_fwdMap (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {p : ℝ} (hp : 0 < p)
    (hA : ∃ v, IsForwardSol w (p : ℂ) T v) : markPos w T p = (fwdMap w T p).re := by
  obtain ⟨v, hv⟩ := hA
  rw [markPos_eq hw hw0 hT (isMark_of_isForwardSol hw hw0 hp hT hv),
    fwdMap_eq_of_isForwardSol hw hv ⟨hT, le_rfl⟩]

/-- At an alive negative point the left mark position is the real forward map. -/
theorem markPosL_eq_re_fwdMap (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {p : ℝ} (hp : p < 0)
    (hA : ∃ v, IsForwardSol w (p : ℂ) T v) : markPosL w T p = (fwdMap w T p).re := by
  have hA' : ∃ v, IsForwardSol (-w) (((-p : ℝ)) : ℂ) T v := by
    rw [alive_neg_iff w T (-p), neg_neg]; exact hA
  unfold markPosL
  have h := markPos_eq_re_fwdMap (w := fun s => -w s) hw.neg (by simp [hw0]) hT (neg_pos.2 hp) hA'
  rw [h]
  have e := QuantumZipper.F1.fwdMap_reflect_ofReal w hT p
  change -(fwdMap (-w) T (((-p : ℝ)) : ℂ)).re = _
  rw [e, Complex.neg_re, neg_neg]

end Alive

/-! ### Returned positions -/

/-- **The returned position of a right mark**: `−1/markPos`. -/
def labelR (U : ℝ → ℝ) (s p : ℝ) : ℝ := -(markPos U s p)⁻¹

/-- **The returned position of a left mark**: `−1/markPosL`. -/
def labelL (U : ℝ → ℝ) (s p : ℝ) : ℝ := -(markPosL U s p)⁻¹

section Labels

variable {κ : ℝ} {c' : BoundaryWord} {x : ℝ} {r : RecData}

/-- **Every label of the root word** is the root, a returned left mark, or a returned right mark. -/
theorem mem_jumps_rootWord {y : ℝ} (hy : y ∈ (rootWord κ c' x r).jumps) :
    y = -rootOff x r ∨
      (∃ i : Fin (flowLineNL c'.fn c'.jumps 0),
        y = labelL (rdrv r) (rtime r) (flowLineXL c'.fn c'.jumps 0 i) - rootOff x r) ∨
      ∃ j : Fin (flowLineNR c'.fn c'.jumps 0),
        y = labelR (rdrv r) (rtime r) (flowLineXR c'.fn c'.jumps 0 j) - rootOff x r := by
  unfold rootWord at hy
  rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW] at hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
  unfold jointWordOfRec at hw
  rw [jumps_retWord (isSorted_stopWord _ _)] at hw
  unfold returnExcept at hw
  rcases Finset.mem_insert.1 hw with rfl | hw'
  · left; ring
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw'
    rcases Sec5.CrossCond.StagedFinal.mem_jumps_stopWord hp with ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · left; simp
    · exact Or.inr (Or.inr ⟨j, rfl⟩)

/-- Every right mark position of a stop word is a jump of it. -/
theorem markPos_mem_jumps_stopWord {k : ℝ} (c : BoundaryWord) (θ : ℝ) (r : RecData) {j : ℕ}
    (hj : j < flowLineNR c.fn c.jumps 0) :
    markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) ∈ (stopWord k (c, θ, r)).jumps := by
  have hmo := GW1W.isMarkOrder_stopWord c r
  refine BoundaryWord.mem_jumps.2 ⟨flowLineNL c.fn c.jumps 0 + 1 + j, by
    change _ < flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0; omega, ?_⟩
  change cumMax (rawPos _ _ _) _ = _
  rw [cumMax_rawPos hmo (by omega)]
  unfold rawPos
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  beta_reduce
  rw [show flowLineNL c.fn c.jumps 0 + 1 + j - flowLineNL c.fn c.jumps 0 - 1 = j by omega]

theorem returned_mem_jumps_rootWord {p : ℝ} (hp : p ∈ (stopWord (16 / κ) (c', 0, r)).jumps) :
    -p⁻¹ - rootOff x r ∈ (rootWord κ c' x r).jumps := by
  unfold rootWord
  rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW]
  refine Finset.mem_image.2 ⟨-p⁻¹, ?_, rfl⟩
  unfold jointWordOfRec
  rw [jumps_retWord (isSorted_stopWord _ _)]
  unfold returnExcept
  exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨p, hp, rfl⟩)

/-- **Each returned left mark is a label of the root word.** -/
theorem labelL_mem_jumps_rootWord (i : Fin (flowLineNL c'.fn c'.jumps 0)) :
    labelL (rdrv r) (rtime r) (flowLineXL c'.fn c'.jumps 0 i) - rootOff x r ∈ (rootWord κ c' x r).jumps := by
  have h := GW1W.markPosL_mem_jumps_stopWord (κ := 16 / κ) c' 0 r i.2
  rw [padFL_fst_fst_fin c'.fn c'.jumps i] at h
  exact returned_mem_jumps_rootWord h

/-- **Each returned right mark is a label of the root word.** -/
theorem labelR_mem_jumps_rootWord (j : Fin (flowLineNR c'.fn c'.jumps 0)) :
    labelR (rdrv r) (rtime r) (flowLineXR c'.fn c'.jumps 0 j) - rootOff x r ∈ (rootWord κ c' x r).jumps := by
  have h := markPos_mem_jumps_stopWord (k := 16 / κ) c' 0 r j.2
  rw [padFL_fst_snd_fin c'.fn c'.jumps j] at h
  exact returned_mem_jumps_rootWord h

/-- **The tail junctions are labels**: the returned seed sides `labelR U s 0` and `labelL U s 0`. -/
theorem tailJunctions_mem_jumps_rootWord :
    labelR (rdrv r) (rtime r) 0 - rootOff x r ∈ (rootWord κ c' x r).jumps ∧
      labelL (rdrv r) (rtime r) 0 - rootOff x r ∈ (rootWord κ c' x r).jumps := by
  have hR := labelR_mem_jumps_rootWord (κ := κ) (x := x) (r := r) ⟨0, Supp8.GB6.zero_lt_flowLineNR c'.fn c'.jumps⟩
  have hL := labelL_mem_jumps_rootWord (κ := κ) (x := x) (r := r) ⟨0, Supp8.GB6.zero_lt_flowLineNL c'.fn c'.jumps⟩
  rw [show flowLineXR c'.fn c'.jumps 0 ⟨0, _⟩ = 0 from Sec4.flowLineXR_zero c'.fn c'.jumps] at hR
  rw [show flowLineXL c'.fn c'.jumps 0 ⟨0, _⟩ = 0 from Sec4.flowLineXL_zero c'.fn c'.jumps] at hL
  exact ⟨hR, hL⟩

/-- **The tail junctions bound all labels** (the leftmost and the rightmost label), as soon as the counterflow's hull
has positive extent on both sides. -/
theorem rootWord_label_bounds (hpos : 0 < markPos (rdrv r) (rtime r) 0) (hneg : markPosL (rdrv r) (rtime r) 0 < 0)
    {y : ℝ} (hy : y ∈ (rootWord κ c' x r).jumps) :
    labelR (rdrv r) (rtime r) 0 - rootOff x r ≤ y ∧ y ≤ labelL (rdrv r) (rtime r) 0 - rootOff x r := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hs := rtime_nonneg r
  have hR0 : labelR (rdrv r) (rtime r) 0 < 0 := neg_neg_of_pos (inv_pos.2 hpos)
  have hL0 : 0 < labelL (rdrv r) (rtime r) 0 := neg_pos.2 (inv_lt_zero.2 hneg)
  rcases mem_jumps_rootWord hy with rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
  · constructor <;> linarith
  · have hxi := GW3Word.flowLineXL_nonpos c'.fn c'.jumps i
    have hm : markPosL (rdrv r) (rtime r) (flowLineXL c'.fn c'.jumps 0 i) ≤ markPosL (rdrv r) (rtime r) 0 :=
      GW1W.markPosL_mono hU hU0 hs le_rfl hxi
    have hneg' := hm.trans_lt hneg
    have h1 : 0 < labelL (rdrv r) (rtime r) (flowLineXL c'.fn c'.jumps 0 i) := neg_pos.2 (inv_lt_zero.2 hneg')
    have h2 : labelL (rdrv r) (rtime r) (flowLineXL c'.fn c'.jumps 0 i) ≤ labelL (rdrv r) (rtime r) 0 := by
      unfold labelL
      exact neg_le_neg ((inv_le_inv_of_neg hneg hneg').2 hm)
    constructor <;> linarith
  · have hxj := GW3Word.flowLineXR_nonneg c'.fn c'.jumps j
    have hm : markPos (rdrv r) (rtime r) 0 ≤ markPos (rdrv r) (rtime r) (flowLineXR c'.fn c'.jumps 0 j) :=
      GW1W.markPos_mono hU hU0 hs le_rfl hxj
    have hpos' := hpos.trans_le hm
    have h1 : labelR (rdrv r) (rtime r) (flowLineXR c'.fn c'.jumps 0 j) < 0 := neg_neg_of_pos (inv_pos.2 hpos')
    have h2 : labelR (rdrv r) (rtime r) 0 ≤ labelR (rdrv r) (rtime r) (flowLineXR c'.fn c'.jumps 0 j) := by
      unfold labelR
      exact neg_le_neg (inv_anti₀ hpos hm)
    constructor <;> linarith

end Labels

/-! ### The returned positions are the boundary chart images -/

section Bdry

variable {U : ℝ → ℝ} {s : ℝ}

/-- **A returned right mark is the boundary chart image** of the untouched physical point `y < 0` (`p = −1/y > 0`). -/
theorem labelR_eq_relBdry (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) {y : ℝ} (hy : y < 0)
    (hyA : (y : ℂ) ∉ closure (Supp8.Q3Rel.invHull U s)) :
    labelR U s (-y⁻¹) = (Supp8.GB6.CoordB.relBdry U s y).re := by
  have hp : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
  have hK := Supp8.Q3Rel.negInv_notMem_closure hy.ne hyA
  have hA := Aux10.exists_isForwardSol_of_notMem_closure hU hU0 hs hp.ne' hK
  rw [GW2Sf.relBdry_of_real hU hU0 hs hy.ne hyA, Complex.ofReal_re]
  unfold labelR
  rw [markPos_eq_re_fwdMap hU hU0 hs hp hA]

/-- **A returned left mark is the boundary chart image** of the untouched physical point `y > 0` (`p = −1/y < 0`). -/
theorem labelL_eq_relBdry (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y)
    (hyA : (y : ℂ) ∉ closure (Supp8.Q3Rel.invHull U s)) :
    labelL U s (-y⁻¹) = (Supp8.GB6.CoordB.relBdry U s y).re := by
  have hp : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy)
  have hK := Supp8.Q3Rel.negInv_notMem_closure hy.ne' hyA
  have hA := Aux10.exists_isForwardSol_of_notMem_closure hU hU0 hs hp.ne hK
  rw [GW2Sf.relBdry_of_real hU hU0 hs hy.ne' hyA, Complex.ofReal_re]
  unfold labelL
  rw [markPosL_eq_re_fwdMap hU hU0 hs hp hA]

/-! ### Monotone on each real ray -/

/-- **The returned right marks are monotone on the right ray** of the original-word coordinate. -/
theorem monotoneOn_labelR (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (hpos : 0 < markPos U s 0) :
    MonotoneOn (labelR U s) (Ici 0) := by
  intro p hp p' hp' hpp'
  have hm := GW1W.markPos_mono hU hU0 hs (show (0 : ℝ) ≤ p from hp) hpp'
  have hp0 : 0 < markPos U s p := hpos.trans_le (GW1W.markPos_mono hU hU0 hs le_rfl hp)
  unfold labelR
  exact neg_le_neg (inv_anti₀ hp0 hm)

/-- **The returned left marks are monotone on the left ray** of the original-word coordinate. -/
theorem monotoneOn_labelL (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (hneg : markPosL U s 0 < 0) :
    MonotoneOn (labelL U s) (Iic 0) := by
  intro p hp p' hp' hpp'
  have hm := GW1W.markPosL_mono hU hU0 hs (show p' ≤ 0 from hp') hpp'
  have hp0 : markPosL U s p' < 0 := (GW1W.markPosL_mono hU hU0 hs le_rfl hp').trans_lt hneg
  have hp0' : markPosL U s p < 0 := hm.trans_lt hp0
  unfold labelL
  exact neg_le_neg ((inv_le_inv_of_neg hp0 hp0').2 hm)

/-- **Monotone on the physical left ray**: `y ↦ labelR U s (−1/y)` on `y < 0`. -/
theorem monotoneOn_labelR_phys (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (hpos : 0 < markPos U s 0) :
    MonotoneOn (fun y => labelR U s (-y⁻¹)) (Iio 0) := by
  intro y hy y' hy' hyy'
  have hy0 : y < 0 := hy
  have hy0' : y' < 0 := hy'
  refine monotoneOn_labelR hU hU0 hs hpos (neg_nonneg.2 (inv_nonpos.2 hy0.le)) (neg_nonneg.2 (inv_nonpos.2 hy0'.le))
    ?_
  exact neg_le_neg ((inv_le_inv_of_neg hy0' hy0).2 hyy')

/-- **Monotone on the physical right ray**: `y ↦ labelL U s (−1/y)` on `y > 0`. -/
theorem monotoneOn_labelL_phys (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (hneg : markPosL U s 0 < 0) :
    MonotoneOn (fun y => labelL U s (-y⁻¹)) (Ioi 0) := by
  intro y hy y' hy' hyy'
  have hy0 : 0 < y := hy
  have hy0' : 0 < y' := hy'
  refine monotoneOn_labelL hU hU0 hs hneg (neg_nonpos.2 (inv_nonneg.2 hy0.le)) (neg_nonpos.2 (inv_nonneg.2 hy0'.le))
    ?_
  exact neg_le_neg (inv_anti₀ hy0 hyy')

end Bdry

end InteractingSLE.Theorem14.GW2Wm

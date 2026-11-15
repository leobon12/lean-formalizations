/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdArc
import InteractingSLE.Spec.Sec7.R6CorReflect

/-!
# R.6's seed corner: planar facts for the inner pocket's landings

Packet PROVE-R6-CORNER. Deterministic facts used to place the landings of the same-time inner chart
(`R6CorReflect`):

* `frontier_pos_left_arc` / `frontier_neg_right_arc`: a boundary point of a bounded change pocket `U` (other than its
  outgoing corner) whose Jordan coordinate has positive (negative) real part lies on `U`'s open left (right) arc — the
  other arc has nonpositive (nonnegative) coordinate (`R6Fd.right_arc_facts`, `R6Fd.left_arc_facts`);
* `openPt_notMem_of_shared_left` / `_right`: the outgoing corner `x₀` of the outer pocket `C` is in `closure U` only
  if it is `U`'s outgoing corner (wall parameters, `R6Fd.mem_Icc_left_of_mem_closure`);
* `landR_re_lt` / `landL_re_gt`: a real point beyond the right (left) force coordinate lands at a real point strictly
  beyond the force landing (intermediate values along the alive real line, as in `R6Fd.le_re_landR`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Function
open QuantumZipper (H Hbar fwdMapInv fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec7.R6Cor

open WangWu PocketCoord Lemma71I PocketJordan PocketWordAssembly R6Fd

variable {R L R' L' : ℝ≥0 → ℂ} {r r' : ℝ≥0}

/-! ### The two arcs of a bounded change pocket in its Jordan coordinate -/

theorem cfArcR_zero_eq (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : cfArcR R L r 0 = cfPt (openPt R L r) := by
  simp only [cfArcR, zero_mul, add_zero]
  rfl

theorem cfArcR_eq_wallPt (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (w : ℝ) :
    cfArcR R L r w = wallPt R (rightLo R L r + w * (rightHi R L r - rightLo R L r)) := rfl

theorem cfArcL_eq_wallPt (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (v : ℝ) :
    cfArcL R L r v = wallPt L (leftLo R L r + v * (leftHi R L r - leftLo R L r)) := rfl

theorem affine_mem_Ioc {lo hi w : ℝ} (hlh : lo < hi) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    lo + w * (hi - lo) ∈ Ioc lo hi := by
  have h1 : 0 < w * (hi - lo) := mul_pos hw0 (sub_pos.2 hlh)
  have h2 : w * (hi - lo) ≤ 1 * (hi - lo) := mul_le_mul_of_nonneg_right hw1 (sub_pos.2 hlh).le
  constructor <;> linarith

theorem affine_mem_Ioo {lo hi w : ℝ} (hlh : lo < hi) (hw0 : 0 < w) (hw1 : w < 1) :
    lo + w * (hi - lo) ∈ Ioo lo hi := by
  have h1 : 0 < w * (hi - lo) := mul_pos hw0 (sub_pos.2 hlh)
  have h2 : w * (hi - lo) < 1 * (hi - lo) := mul_lt_mul_of_pos_right hw1 (sub_pos.2 hlh)
  constructor <;> linarith

/-- **Boundary points with positive coordinate are on the open left arc.** -/
theorem frontier_pos_left_arc (hU : IsChangeConfigInc R' L r') (hU0 : (0 : ℂ) ∉ closure (changePocket R' L r'))
    (hor : PocketMarks.IsFlowChartOriented R' L r') {ψ' : ℂ → ℂ} (hψ' : IsCfJordan R' L r' ψ') {p : ℂ}
    (hp : p ∈ frontier (cfPocket R' L r')) (hpx : p ≠ cfPt (openPt R' L r')) (hpos : 0 < (ψ' p).re) :
    ∃ θ ∈ Ioo (leftLo R' L r') (leftHi R' L r'), p = wallPt L θ := by
  have hUc := hU.isCfPocket hU0
  obtain ⟨-, -, huv, -, -, hab, hLa, hLb⟩ := hU.changeCorner_props
  rw [hUc.frontier_eq] at hp
  rcases hp with ⟨w, hw, hwp⟩ | ⟨v, hv, hvp⟩
  · exfalso
    rcases hw.1.lt_or_eq with hw0 | hw0
    · obtain ⟨-, -, hmono⟩ := right_arc_facts hU hU0 hor hψ'
      have hs := affine_mem_Ioc huv hw0 hw.2
      have hhi : rightHi R' L r' ∈ Ioc (rightLo R' L r') (rightHi R' L r') := ⟨huv, le_rfl⟩
      have hle : (ψ' (wallPt R' (rightLo R' L r' + w * (rightHi R' L r' - rightLo R' L r')))).re ≤
          (ψ' (wallPt R' (rightHi R' L r'))).re := hmono.monotoneOn hs hhi hs.2
      have h0 : ψ' (wallPt R' (rightHi R' L r')) = 0 := hψ'.2.2.2.2.2.1
      rw [← cfArcR_eq_wallPt, hwp, h0, Complex.zero_re] at hle
      linarith
    · exact hpx (by rw [← hwp, ← hw0]; exact cfArcR_zero_eq R' L r')
  · rcases hv.1.lt_or_eq with hv0 | hv0
    · rcases hv.2.lt_or_eq with hv1 | hv1
      · exact ⟨_, affine_mem_Ioo hab hv0 hv1, by rw [← hvp]; exact cfArcL_eq_wallPt R' L r' v⟩
      · exfalso
        have he : p = cfPt (closePt R' L r') := by
          rw [← hvp, cfArcL_eq_wallPt, hv1, one_mul, add_sub_cancel]
          show cfPt (toDisc (Lemma71I.realPath L) (leftHi R' L r')) = _
          rw [hLb]
        rw [he, hψ'.2.2.2.2.2.1, Complex.zero_re] at hpos
        exact lt_irrefl _ hpos
    · exfalso
      apply hpx
      rw [← hvp, cfArcL_eq_wallPt, ← hv0, zero_mul, add_zero]
      show cfPt (toDisc (Lemma71I.realPath L) (leftLo R' L r')) = _
      rw [hLa]

/-- **Boundary points with negative coordinate are on the open right arc.** -/
theorem frontier_neg_right_arc (hU : IsChangeConfigInc R L' r') (hU0 : (0 : ℂ) ∉ closure (changePocket R L' r'))
    (hor : PocketMarks.IsFlowChartOriented R L' r') {ψ' : ℂ → ℂ} (hψ' : IsCfJordan R L' r' ψ') {p : ℂ}
    (hp : p ∈ frontier (cfPocket R L' r')) (hpx : p ≠ cfPt (openPt R L' r')) (hneg : (ψ' p).re < 0) :
    ∃ s ∈ Ioo (rightLo R L' r') (rightHi R L' r'), p = wallPt R s := by
  have hUc := hU.isCfPocket hU0
  obtain ⟨-, -, huv, -, -, hab, hLa, hLb⟩ := hU.changeCorner_props
  rw [hUc.frontier_eq] at hp
  rcases hp with ⟨w, hw, hwp⟩ | ⟨v, hv, hvp⟩
  · rcases hw.1.lt_or_eq with hw0 | hw0
    · rcases hw.2.lt_or_eq with hw1 | hw1
      · exact ⟨_, affine_mem_Ioo huv hw0 hw1, by rw [← hwp]; exact cfArcR_eq_wallPt R L' r' w⟩
      · exfalso
        have he : p = cfPt (closePt R L' r') := by
          rw [← hwp, cfArcR_eq_wallPt, hw1, one_mul, add_sub_cancel]
          rfl
        rw [he, hψ'.2.2.2.2.2.1, Complex.zero_re] at hneg
        exact lt_irrefl _ hneg
    · exact absurd (by rw [← hwp, ← hw0]; exact cfArcR_zero_eq R L' r') hpx
  · exfalso
    rcases hv.1.lt_or_eq with hv0 | hv0
    · obtain ⟨-, -, hanti⟩ := left_arc_facts hU hU0 hor hψ'
      have hs := affine_mem_Ioc hab hv0 hv.2
      have hhi : leftHi R L' r' ∈ Ioc (leftLo R L' r') (leftHi R L' r') := ⟨hab, le_rfl⟩
      have hle : (ψ' (wallPt L' (leftHi R L' r'))).re ≤
          (ψ' (wallPt L' (leftLo R L' r' + v * (leftHi R L' r' - leftLo R L' r')))).re :=
        hanti.antitoneOn hs hhi hs.2
      have h0 : ψ' (wallPt L' (leftHi R L' r')) = 0 := by
        show ψ' (cfPt (toDisc (Lemma71I.realPath L') (leftHi R L' r'))) = 0
        rw [hLb]; exact hψ'.2.2.2.2.2.1
      rw [← cfArcL_eq_wallPt, hvp, h0, Complex.zero_re] at hle
      linarith
    · apply hpx
      rw [← hvp, cfArcL_eq_wallPt, ← hv0, zero_mul, add_zero]
      show cfPt (toDisc (Lemma71I.realPath L') (leftLo R L' r')) = _
      rw [hLa]

/-! ### The outer pocket's outgoing corner seen from the inner pocket -/

/-- **Shared left wall: `x₀ ∈ closure U` only if `x₀ = x₀ᵁ`.** -/
theorem openPt_eq_of_mem_closure_left (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hU : IsChangeConfigInc R' L r') (hU0 : (0 : ℂ) ∉ closure (changePocket R' L r'))
    (hsub : cfPocket R' L r' ⊆ cfPocket R L r) (hm : cfPt (openPt R L r) ∈ closure (cfPocket R' L r')) :
    cfPt (openPt R L r) = cfPt (openPt R' L r') := by
  obtain ⟨-, -, -, ha, -, -, hLa, -⟩ := h.changeCorner_props
  obtain ⟨-, -, -, ha', -, hab', hLa', -⟩ := hU.changeCorner_props
  have hx₀ : cfPt (openPt R L r) = wallPt L (leftLo R L r) := by
    show _ = cfPt (toDisc (Lemma71I.realPath L) (leftLo R L r)); rw [hLa]
  have hx₀' : cfPt (openPt R' L r') = wallPt L (leftLo R' L r') := by
    show _ = cfPt (toDisc (Lemma71I.realPath L) (leftLo R' L r')); rw [hLa']
  have h1 := mem_Icc_left_of_mem_closure hU hU0 ⟨h.leftLo_pos h0, ha.2⟩ (hx₀ ▸ hm)
  have h2 := mem_Icc_left_of_mem_closure h h0 ⟨hU.leftLo_pos hU0, ha'.2⟩
    (wallPt_left_mem_closure hU hU0 hsub ⟨le_rfl, hab'.le⟩)
  rw [hx₀, hx₀', le_antisymm h2.1 h1.1]

/-- **Shared right wall: `x₀ ∈ closure U` only if `x₀ = x₀ᵁ`.** -/
theorem openPt_eq_of_mem_closure_right (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hU : IsChangeConfigInc R L' r') (hU0 : (0 : ℂ) ∉ closure (changePocket R L' r'))
    (hsub : cfPocket R L' r' ⊆ cfPocket R L r) (hm : cfPt (openPt R L r) ∈ closure (cfPocket R L' r')) :
    cfPt (openPt R L r) = cfPt (openPt R L' r') := by
  obtain ⟨hu, -, -, -, -, -, -, -⟩ := h.changeCorner_props
  obtain ⟨hu', -, huv', -, -, -, -, -⟩ := hU.changeCorner_props
  have hx₀ : cfPt (openPt R L r) = wallPt R (rightLo R L r) := rfl
  have hx₀' : cfPt (openPt R L' r') = wallPt R (rightLo R L' r') := rfl
  have h1 := mem_Icc_right_of_mem_closure hU hU0 ⟨h.rightLo_pos h0, hu.2⟩ (hx₀ ▸ hm)
  have h2 := mem_Icc_right_of_mem_closure h h0 ⟨hU.rightLo_pos hU0, hu'.2⟩
    (wallPt_right_mem_closure hU hU0 hsub ⟨le_rfl, huv'.le⟩)
  rw [hx₀, hx₀', le_antisymm h2.1 h1.1]

/-! ### Real landings beyond the force coordinates -/

section Land

open WangWu (chartAL chartAR)

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {u : ℝ}

/-- **Beyond the right force coordinate the landing is real and strictly right of the force landing.** -/
theorem landR_re_lt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u)
    (hlt : chartAL W u < chartAR W u) {y : ℝ} (hy : chartAR W u < y) :
    (extendFrom H (fwdMapInv W u) (y : ℂ)).im = 0 ∧
      (extendFrom H (fwdMapInv W u) (chartAR W u : ℂ)).re < (extendFrom H (fwdMapInv W u) (y : ℂ)).re := by
  set F : ℝ → ℂ := fun t => extendFrom H (fwdMapInv W u) (t : ℂ) with hF
  have halive : ∀ t : ℝ, chartAR W u < t → F t ∉ closure (fwdHull W u) := fun t ht =>
    Supp8.RelTrans.extendFrom_notMem_closure_of_chartAR_lt hη hW hW0 hu.le ht
  have hreal : ∀ t : ℝ, chartAR W u < t → (F t).im = 0 := fun t ht =>
    Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hη hW hW0 hu.le (halive t ht)
  set b := (F (chartAR W u)).re with hb
  have hbF : F (chartAR W u) = (b : ℂ) := eq_ofReal_re_of_im_eq_zero (landR_im_eq_zero hη hW hW0 hu.le)
  have hbK : ((b : ℝ) : ℂ) ∈ closure (fwdHull W u) := hbF ▸ landR_mem_closure hη hW hW0 hu hlt
  refine ⟨hreal y hy, ?_⟩
  by_contra hle
  push Not at hle
  have hFc : Continuous F := continuous_landing hη hW hW0 hu.le
  obtain ⟨C, hC⟩ := R6Fd.exists_norm_extendFrom_sub_le hη hW hW0 hu.le
  set Y := max y (b + C + 1) with hY
  have hgY : b < (F Y).re := by
    have h1 := hC (Y : ℂ) (R6Fc.real_mem_Hbar Y)
    have h2 : |(F Y).re - Y| ≤ C := by
      have := Complex.abs_re_le_norm (F Y - (Y : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      exact this.trans h1
    have h3 : b + C + 1 ≤ Y := le_max_right _ _
    linarith [(abs_le.1 h2).1]
  obtain ⟨y', hy', hy'b⟩ := intermediate_value_Icc (le_max_left y (b + C + 1))
    (Complex.continuous_re.comp hFc).continuousOn ⟨hle, hgY.le⟩
  have hy'a : chartAR W u < y' := lt_of_lt_of_le hy hy'.1
  apply halive y' hy'a
  have he : F y' = (b : ℂ) := Complex.ext (by simpa using hy'b) (by simpa using hreal y' hy'a)
  rw [he]
  exact hbK

/-- **Beyond the left force coordinate the landing is real and strictly left of the force landing.** -/
theorem landL_re_gt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u)
    (hlt : chartAL W u < chartAR W u) {y : ℝ} (hy : y < chartAL W u) :
    (extendFrom H (fwdMapInv W u) (y : ℂ)).im = 0 ∧
      (extendFrom H (fwdMapInv W u) (y : ℂ)).re < (extendFrom H (fwdMapInv W u) (chartAL W u : ℂ)).re := by
  set F : ℝ → ℂ := fun t => extendFrom H (fwdMapInv W u) (t : ℂ) with hF
  have halive : ∀ t : ℝ, t < chartAL W u → F t ∉ closure (fwdHull W u) := fun t ht =>
    Supp8.RelTrans.extendFrom_notMem_closure_of_lt_chartAL hη hW hW0 hu.le ht
  have hreal : ∀ t : ℝ, t < chartAL W u → (F t).im = 0 := fun t ht =>
    Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hη hW hW0 hu.le (halive t ht)
  set b := (F (chartAL W u)).re with hb
  have hbF : F (chartAL W u) = (b : ℂ) := eq_ofReal_re_of_im_eq_zero (landL_im_eq_zero hη hW hW0 hu.le)
  have hbK : ((b : ℝ) : ℂ) ∈ closure (fwdHull W u) := hbF ▸ landL_mem_closure hη hW hW0 hu hlt
  refine ⟨hreal y hy, ?_⟩
  by_contra hle
  push Not at hle
  have hFc : Continuous F := continuous_landing hη hW hW0 hu.le
  obtain ⟨C, hC⟩ := R6Fd.exists_norm_extendFrom_sub_le hη hW hW0 hu.le
  set Y := min y (b - C - 1) with hY
  have hgY : (F Y).re < b := by
    have h1 := hC (Y : ℂ) (R6Fc.real_mem_Hbar Y)
    have h2 : |(F Y).re - Y| ≤ C := by
      have := Complex.abs_re_le_norm (F Y - (Y : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      exact this.trans h1
    have h3 : Y ≤ b - C - 1 := min_le_right _ _
    linarith [(abs_le.1 h2).2]
  obtain ⟨y', hy', hy'b⟩ := intermediate_value_Icc (min_le_left y (b - C - 1))
    (Complex.continuous_re.comp hFc).continuousOn ⟨hgY.le, hle⟩
  have hy'a : y' < chartAL W u := lt_of_le_of_lt hy'.2 hy
  apply halive y' hy'a
  have he : F y' = (b : ℂ) := Complex.ext (by simpa using hy'b) (by simpa using hreal y' hy'a)
  rw [he]
  exact hbK

end Land

end InteractingSLE.Sec7.R6Cor

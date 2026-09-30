import QuantumZipper.Proofs.Zipper.Cor15ZipFixLaw
import QuantumZipper.Proofs.Zipper.Cor15ZipRead
import QuantumZipper.Proofs.Zipper.Cor15MeasVerCInv
import QuantumZipper.Proofs.LQG.GoodMeasurableReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-ZIPCOORD (1): deterministic tools for the zip coordinate reading

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 and §1.4.
Task COR15-ZIPCOORD (decision D42). Own bookkeeping; no new analytic input.

* `rawConv_of_C1`: the countable uniform-continuity certificate `GoodMeas.C1` (raw values at the
  dyadic folded circles are uniformly continuous in the centre on bounded sets, a measurable
  condition: `GoodMeas.measurable_C1`) gives raw convergence along `dyadicRoundC n z` at **every**
  `z : ℂ` (the uncountable `∀ z` of the reading node, made measurable). This is the Cauchy
  argument of `GoodMeas.tendsto_raw_of_C1`, extended off `Hbar` by folding.
* `C1_of_coordsFull_eq_add`: the certificate depends only on the circle coordinates, up to an
  additive constant.
* `ccGoodAt_of_avgReg_shift`, `measurableSet_ccGoodAt`: the coordinate-change good condition
  `CCGoodAt` (integrability and convergence of the regularizing integrals) passes to shifted
  fields and is a measurable condition on a parameter.
* `coordChange_revMapInv_eq_CInv_fc`: the `CInv` candidate at a dyadic folded circle missing the
  time-reversed hull (the field-free part of `zipFld_apply_eq_CInv`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CoordsFull CircleCont GoodMeas

/-- A folded dyadic lattice point is a dyadic lattice point (as `F1ReflReg.foldH_lpt`). -/
theorem zc_foldH_lpt (n : ℕ) (a b : ℤ) : ∃ b' : ℤ, foldH (lpt n a b) = lpt n a b' := by
  unfold foldH
  split_ifs
  · exact ⟨b, rfl⟩
  · refine ⟨-b, ?_⟩
    apply Complex.ext <;> simp [CircleCont.lpt, neg_div]

theorem zc_foldH_mem_Hbar (w : ℂ) : foldH w ∈ Hbar := by
  unfold foldH Hbar
  split_ifs with h
  · exact h
  · simp only [mem_ofPred_eq, Complex.conj_im]
    linarith [not_le.mp h]

/-- **Raw convergence at every centre from the certificate `C1`.** -/
theorem rawConv_of_C1 {x : FieldSample} (h : C1 x) (k : ℕ) (z : ℂ) :
    ∃ l, Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l) := by
  refine ⟨_, tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
    (Metric.cauchySeq_iff.2 fun ε hε => ?_))⟩
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
  obtain ⟨j, hj⟩ := h k (⌈‖z‖⌉₊ + 1) e
  have hc := Nat.le_ceil ‖z‖
  set η : ℝ := min (1 / 2) ((1 / ((j : ℝ) + 1)) / 2) with hηd
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η ≤ (1 / ((j : ℝ) + 1)) / 2 := min_le_right _ _
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (RegClosure.tendsto_dyadicRoundC z) η hη
  refine ⟨N, fun n hn n' hn' => ?_⟩
  have h1 : ‖dyadicRoundC n z - z‖ < η := by rw [← dist_eq_norm]; exact hN n hn
  have h2 : ‖dyadicRoundC n' z - z‖ < η := by rw [← dist_eq_norm]; exact hN n' hn'
  obtain ⟨b1, hb1⟩ := zc_foldH_lpt n ⌊(2 : ℝ) ^ n * z.re⌋ ⌊(2 : ℝ) ^ n * z.im⌋
  obtain ⟨b2, hb2⟩ := zc_foldH_lpt n' ⌊(2 : ℝ) ^ n' * z.re⌋ ⌊(2 : ℝ) ^ n' * z.im⌋
  rw [← dyadicRoundC_eq_lpt] at hb1 hb2
  have e1 : x (foldedCircle (dyadicRoundC n z) (radius k)) =
      raw x (lpt n ⌊(2 : ℝ) ^ n * z.re⌋ b1) k := by
    rw [raw, ← hb1, CoordReg.foldedCircle_foldH]
  have e2 : x (foldedCircle (dyadicRoundC n' z) (radius k)) =
      raw x (lpt n' ⌊(2 : ℝ) ^ n' * z.re⌋ b2) k := by
    rw [raw, ← hb2, CoordReg.foldedCircle_foldH]
  have n1 := norm_sub_norm_le (dyadicRoundC n z) z
  have n2 := norm_sub_norm_le (dyadicRoundC n' z) z
  have hM : ∀ m : ℕ, ‖dyadicRoundC m z - z‖ < η →
      ‖foldH (dyadicRoundC m z)‖ ≤ ((⌈‖z‖⌉₊ + 1 : ℕ) : ℝ) := by
    intro m hm
    have := norm_sub_norm_le (dyadicRoundC m z) z
    rw [TwoPoint.norm_foldH]
    push_cast
    linarith
  have hd : ‖foldH (dyadicRoundC n z) - foldH (dyadicRoundC n' z)‖ < 1 / ((j : ℝ) + 1) := by
    refine (TwoPoint.norm_foldH_sub_le _ _).trans_lt ?_
    calc ‖dyadicRoundC n z - dyadicRoundC n' z‖
        = ‖(dyadicRoundC n z - z) - (dyadicRoundC n' z - z)‖ := by congr 1; ring
      _ ≤ ‖dyadicRoundC n z - z‖ + ‖dyadicRoundC n' z - z‖ := norm_sub_le _ _
      _ < 1 / ((j : ℝ) + 1) := by linarith
  rw [Real.dist_eq, e1, e2]
  refine (hj n _ b1 n' _ b2 ?_ ?_ ?_ ?_ ?_).trans_lt he
  · rw [← hb1]; exact zc_foldH_mem_Hbar _
  · rw [← hb2]; exact zc_foldH_mem_Hbar _
  · rw [← hb1]; exact hM n h1
  · rw [← hb2]; exact hM n' h2
  · rw [← hb1, ← hb2]; exact hd

/-- Every dyadic lattice circle of radius `2^{-k}` is an enumerated folded circle. -/
theorem exists_fullIndex_lpt (n : ℕ) (a b : ℤ) (k : ℕ) :
    ∃ i, fullIndex i = (lpt n a b, radius k) := by
  obtain ⟨i, hi⟩ := fullIndex_surj n (lpt n a b) 1 one_pos k
  refine ⟨i, ?_⟩
  rw [hi, dyadicRoundC_lpt le_rfl]
  congr 1
  simp [radius, inv_pow]

/-- **`C1` depends only on the circle coordinates, up to an additive constant.** -/
theorem C1_of_coordsFull_eq_add {x y : FieldSample} {c : ℝ}
    (h : ∀ i, coordsFull y i = coordsFull x i + c) (hx : C1 x) : C1 y := by
  have hr : ∀ n a b k, raw y (lpt n a b) k = raw x (lpt n a b) k + c := by
    intro n a b k
    obtain ⟨i, hi⟩ := exists_fullIndex_lpt n a b k
    have := h i
    simp only [coordsFull, hi] at this
    exact this
  intro k M e
  obtain ⟨j, hj⟩ := hx k M e
  refine ⟨j, fun n a b n' a' b' h1 h2 h3 h4 h5 => ?_⟩
  rw [hr, hr, add_sub_add_right_eq_sub]
  exact hj n a b n' a' b' h1 h2 h3 h4 h5

/-- `fromC g` has circle coordinates `g` when `g` only depends on the enumerated circle. -/
theorem coordsFull_fromC_of_consistent {g : ℕ → ℝ}
    (hg : ∀ i j, foldedCircle (fullIndex i).1 (fullIndex i).2 =
      foldedCircle (fullIndex j).1 (fullIndex j).2 → g i = g j) :
    coordsFull (E1.fromC g) = g := by
  classical
  funext i
  have h : ∃ j, foldedCircle (fullIndex j).1 (fullIndex j).2 =
      foldedCircle (fullIndex i).1 (fullIndex i).2 := ⟨i, rfl⟩
  simp only [coordsFull, E1.fromC, h, ↓reduceDIte]
  exact hg _ _ (Nat.find_spec h)

/-- **`CCGoodAt` passes along a constant offset of `avgReg`.** -/
theorem ccGoodAt_of_avgReg_shift {x y : FieldSample} {ψ : ℂ → ℂ} {c : ℝ}
    (h : ∀ j w, avgReg x j w = avgReg y j w + c) {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hg : CCGoodAt y ψ μ) : CCGoodAt x ψ μ := by
  obtain ⟨hint, L, hL⟩ := hg
  have e : ∀ j, (fun w => avgReg x j w) = fun w => avgReg y j w + c := fun j => funext (h j)
  refine ⟨fun j => by rw [e j]; exact (hint j).add (integrable_const c),
    L + ∫ _, c ∂(μ.map ψ), ?_⟩
  refine (hL.add_const _).congr fun j => ?_
  rw [e j, integral_add (hint j) (integrable_const c)]

/-- **`CCGoodAt` is a measurable condition on the parameter** of a reading `Vp`. -/
theorem measurableSet_ccGoodAt {α : Type} [MeasurableSpace α] {Vp : α → ℝ → ℝ}
    (hVc : ∀ b, Continuous (Vp b)) (hV0 : ∀ b, Vp b 0 = 0)
    (hVm : ∀ s, Measurable fun b => Vp b s) {t : ℝ} (ht : 0 < t) {Y : α → FieldSample}
    (hY : Measurable Y) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    MeasurableSet {b | CCGoodAt (Y b) (revMapInv (Vp b) t) μ} := by
  have hR := measurable_revMapInv_param hVc hV0 hVm ht
  set F : ℕ → α × ℂ → ℝ := fun j p => avgReg (Y p.1) j (revMapInv (Vp p.1) t p.2) with hFd
  have hF : ∀ j, Measurable (F j) := fun j =>
    (measurable_avgReg j).comp ((hY.comp measurable_fst).prodMk (hR.comp measurable_swap))
  have hsl : ∀ b j, Measurable fun w => avgReg (Y b) j w := fun b j =>
    (measurable_avgReg j).comp (measurable_const.prodMk measurable_id)
  have hψ : ∀ b, Measurable (revMapInv (Vp b) t) := measurable_revMapInv_slice hR
  have hI : ∀ b j, Integrable (fun w => avgReg (Y b) j w) (μ.map (revMapInv (Vp b) t)) ↔
      Integrable (fun z => F j (b, z)) μ := fun b j =>
    integrable_map_measure (hsl b j).aestronglyMeasurable (hψ b).aemeasurable
  have hE : ∀ b j, ∫ w, avgReg (Y b) j w ∂(μ.map (revMapInv (Vp b) t)) =
      ∫ z, F j (b, z) ∂μ := fun b j =>
    integral_map (hψ b).aemeasurable (hsl b j).aestronglyMeasurable
  have e : {b | CCGoodAt (Y b) (revMapInv (Vp b) t) μ} =
      (⋂ j, {b | Integrable (fun z => F j (b, z)) μ}) ∩
        {b | ∃ L, Tendsto (fun j => ∫ z, F j (b, z) ∂μ) atTop (𝓝 L)} := by
    ext b
    simp only [CCGoodAt, mem_ofPred_eq, mem_inter_iff, mem_iInter, hI, hE]
  rw [e]
  refine (MeasurableSet.iInter fun j => ?_).inter ?_
  · have hj : {b | Integrable (fun z => F j (b, z)) μ} =
        {b | ∫⁻ z, ‖F j (b, z)‖ₑ ∂μ < ∞} := by
      ext b
      simp only [mem_ofPred_eq]
      exact ⟨fun h => h.2,
        fun h => ⟨((hF j).comp measurable_prodMk_left).aestronglyMeasurable, h⟩⟩
    rw [hj]
    exact measurableSet_lt (hF j).enorm.lintegral_prod_right' measurable_const
  · exact StronglyMeasurable.measurableSet_exists_tendsto fun j =>
      (hF j).stronglyMeasurable.integral_prod_right'

/-- **The `CInv` candidate at a dyadic folded circle missing the time-reversed hull**, for an
arbitrary field (the field-free part of `zipFld_apply_eq_CInv`). -/
theorem coordChange_revMapInv_eq_CInv_fc {α : Type} [MeasurableSpace α] {Vp : α → ℝ → ℝ}
    (hVc : ∀ b, Continuous (Vp b)) (hV0 : ∀ b, Vp b 0 = 0) {t : ℝ} (ht : 0 < t) (Q : ℝ)
    (y : FieldSample) (e : α) (i : ℕ)
    (hnull : foldedCircle (fullIndex i).1 (fullIndex i).2
      (fwdHull (ArcDriver.trev (Vp e) t) t) = 0) :
    coordChange y (revMapInv (Vp e) t) Q (foldedCircle (fullIndex i).1 (fullIndex i).2) =
      CInv Vp t Q (foldedCircle (fullIndex i).1 (fullIndex i).2) (coordsFull y, e) := by
  set σ : Measure ℂ := foldedCircle (fullIndex i).1 (fullIndex i).2 with hσdef
  show evalReg y (σ.map (revMapInv (Vp e) t)) +
      Q * ∫ z, Real.log ‖deriv (revMapInv (Vp e) t) z‖ ∂σ =
    evalReg (E1.fromC (coordsFull y)) (σ.map (revMapInv (Vp e) t)) +
      Q * ∫ z, Real.log ‖DInv Vp t (z, e)‖ ∂σ
  congr 1
  · rw [evalReg_congr_full (E1.coordsFull_fromC y)]
  · congr 1
    refine integral_congr_ae ?_
    have hHull : ∀ᵐ z ∂σ, z ∉ fwdHull (ArcDriver.trev (Vp e) t) t := by
      rw [ae_iff]
      simpa using hnull
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H (fullIndex i).1
      (UnzipFull.fullIndex_radius_pos i), hHull] with z hzH hzHull
    rw [DInv_eq (t := t) (Vp := Vp) hVc hV0 ht e ⟨hzH, hzHull⟩]

end Cor15Group
end QuantumZipper

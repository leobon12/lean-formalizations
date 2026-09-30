import QuantumZipper.Proofs.Zipper.MeasUnzipZip
import QuantumZipper.Proofs.Zipper.MeasUnzipDrive
import QuantumZipper.Proofs.Zipper.E6LocAbsOut
import QuantumZipper.Proofs.Zipper.E6LocAbsBasic
import QuantumZipper.Proofs.GFF.CircleContinuity

/-!
# LOCRICH-COMAP (2): the zipper output read from the local data, given time and scale

Theorem 1.3, node E6 under D25. The field enters the measurable expression `MeasUnzip.outJ` of the
zipper output only through the regularized circle averages `avgReg x k` at the points
`f_τ⁻¹(u)`, `u` in the support of the rescaled test measures. Near `0` these averages are
read off the rich local data `locFieldFull R' x`:

* `locField R' d`: the field whose raw value at each `coordsFull` circle inside `closedBall 0 R'`
  is the corresponding coordinate of `d` (junk `0` at all other measures); it is a measurable
  function of `d` (`measurable_locField`), and `avgReg (locField R' (locFieldFull R' x)) k z =
  avgReg x k z` for `‖z‖ + 3 ≤ R'` (`avgReg_locField`).
* `locRich_zipLenDown_eq_loc`: if the flow `f_τ⁻¹` maps `ℍ ∩ closedBall 0 (aR + 3)` into
  `ball 0 (R' − 3)`, the output `locRich R (zipLenDown γ ℓ (x, Wof f))` equals `outLoc`, a
  jointly measurable function of the local field data, the driver path, the hitting time `τ` and
  the scale `a` (`measurable_outLoc`).

Own elementary bookkeeping (the paper, Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the
locality without proof).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.E6

open D3Plus MeasUnzip CharFun

/-! ## The localized field -/

open Classical in
/-- The field read off the rich local data: at a `coordsFull` circle inside `closedBall 0 R'`
the corresponding coordinate of `d`, junk `0` elsewhere. -/
def locField (R' : ℕ) (d : (ℕ → ℝ) × (TestFun H → ℝ)) : FieldSample := fun μ =>
  if h : ∃ i, inBallFull R' i ∧
      foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 = μ then
    d.1 h.choose else 0

theorem measurable_locField (R' : ℕ) : Measurable (locField R') := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : ∃ i, inBallFull R' i ∧
      foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 = μ
  · simp only [locField, dif_pos h]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [locField, dif_neg h]
    exact measurable_const

theorem locField_circle (R' : ℕ) (x : FieldSample) {i : ℕ} (hi : inBallFull R' i) :
    locField R' (locFieldFull R' x)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      x (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) := by
  have h : ∃ j, inBallFull R' j ∧
      foldedCircle (CoordsFull.fullIndex j).1 (CoordsFull.fullIndex j).2 =
        foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 := ⟨i, hi, rfl⟩
  simp only [locField, dif_pos h, locFieldFull, if_pos h.choose_spec.1, CoordsFull.coordsFull]
  rw [h.choose_spec.2]

/-- **The regularized averages of the localized field** agree with those of `x` at points with
`‖z‖ + 3 ≤ R'`. -/
theorem avgReg_locField {R' : ℕ} (x : FieldSample) (k : ℕ) {z : ℂ} (hz : ‖z‖ + 3 ≤ R') :
    avgReg (locField R' (locFieldFull R' x)) k z = avgReg x k z := by
  unfold avgReg
  congr 1
  funext n
  obtain ⟨i, hi⟩ := CoordsFull.fullIndex_surj n z 1 one_pos k
  have hr : radius k = ((1 : ℤ) : ℝ) / (2 : ℝ) ^ k := radius_eq_one_div k
  have hin : inBallFull R' i := by
    unfold inBallFull
    rw [hi]
    have h1 := CircleCont.norm_dyadicRoundC_sub_le n z
    have h2 : (1 : ℝ) / 2 ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have h3 : ((1 : ℤ) : ℝ) / (2 : ℝ) ^ k ≤ 1 := by rw [← hr]; exact RegCont.radius_le_one k
    have h4 := norm_sub_norm_le (dyadicRoundC n z) z
    simp only at h3 ⊢
    linarith
  have e : foldedCircle (dyadicRoundC n z) (radius k) =
      foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 := by
    rw [hi, hr]
  rw [e, locField_circle R' x hin]

/-! ## The unzipped field of the localized field -/

variable {T : ℝ} (hT : 0 ≤ T)

theorem unzRawJ_congr_avg {γ κ : ℝ} {μ : Measure ℂ} {f : C(Icc (0 : ℝ) T, ℝ)}
    {x x' : FieldSample} {s : ℝ}
    (h : ∀ᵐ u ∂μ, ∀ k, avgReg x k (flowJ hT κ (f, (s, u))) =
      avgReg x' k (flowJ hT κ (f, (s, u)))) :
    unzRawJ hT γ κ μ ((f, x), s) = unzRawJ hT γ κ μ ((f, x'), s) := by
  unfold unzRawJ
  have : (fun k => ∫ u, avgReg x k (flowJ hT κ (f, (s, u))) ∂μ) =
      fun k => ∫ u, avgReg x' k (flowJ hT κ (f, (s, u))) ∂μ :=
    funext fun k => integral_congr_ae (h.mono fun u hu => hu k)
  rw [this]

/-- Raw values at folded circles of the unzipped fields of `x` and of its localization agree when
the flow maps `ℍ ∩ closedBall 0 b` into `ball 0 (R' − 3)` and the circle lies in `closedBall 0 b`. -/
theorem ufJ_locField_circle {γ κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : FieldSample) {R' : ℕ} {b : ℝ}
    (hflow : ∀ u ∈ H, ‖u‖ ≤ b → ‖fwdMapInv (Wof κ T hT f) s u‖ + 3 ≤ R')
    {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hcb : ‖c‖ + ρ ≤ b) :
    ufJ hT γ κ ((f, locField R' (locFieldFull R' x)), s) (foldedCircle c ρ) =
      ufJ hT γ κ ((f, x), s) (foldedCircle c ρ) := by
  unfold ufJ
  split_ifs with hν
  · apply unzRawJ_congr_avg
    have hH : ∀ᵐ u ∂(foldedCircle c ρ), u ∈ H := TwoPoint.foldedCircle_ae_mem_H c hρ
    have hB : ∀ᵐ u ∂(foldedCircle c ρ), u ∈ CircleFubini.ballH b :=
      ae_iff.2 (CircleFubini.foldedCircle_support hρ.le hcb)
    filter_upwards [hH, hB] with u hu hub k
    have hfl : flowJ hT κ (f, (s, u)) = fwdMapInv (Wof κ T hT f) s u := by
      simp only [flowJ, if_pos (And.intro hf (show (s, u) ∈ KT T from ⟨hs, hu⟩))]
    rw [hfl]
    exact avgReg_locField x k (hflow u hu (mem_closedBall_zero_iff.1 hub.1))
  · rfl

/-- The regularized averages of the unzipped fields of `x` and of its localization agree at
points `w` with `‖w‖ + 3 ≤ b`. -/
theorem avgReg_ufJ_locField {γ κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : FieldSample) {R' : ℕ} {b : ℝ}
    (hflow : ∀ u ∈ H, ‖u‖ ≤ b → ‖fwdMapInv (Wof κ T hT f) s u‖ + 3 ≤ R') (k : ℕ) {w : ℂ}
    (hw : ‖w‖ + 3 ≤ b) :
    avgReg (ufJ hT γ κ ((f, locField R' (locFieldFull R' x)), s)) k w =
      avgReg (ufJ hT γ κ ((f, x), s)) k w := by
  unfold avgReg
  congr 1
  funext n
  refine ufJ_locField_circle hT hf hs x hflow (radius_pos k) ?_
  have h1 := CircleCont.norm_dyadicRoundC_sub_le n w
  have h2 : (1 : ℝ) / 2 ^ n ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have h3 := RegCont.radius_le_one k
  have h4 := norm_sub_norm_le (dyadicRoundC n w) w
  linarith

/-- Raw values of the rescaled unzipped fields of `x` and of its localization agree at measures
carried by `ballH r`, when the flow maps `ℍ ∩ closedBall 0 (a r + 3)` into `ball 0 (R' − 3)`. -/
theorem rescale_ufJ_locField_eq {γ κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : FieldSample) {R' : ℕ} {Q a r : ℝ} (ha : 0 < a)
    (hflow : ∀ u ∈ H, ‖u‖ ≤ a * r + 3 → ‖fwdMapInv (Wof κ T hT f) s u‖ + 3 ≤ R')
    {μ : Measure ℂ} (hμ : μ (CircleFubini.ballH r)ᶜ = 0) :
    rescale (ufJ hT γ κ ((f, locField R' (locFieldFull R' x)), s)) Q a μ =
      rescale (ufJ hT γ κ ((f, x), s)) Q a μ := by
  simp only [rescale, coordChange]
  refine congrArg (· + _) ?_
  unfold evalReg
  have hm : Measurable fun z : ℂ => (a : ℂ) * z := measurable_const.mul measurable_id
  have hB : ∀ᵐ u ∂(μ.map fun z : ℂ => (a : ℂ) * z), u ∈ closedBall (0 : ℂ) (a * r) := by
    refine (ae_map_iff hm.aemeasurable (p := fun u => u ∈ closedBall (0 : ℂ) (a * r))
      measurableSet_closedBall).2 ?_
    have hae : ∀ᵐ u ∂μ, u ∈ CircleFubini.ballH r := ae_iff.2 hμ
    filter_upwards [hae] with u hu
    have hu1 : ‖u‖ ≤ r := mem_closedBall_zero_iff.1 hu.1
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
    exact mul_le_mul_of_nonneg_left hu1 ha.le
  have : (fun k => ∫ w, avgReg (ufJ hT γ κ ((f, locField R' (locFieldFull R' x)), s)) k w
      ∂(μ.map fun z : ℂ => (a : ℂ) * z)) =
      fun k => ∫ w, avgReg (ufJ hT γ κ ((f, x), s)) k w ∂(μ.map fun z : ℂ => (a : ℂ) * z) :=
    funext fun k => integral_congr_ae (hB.mono fun w hw =>
      avgReg_ufJ_locField hT hf hs x hflow k (by linarith [mem_closedBall_zero_iff.1 hw]))
  rw [this]

/-- The rich local data of the rescaled unzipped fields of `x` and of its localization agree. -/
theorem locFieldFull_rescale_ufJ_locField {γ κ : ℝ} {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ PZ hT κ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (x : FieldSample) {R R' : ℕ} {Q a : ℝ} (ha : 0 < a)
    (hflow : ∀ u ∈ H, ‖u‖ ≤ a * R + 3 → ‖fwdMapInv (Wof κ T hT f) s u‖ + 3 ≤ R') :
    locFieldFull R (rescale (ufJ hT γ κ ((f, locField R' (locFieldFull R' x)), s)) Q a) =
      locFieldFull R (rescale (ufJ hT γ κ ((f, x), s)) Q a) := by
  have key : ∀ μ : Measure ℂ, μ (CircleFubini.ballH R)ᶜ = 0 →
      rescale (ufJ hT γ κ ((f, locField R' (locFieldFull R' x)), s)) Q a μ =
        rescale (ufJ hT γ κ ((f, x), s)) Q a μ :=
    fun μ hμ => rescale_ufJ_locField_eq hT hf hs x ha hflow hμ
  generalize locField R' (locFieldFull R' x) = L at key ⊢
  unfold locFieldFull
  refine Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)
  · simp only
    split_ifs with h
    · have hr0 : (0 : ℝ) ≤ (CoordsFull.fullIndex i).2 := by
        simp only [CoordsFull.fullIndex]; positivity
      exact key _ (CircleFubini.foldedCircle_support hr0 h)
    · rfl
  · simp only
    split_ifs with h
    · unfold pairRaw
      have e1 := key _ (withDensity_ballH_compl h 1)
      have e2 := key _ (withDensity_ballH_compl h (-1))
      simp only [one_mul, neg_one_mul] at e1 e2
      rw [e1, e2]
    · rfl

/-! ## The output read from the local data -/

variable (γ κ : ℝ) (R R' : ℕ)

/-- The zipper output as a function of the local field data `p.1.1`, the driver window `p.1.2`
(read through a path extraction `π`), the hitting time `p.2.1` and the scale `p.2.2`. -/
def outLoc (π : (ℝ≥0 → ℝ) → C(Icc (0 : ℝ) T, ℝ)) (p : FullData × ℝ × ℝ) : FullData :=
  (locFieldFull R (rescale (ufJ hT γ κ ((π p.1.2, locField R' p.1.1), p.2.1)) (Qc γ) p.2.2),
    drvJ hT κ R (π p.1.2, p.2.1, p.2.2))

theorem measurable_outLoc {π : (ℝ≥0 → ℝ) → C(Icc (0 : ℝ) T, ℝ)} (hπ : Measurable π) :
    Measurable (outLoc hT γ κ R R' π) := by
  have hπ' : Measurable fun p : FullData × ℝ × ℝ => π p.1.2 :=
    hπ.comp (measurable_snd.comp measurable_fst)
  have hy : Measurable fun p : FullData × ℝ × ℝ =>
      ufJ hT γ κ ((π p.1.2, locField R' p.1.1), p.2.1) :=
    (measurable_ufJ hT γ κ).comp ((hπ'.prodMk ((measurable_locField R').comp
      (measurable_fst.comp measurable_fst))).prodMk (measurable_fst.comp measurable_snd))
  have h1 := (measurable_locFieldFull_rescale hy (Qc γ) R).comp
    (measurable_id.prodMk (measurable_snd.comp measurable_snd))
  have h2 := (measurable_drvJ hT κ R).comp (hπ'.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (measurable_snd.comp measurable_snd)))
  exact h1.prodMk h2

variable {γ κ R R'}

end QuantumZipper.E6

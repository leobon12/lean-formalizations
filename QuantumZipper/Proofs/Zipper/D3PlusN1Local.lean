import QuantumZipper.Proofs.Zipper.D3PlusLocal
import QuantumZipper.Proofs.Zipper.LocRichBasic
import QuantumZipper.Proofs.Section5.Prop16MeasArea

/-!
# D3⁺(i), node N1 (part 1): locality of the local canonical data

If two field samples `y, y'` have the same raw values at the dyadic folded circles inside
`ball 0 r` (`AgreeNear y y' r`), then

* `isVagueLimitOn_halfDisc_of_agree`, `qAreaMeasureOn_halfDisc_congr`,
  `scaleParamOn_halfDisc_congr`: their local area measures and local scales on `halfDisc r`
  coincide (the area approximations agree on every compact subset of `halfDisc r` for large `k`;
  the local vague limit is unique, `LocalRule.qAreaMeasureOn_eq`);
* `locFieldFull_rescale_congr`: the rich local data (D25) of their rescalings by `a > 0` with
  `a R < r` coincide (every coordinate is read at a measure carried by `closedBall 0 R`).

Own elementary arguments (measure-theoretic plumbing; AGENT_GUIDE cost rule), extending
`D3PlusLocal.lean`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

theorem AgreeNear.symm' {y y' : FieldSample} {r : ℝ} (h : AgreeNear y y' r) : AgreeNear y' y r :=
  fun n k z hz => (h n k z hz).symm

/-- **Local vague limits transfer along `AgreeNear`.** -/
theorem isVagueLimitOn_halfDisc_of_agree {γ r : ℝ} {y y' : FieldSample} (hag : AgreeNear y y' r)
    {m : Measure ℂ} (hm : IsVagueLimitOn (halfDisc r) (areaApprox γ y) m) :
    IsVagueLimitOn (halfDisc r) (areaApprox γ y') m := by
  obtain ⟨h1, h2, h3⟩ := hm
  refine ⟨h1, h2, fun f hf hfc hfU => ?_⟩
  refine (h3 f hf hfc hfU).congr' ?_
  have hKc : IsClosed (tsupport f) := isClosed_tsupport f
  obtain ⟨ρ, hρ, hKρ⟩ := exists_lt_subset_ball hKc (hfU.trans inter_subset_left)
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt (sub_pos.2 hρ)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hKm : MeasurableSet (tsupport f) := hKc.measurableSet
  have hvan : ∀ z, z ∉ tsupport f → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hmeq : (areaApprox γ y k).restrict (tsupport f) =
      (areaApprox γ y' k).restrict (tsupport f) := by
    rw [areaApprox, areaApprox, restrict_withDensity hKm, restrict_withDensity hKm]
    refine withDensity_congr_ae ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun z hz => ?_))
    have hzρ := hKρ hz
    rw [Metric.mem_ball, dist_zero_right] at hzρ
    have hzk : ‖z‖ + radius k < r := by linarith [hK k hk]
    simp only [avgReg_congr hag hzk]
  have e1 : ∫ z, f z ∂(areaApprox γ y k) = ∫ z in tsupport f, f z ∂(areaApprox γ y k) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
  have e2 : ∫ z, f z ∂(areaApprox γ y' k) = ∫ z in tsupport f, f z ∂(areaApprox γ y' k) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
  rw [e1, e2, hmeq]

theorem exists_isVagueLimitOn_halfDisc_iff {γ r : ℝ} {y y' : FieldSample}
    (hag : AgreeNear y y' r) :
    (∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y) m) ↔
      ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y') m :=
  ⟨fun ⟨m, hm⟩ => ⟨m, isVagueLimitOn_halfDisc_of_agree hag hm⟩,
    fun ⟨m, hm⟩ => ⟨m, isVagueLimitOn_halfDisc_of_agree hag.symm' hm⟩⟩

/-- **The local area measure on `halfDisc r` only depends on the raw values near `0`.** -/
theorem qAreaMeasureOn_halfDisc_congr {γ r : ℝ} {y y' : FieldSample} (hag : AgreeNear y y' r) :
    qAreaMeasureOn γ y (halfDisc r) = qAreaMeasureOn γ y' (halfDisc r) := by
  by_cases h : ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y) m
  · obtain ⟨m, hm⟩ := h
    rw [LocalRule.qAreaMeasureOn_eq (isOpen_halfDisc r) hm,
      LocalRule.qAreaMeasureOn_eq (isOpen_halfDisc r) (isVagueLimitOn_halfDisc_of_agree hag hm)]
  · have h' : ¬ ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y') m := fun h' =>
      h ((exists_isVagueLimitOn_halfDisc_iff hag).2 h')
    rw [Prop16Area.Meas.qAreaMeasureOn_of_not h, Prop16Area.Meas.qAreaMeasureOn_of_not h']

theorem scaleParamOn_halfDisc_congr {γ r : ℝ} {y y' : FieldSample} (hag : AgreeNear y y' r) :
    scaleParamOn γ y (halfDisc r) = scaleParamOn γ y' (halfDisc r) := by
  simp only [scaleParamOn, qAreaMeasureOn_halfDisc_congr hag]

/-- A signed-part density measure of a test function supported in `closedBall 0 R` is carried
by `closedBall 0 R`. -/
theorem withDensity_compl_closedBall {ρ : ℂ → ℝ} {R : ℝ}
    (hρ : tsupport ρ ⊆ Metric.closedBall (0 : ℂ) R) (σ : ℝ) :
    (volume.withDensity fun z => ENNReal.ofReal (σ * ρ z)) (Metric.closedBall 0 R)ᶜ = 0 := by
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet.compl]
  have h0 : ∀ z ∈ (Metric.closedBall (0 : ℂ) R)ᶜ, ENNReal.ofReal (σ * ρ z) = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hρ h))]; simp
  rw [setLIntegral_congr_fun Metric.isClosed_closedBall.measurableSet.compl h0]
  simp

/-- **Rich local data of rescalings only depend on the raw values near `0`.** -/
theorem locFieldFull_rescale_congr {y y' : FieldSample} {r : ℝ} (hag : AgreeNear y y' r)
    {Q a : ℝ} (ha : 0 < a) {R : ℕ} (haR : a * R < r) :
    locFieldFull R (rescale y Q a) = locFieldFull R (rescale y' Q a) := by
  classical
  unfold locFieldFull
  refine Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)
  · simp only
    split_ifs with h
    · have hr0 : (0 : ℝ) ≤ (CoordsFull.fullIndex i).2 := by
        simp only [CoordsFull.fullIndex]; positivity
      have hsupp := CircleFubini.foldedCircle_support hr0 h
      exact rescale_congr hag ha (measure_mono_null (compl_subset_compl.2 inter_subset_left) hsupp)
        haR
    · rfl
  · simp only
    split_ifs with h
    · have h1 := withDensity_compl_closedBall h 1
      have h2 := withDensity_compl_closedBall h (-1)
      simp only [one_mul, neg_one_mul] at h1 h2
      simp only [pairRaw]
      rw [rescale_congr hag ha h1 haR, rescale_congr hag ha h2 haR]
    · rfl

end D3Plus
end QuantumZipper

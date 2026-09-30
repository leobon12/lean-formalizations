import QuantumZipper.Proofs.Zipper.D3PlusStmt
import QuantumZipper.Proofs.LQG.AtomlessUncond

/-!
# D3⁺ consumers: the global scale equals the local scale when the latter is small

Decision D23: D3⁺ is read locally (`scaleParamOn`/`canonicalOn` on `halfDisc r`), while E5's
`canonConfig` uses the global `scaleParam`/`canonical`. `scaleParam_eq_scaleParamOn_of_lt` is the
deterministic step of that conversion: if the global area measure of `y` and the local area measure
of `y'` on `halfDisc r` agree on the half-balls `ball 0 b ∩ ℍ`, `b ≤ r`, and the local scale of
`y'` lies in `(0, r)`, then the global scale of `y` is the same number. (Own elementary argument:
the defining sets of the two infima agree below `r`.)

`locField_canonical_eq_canonicalOn` is the field-level conversion: if `y` and `y'` have the same
raw values at the dyadic folded circles `foldedCircle (dyadicRoundC n z) (radius k)` lying in
`ball 0 r` (a countable family, so an almost-sure hypothesis in E5), the global area measure of `y`
exists, and the local scale `s` of `y'` satisfies `0 < s` and `s (R + 1) < r`, then
`scaleParam γ y = s` and `locField R (canonical γ y) = locField R (canonicalOn γ y' (halfDisc r))`.
Route (own elementary argument): `avgReg` reads only raw values at such circles
(`avgReg_congr`), so `evalReg` agrees on measures carried by `closedBall 0 ρ`, `ρ < r`
(`evalReg_congr`), hence the rescaled fields agree on `locField R` (`locField_rescale_congr`), and
the area approximations agree on compact subsets of `halfDisc r` for large `k`
(`qAreaMeasureOn_eq_restrict_of_agree`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

theorem scaleParam_eq_scaleParamOn_of_lt {γ r : ℝ} {y y' : FieldSample}
    (hloc : ∀ b : ℝ, b ≤ r → qAreaMeasure γ y (Metric.ball 0 b ∩ H) =
      qAreaMeasureOn γ y' (halfDisc r) (Metric.ball 0 b ∩ H))
    (hpos : 0 < scaleParamOn γ y' (halfDisc r)) (hlt : scaleParamOn γ y' (halfDisc r) < r) :
    scaleParam γ y = scaleParamOn γ y' (halfDisc r) := by
  set Sg := {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ y (Metric.ball 0 a ∩ H)} with hSg
  set Sl := {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasureOn γ y' (halfDisc r) (Metric.ball 0 a ∩ H)}
    with hSl
  have hs : scaleParamOn γ y' (halfDisc r) = sInf Sl := rfl
  have hg : scaleParam γ y = sInf Sg := rfl
  rw [hs] at hpos hlt ⊢
  rw [hg]
  have hSlne : Sl.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty] at hpos
    exact lt_irrefl _ hpos
  have hbl : BddBelow Sl := ⟨0, fun a ha => ha.1.le⟩
  have hbg : BddBelow Sg := ⟨0, fun a ha => ha.1.le⟩
  -- elements of `Sl` below `r` are in `Sg`
  have hlg : ∀ a ∈ Sl, a ≤ r → a ∈ Sg := fun a ha har => ⟨ha.1, by rw [hloc a har]; exact ha.2⟩
  have hgl : ∀ a ∈ Sg, a ≤ r → a ∈ Sl := fun a ha har => ⟨ha.1, by rw [← hloc a har]; exact ha.2⟩
  obtain ⟨a₀, ha₀, ha₀r⟩ := exists_lt_of_csInf_lt hSlne hlt
  have hSgne : Sg.Nonempty := ⟨a₀, hlg a₀ ha₀ ha₀r.le⟩
  refine le_antisymm ?_ (le_csInf hSgne fun b hb => ?_)
  · -- `sInf Sg ≤ s`
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨b, hb, hbε⟩ := exists_lt_of_csInf_lt hSlne (lt_min (lt_add_of_pos_right (sInf Sl) hε) hlt)
    exact (csInf_le hbg (hlg b hb (hbε.trans_le (min_le_right _ _)).le)).trans_lt
      (hbε.trans_le (min_le_left _ _))
  · -- `s ≤ b` for `b ∈ Sg`
    by_cases hbr : b ≤ r
    · exact csInf_le hbl (hgl b hb hbr)
    · exact hlt.le.trans (not_le.1 hbr).le

/-! ## Field-level locality -/

/-- Raw values of `y` and `y'` agree at the dyadic folded circles inside `ball 0 r`. -/
def AgreeNear (y y' : FieldSample) (r : ℝ) : Prop :=
  ∀ (n k : ℕ) (z : ℂ), ‖dyadicRoundC n z‖ + radius k < r →
    y (foldedCircle (dyadicRoundC n z) (radius k)) = y' (foldedCircle (dyadicRoundC n z) (radius k))

theorem limUnder_congr_eventually {f g : ℕ → ℝ} (h : f =ᶠ[atTop] g) :
    limUnder atTop f = limUnder atTop g := by
  simp only [limUnder]
  rw [Filter.map_congr h]

theorem avgReg_congr {y y' : FieldSample} {r : ℝ} (hag : AgreeNear y y' r) {k : ℕ} {z : ℂ}
    (hz : ‖z‖ + radius k < r) : avgReg y k z = avgReg y' k z := by
  unfold avgReg
  apply limUnder_congr_eventually
  have hc : Tendsto (fun n => ‖dyadicRoundC n z‖ + radius k) atTop (𝓝 (‖z‖ + radius k)) :=
    ((continuous_norm.tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)).add_const _
  filter_upwards [hc.eventually (gt_mem_nhds hz)] with n hn
  exact hag n k z hn

theorem evalReg_congr {y y' : FieldSample} {r : ℝ} (hag : AgreeNear y y' r) {ν : Measure ℂ}
    {ρ : ℝ} (hν : ν (Metric.closedBall 0 ρ)ᶜ = 0) (hρ : ρ < r) : evalReg y ν = evalReg y' ν := by
  unfold evalReg
  apply limUnder_congr_eventually
  obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt (sub_pos.2 hρ)
  filter_upwards [eventually_ge_atTop K] with k hk
  refine integral_congr_ae ?_
  have hae : ∀ᵐ w ∂ν, w ∈ Metric.closedBall (0 : ℂ) ρ := ae_iff.2 hν
  filter_upwards [hae] with w hw
  apply avgReg_congr hag
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  linarith [hK k hk]

theorem rescale_congr {y y' : FieldSample} {r : ℝ} (hag : AgreeNear y y' r) {Q a : ℝ} (ha : 0 < a)
    {μ : Measure ℂ} {s : ℝ} (hμ : μ (Metric.closedBall 0 s)ᶜ = 0) (hs : a * s < r) :
    rescale y Q a μ = rescale y' Q a μ := by
  simp only [rescale, coordChange]
  congr 1
  refine evalReg_congr hag (ρ := a * s) ?_ hs
  have hm : Measurable fun z : ℂ => (a : ℂ) * z := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm Metric.isClosed_closedBall.measurableSet.compl]
  refine measure_mono_null (fun z hz => ?_) hμ
  simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hz ⊢
  exact lt_of_mul_lt_mul_left hz ha.le

theorem locField_rescale_congr {y y' : FieldSample} {r : ℝ} (hag : AgreeNear y y' r) {Q a : ℝ}
    (ha : 0 < a) {R : ℕ} (haR : a * R < r) :
    TV.locField R (rescale y Q a) = TV.locField R (rescale y' Q a) := by
  funext n
  unfold TV.locField
  split_ifs with h
  · have hr0 : (0 : ℝ) ≤ radius (Factorization.dyadicIndex n).2 := by unfold radius; positivity
    have hsupp := CircleFubini.foldedCircle_support hr0 h
    exact rescale_congr hag ha (measure_mono_null (compl_subset_compl.2 inter_subset_left) hsupp)
      haR
  · rfl

/-- **Area locality.** If the area approximations of `y` converge vaguely on `ℍ` to `μ` and `y`,
`y'` agree near `0`, then the local area measure of `y'` on `halfDisc r` is `μ|_{halfDisc r}`. -/
theorem qAreaMeasureOn_eq_restrict_of_agree {γ r : ℝ} {y y' : FieldSample} (hag : AgreeNear y y' r)
    {μ : Measure ℂ} (hy : IsVagueLimitOn H (areaApprox γ y) μ) :
    qAreaMeasureOn γ y' (halfDisc r) = μ.restrict (halfDisc r) := by
  have hU := isOpen_halfDisc r
  obtain ⟨h1, h2, h3⟩ := AtomlessUncond.isVagueLimitOn_restrict hU (halfDisc_subset_H r) hy
  refine LocalRule.qAreaMeasureOn_eq hU ⟨h1, h2, fun f hf hfc hfU => ?_⟩
  refine (h3 f hf hfc hfU).congr' ?_
  -- the approximations agree on `tsupport f` for large `k`
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

end D3Plus
end QuantumZipper

import QuantumZipper.Proofs.Thm18.G3ConcreteField
import QuantumZipper.Proofs.LQG.LocalRule

/-!
# G3 fidelity F2 (part 1): folded circles against real discs, and `avgReg` of the region fields

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 70–71): the boundary lengths used by
the concrete G3 scheme are read from the region fields (`G3ConcreteField.lean`). Here, for a real
centre `t`, we decide exactly which folded circles `foldedCircle c ρ` belong to `circIn t r`
(`‖c − t‖ + ρ < r` suffices, `r ≤ ‖c − t‖ + ρ` excludes) and to `circOut` (`rᵢ + ρ ≤ ‖c − tᵢ‖`
suffices, `‖c − t₁‖ < r₁ + ρ` with `ρ < r₁` excludes), and deduce the regularized averages of
the region and gap fields at real points off the thin shells `|‖s − t‖ − r| ≤ 2^{-k}`: they are
those of the full field inside, and `0` outside.

The only input is that the folded circle about `c` of radius `ρ` sees the distance to a real
point `t` exactly as the full circle does (`‖foldH u − t‖ = ‖u − t‖`), and that this distance
ranges over `[‖c − t‖ − ρ, ‖c − t‖ + ρ]`, both ends being attained. Own elementary arguments
(AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Fid

theorem norm_foldH_sub_real (u : ℂ) (t : ℝ) : ‖foldH u - t‖ = ‖u - t‖ := by
  unfold foldH
  split_ifs
  · rfl
  · rw [show (starRingEnd ℂ) u - (t : ℂ) = (starRingEnd ℂ) (u - t) by
      rw [map_sub, Complex.conj_ofReal]]
    exact Complex.norm_conj _

theorem circleMap_sub_real (c : ℂ) (ρ θ t : ℝ) :
    circleMap c ρ θ - t = circleMap (c - t) ρ θ := by
  simp only [circleMap]; ring

/-- The folded circle on a set of points described by their distance to a real point. -/
theorem fc_dist_apply (c : ℂ) (ρ t : ℝ) {O : Set ℝ} (hO : MeasurableSet O) :
    foldedCircle c ρ {u : ℂ | ‖u - (t : ℂ)‖ ∈ O} = (ENNReal.ofReal (2 * π))⁻¹ *
      volume ({θ | ‖circleMap c ρ θ - t‖ ∈ O} ∩ Ico 0 (2 * π)) := by
  have hA : MeasurableSet {u : ℂ | ‖u - t‖ ∈ O} :=
    (continuous_id.sub continuous_const).norm.measurable hO
  rw [foldedCircle, Measure.map_apply measurable_foldH hA]
  have hpre : foldH ⁻¹' {u : ℂ | ‖u - t‖ ∈ O} = {u : ℂ | ‖u - (t : ℂ)‖ ∈ O} := by
    ext u; simp only [mem_preimage, mem_setOf_eq, norm_foldH_sub_real]
  rw [hpre, circleUnif, Measure.smul_apply, Measure.map_apply (measurable_circleMap c ρ) hA,
    smul_eq_mul, Measure.restrict_apply ((measurable_circleMap c ρ) hA)]
  rfl

theorem fc_dist_null (c : ℂ) (ρ t : ℝ) {O : Set ℝ} (hO : MeasurableSet O)
    (h : ∀ θ, ‖circleMap c ρ θ - t‖ ∉ O) : foldedCircle c ρ {u : ℂ | ‖u - (t : ℂ)‖ ∈ O} = 0 := by
  rw [fc_dist_apply c ρ t hO]
  have : {θ | ‖circleMap c ρ θ - t‖ ∈ O} = ∅ := eq_empty_of_forall_notMem fun θ hθ => h θ hθ
  simp [this]

theorem fc_dist_pos (c : ℂ) (ρ t : ℝ) {O : Set ℝ} (hO : IsOpen O) (θ₀ : ℝ)
    (h : ‖circleMap c ρ θ₀ - t‖ ∈ O) : 0 < foldedCircle c ρ {u : ℂ | ‖u - (t : ℂ)‖ ∈ O} := by
  rw [fc_dist_apply c ρ t hO.measurableSet]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top) (ne_of_gt ?_)
  set U := {θ | ‖circleMap c ρ θ - t‖ ∈ O} with hUdef
  have hU : IsOpen U :=
    hO.preimage (((continuous_circleMap c ρ).sub continuous_const).norm)
  set θ₁ := toIcoMod Real.two_pi_pos 0 θ₀ with hθ₁
  have hθI : θ₁ ∈ Ico 0 (0 + 2 * π) := toIcoMod_mem_Ico _ _ _
  rw [zero_add] at hθI
  have hθU : θ₁ ∈ U := by
    have : circleMap c ρ θ₁ = circleMap c ρ θ₀ := by
      rw [hθ₁, toIcoMod]
      exact (periodic_circleMap c ρ).sub_zsmul_eq _
    simp only [hUdef, mem_setOf_eq, this]
    exact h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU θ₁ hθU
  have hsub : Ioo θ₁ (min (θ₁ + ε) (2 * π)) ⊆ U ∩ Ico 0 (2 * π) := by
    intro θ hθ
    refine ⟨hball ?_, hθI.1.trans hθ.1.le, hθ.2.trans_le (min_le_right _ _)⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hθ.1]
    · linarith [hθ.2.trans_le (min_le_left _ _)]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  have := hθI.2
  exact sub_pos.2 (lt_min (by linarith) this)

/-- Distances from a real point along the circle stay within `ρ` of the centre's distance. -/
theorem abs_norm_circleMap_sub_le (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (θ t : ℝ) :
    |‖circleMap c ρ θ - t‖ - ‖c - t‖| ≤ ρ := by
  rw [circleMap_sub_real]
  have h := abs_norm_sub_norm_le (circleMap (c - t) ρ θ) (c - t)
  have e : circleMap (c - t) ρ θ - (c - t) = ρ * Complex.exp (θ * Complex.I) := by
    simp only [circleMap]; ring
  rwa [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hρ] at h

/-- The farthest point of the circle from `t`. -/
theorem norm_circleMap_far (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) :
    ‖circleMap c ρ (c - t).arg - t‖ = ‖c - t‖ + ρ := by
  rw [circleMap_sub_real]
  set z := c - t
  have e : circleMap z ρ z.arg = ((‖z‖ + ρ : ℝ) : ℂ) * Complex.exp (z.arg * Complex.I) := by
    simp only [circleMap]
    push_cast
    rw [add_mul, Complex.norm_mul_exp_arg_mul_I]
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- The nearest point of the circle to `t`. -/
theorem norm_circleMap_near (c : ℂ) (ρ t : ℝ) :
    ‖circleMap c ρ ((c - t).arg + π) - t‖ = |‖c - t‖ - ρ| := by
  rw [circleMap_sub_real]
  set z := c - t
  have e : circleMap z ρ (z.arg + π) = ((‖z‖ - ρ : ℝ) : ℂ) * Complex.exp (z.arg * Complex.I) := by
    simp only [circleMap]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I, sub_mul,
      Complex.norm_mul_exp_arg_mul_I]
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem compl_closedBall_eq (t r : ℝ) :
    (closedBall (t : ℂ) r)ᶜ = {u : ℂ | ‖u - t‖ ∈ Ioi r} := by
  ext u; simp [dist_eq_norm]

theorem ball_eq (t r : ℝ) : ball (t : ℂ) r = {u : ℂ | ‖u - t‖ ∈ Iio r} := by
  ext u; simp [dist_eq_norm]

/-! ## Membership in `circIn` and `circOut` -/

theorem fc_mem_circIn {t r ρ : ℝ} (hρ : 0 < ρ) {c : ℂ} (h : ‖c - t‖ + ρ < r) :
    foldedCircle c ρ ∈ circIn t r := by
  refine ⟨c, ρ, hρ, rfl, ‖c - t‖ + ρ, h, ?_⟩
  rw [compl_closedBall_eq]
  refine fc_dist_null c ρ t measurableSet_Ioi fun θ hθ => ?_
  have := abs_norm_circleMap_sub_le c hρ.le θ t
  rw [mem_Ioi] at hθ
  linarith [le_abs_self (‖circleMap c ρ θ - t‖ - ‖c - t‖)]

theorem fc_not_mem_circIn {t r ρ : ℝ} (hρ : 0 ≤ ρ) {c : ℂ} (h : r ≤ ‖c - t‖ + ρ) :
    foldedCircle c ρ ∉ circIn t r := by
  rintro ⟨d, ρ', -, -, r', hr', hμ⟩
  rw [compl_closedBall_eq] at hμ
  have := fc_dist_pos c ρ t isOpen_Ioi (c - t).arg
    (show ‖circleMap c ρ (c - t).arg - t‖ ∈ Ioi r' by
      rw [norm_circleMap_far c hρ, mem_Ioi]; linarith)
  rw [hμ] at this
  exact lt_irrefl _ this

theorem fc_ball_null {t r ρ : ℝ} (hρ : 0 ≤ ρ) {c : ℂ} (h : r + ρ ≤ ‖c - t‖) :
    foldedCircle c ρ (ball (t : ℂ) r) = 0 := by
  rw [ball_eq]
  refine fc_dist_null c ρ t measurableSet_Iio fun θ hθ => ?_
  have := abs_norm_circleMap_sub_le c hρ θ t
  rw [mem_Iio] at hθ
  linarith [neg_abs_le (‖circleMap c ρ θ - t‖ - ‖c - t‖)]

theorem fc_mem_circOut {t₁ r₁ t₂ r₂ ρ : ℝ} (hρ : 0 < ρ) {c : ℂ} (h₁ : r₁ + ρ ≤ ‖c - t₁‖)
    (h₂ : r₂ + ρ ≤ ‖c - t₂‖) : foldedCircle c ρ ∈ circOut t₁ r₁ t₂ r₂ :=
  ⟨c, ρ, hρ, rfl, measure_union_null (fc_ball_null hρ.le h₁) (fc_ball_null hρ.le h₂)⟩

/-! ## Regularized averages of the restricted fields at real points -/

theorem avgReg_zero (k : ℕ) (z : ℂ) : avgReg (0 : FieldSample) k z = 0 := by
  unfold avgReg
  simp only [Pi.zero_apply]
  exact tendsto_const_nhds.limUnder_eq

theorem norm_ofReal_sub (s t : ℝ) : ‖(s : ℂ) - t‖ = |s - t| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem norm_sub_real_le (c : ℂ) (s t : ℝ) : ‖c - t‖ ≤ ‖c - s‖ + |s - t| := by
  rw [← norm_ofReal_sub]
  calc ‖c - t‖ = ‖(c - s) + ((s : ℂ) - t)‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _

theorem abs_sub_le_norm (c : ℂ) (s t : ℝ) : |s - t| ≤ ‖c - s‖ + ‖c - t‖ := by
  rw [← norm_ofReal_sub]
  calc ‖(s : ℂ) - t‖ = ‖-(c - s) + (c - t)‖ := by ring_nf
    _ ≤ ‖-(c - s)‖ + ‖c - t‖ := norm_add_le _ _
    _ = _ := by rw [norm_neg]

variable {y : FieldSample} {k : ℕ} {s : ℝ}

theorem avgReg_region_in {t r : ℝ} (h : |s - t| + radius k < r) :
    avgReg (restrictField (circIn t r) y) k s = avgReg y k s := by
  classical
  refine LocalRule.avgReg_congr_local k (ρ := r - |s - t| - radius k) (by linarith)
    (fun c _ hc => ?_) (GaussTK.ofReal_mem_Hbar s)
  rw [dist_eq_norm] at hc
  have := norm_sub_real_le c s t
  simp only [restrictField, if_pos (fc_mem_circIn (radius_pos k) (by linarith :
    ‖c - t‖ + radius k < r))]

theorem avgReg_region_out {t r : ℝ} (h : r < |s - t| + radius k) :
    avgReg (restrictField (circIn t r) y) k s = 0 := by
  classical
  rw [← avgReg_zero k (s : ℂ)]
  refine LocalRule.avgReg_congr_local k (ρ := |s - t| + radius k - r) (by linarith)
    (fun c _ hc => ?_) (GaussTK.ofReal_mem_Hbar s)
  rw [dist_eq_norm] at hc
  have := abs_sub_le_norm c s t
  simp only [restrictField, Pi.zero_apply, if_neg (fc_not_mem_circIn (radius_pos k).le
    (by linarith : r ≤ ‖c - t‖ + radius k))]

theorem avgReg_gap_in {t₁ r₁ t₂ r₂ : ℝ} (h₁ : r₁ + radius k < |s - t₁|)
    (h₂ : r₂ + radius k < |s - t₂|) :
    avgReg (restrictField (circOut t₁ r₁ t₂ r₂) y) k s = avgReg y k s := by
  classical
  refine LocalRule.avgReg_congr_local k
    (ρ := min (|s - t₁| - r₁ - radius k) (|s - t₂| - r₂ - radius k))
    (lt_min (by linarith) (by linarith)) (fun c _ hc => ?_) (GaussTK.ofReal_mem_Hbar s)
  rw [dist_eq_norm] at hc
  have e1 := abs_sub_le_norm c s t₁
  have e2 := abs_sub_le_norm c s t₂
  have m1 := min_le_left (|s - t₁| - r₁ - radius k) (|s - t₂| - r₂ - radius k)
  have m2 := min_le_right (|s - t₁| - r₁ - radius k) (|s - t₂| - r₂ - radius k)
  simp only [restrictField, if_pos (fc_mem_circOut (radius_pos k)
    (by linarith : r₁ + radius k ≤ ‖c - t₁‖) (by linarith : r₂ + radius k ≤ ‖c - t₂‖))]

end G3Fid
end Thm18Asm
end QuantumZipper

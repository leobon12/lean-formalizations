import HigherDimLQGMetric.Field.SphereAvgBasic
import HigherDimLFPP.Field.LogEnergy

/-!
# Small-ball growth of the uniform measure on the unit sphere

Packet F3 (Phase A, block A1). MA0 Details (a) D-F3 ("sphere measures are atomless with linear
small-ball growth for `d ≥ 2`"); blueprint Lemma `lem:potential` (proof of (a)).

* `unitSphereProb_apply_eq`: the cone formula `σ(A) = |(0,1)·(S ∩ A)| / |B(0,1)|` (Mathlib's
  `Measure.toSphere_apply'`);
* `unitSphereProb_closedBall_le`: `σ(B̄(w, s)) ≤ 2^d min(1, s)` for `d ≥ 2`, all `w`, `s > 0`;
* `growthBound_unitSphereProb`: the same as HigherDimLFPP's `GrowthBound σ (2^d) 1`.

Proof of the growth bound (an own elementary step, not in MA0): for `0 < s < 1`, put
`T = S ∩ B̄(w, s)` (`S` the unit sphere), `a = 1 - s` and `X = |(0,1)·T|`. Then
`(0,1)·T ⊆ a·((0,1)·T) ∪ B̄(w, 2s)` (a point `c t` with `c < a` is `a ((c/a) t)`; if `c ≥ a` then
`|c t - w| ≤ (1 - c) + |t - w| ≤ 2s`), so `X ≤ a^d X + (2s)^d |B(0,1)|`. Since `a^d ≤ a = 1 - s`,
`s X ≤ (2s)^d |B(0,1)|`, i.e. `σ(B̄(w,s)) = X/|B(0,1)| ≤ 2^d s^{d-1} ≤ 2^d s` (`d ≥ 2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- **The cone formula**: `σ(A) = |B(0,1)|⁻¹ |(0,1) · (S ∩ A)|` (`d ≥ 1`). -/
theorem unitSphereProb_apply_eq (hd : 1 ≤ d) {A : Set (Rd d)} (hA : MeasurableSet A) :
    unitSphereProb d A =
      (volume (ball (0 : Rd d) 1))⁻¹ * volume (Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ A)) := by
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hdt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  rw [unitSphereProb, Measure.smul_apply, Measure.map_apply measurable_subtype_coe hA,
    Measure.toSphere_apply' _ (measurable_subtype_coe hA), Measure.toSphere_apply_univ,
    Subtype.image_preimage_coe, smul_eq_mul, finrank_rd,
    ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), mul_mul_mul_comm, ENNReal.inv_mul_cancel hd0 hdt,
    one_mul]

theorem Ioo_smul_sphere_inter_subset_ball (A : Set (Rd d)) :
    Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ A) ⊆ ball (0 : Rd d) 1 := by
  intro x hx
  obtain ⟨c, hc, t, ht, rfl⟩ := mem_smul.1 hx
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1,
    mem_sphere_zero_iff_norm.1 ht.1, mul_one]
  exact hc.2

/-- The covering step of the growth bound. -/
theorem Ioo_smul_sphere_inter_closedBall_subset {s : ℝ} (hs1 : s < 1) (w : Rd d) :
    Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ closedBall w s) ⊆
      (1 - s) • (Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ closedBall w s)) ∪
        closedBall w (2 * s) := by
  intro x hx
  obtain ⟨c, hc, t, ht, rfl⟩ := mem_smul.1 hx
  have ha : 0 < 1 - s := by linarith
  rcases lt_or_ge c (1 - s) with hca | hca
  · refine Or.inl (mem_smul_set.2 ⟨(c / (1 - s)) • t, mem_smul.2 ⟨c / (1 - s),
      ⟨div_pos hc.1 ha, (div_lt_one ha).2 hca⟩, t, ht, rfl⟩, ?_⟩)
    rw [smul_smul, mul_div_cancel₀ _ ha.ne']
  · refine Or.inr ?_
    have ht1 : ‖t‖ = 1 := mem_sphere_zero_iff_norm.1 ht.1
    have htw : ‖t - w‖ ≤ s := by rw [← dist_eq_norm]; exact ht.2
    rw [mem_closedBall, dist_eq_norm]
    calc ‖c • t - w‖ = ‖(c - 1) • t + (t - w)‖ := by rw [sub_smul, one_smul]; abel_nf
      _ ≤ ‖(c - 1) • t‖ + ‖t - w‖ := norm_add_le _ _
      _ = |c - 1| + ‖t - w‖ := by rw [norm_smul, Real.norm_eq_abs, ht1, mul_one]
      _ ≤ s + s := by
          refine add_le_add ?_ htw
          rw [abs_of_nonpos (by linarith [hc.2])]
          linarith
      _ = 2 * s := by ring

/-- **Growth of the unit sphere measure**: `σ(B̄(w, s)) ≤ 2^d min(1, s)` for `d ≥ 2`. -/
theorem unitSphereProb_closedBall_le (hd : 2 ≤ d) (w : Rd d) {s : ℝ} (hs : 0 < s) :
    (unitSphereProb d).real (closedBall w s) ≤ 2 ^ d * min 1 s := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  rcases le_or_gt 1 s with hs1 | hs1
  · rw [min_eq_left hs1, mul_one]
    exact measureReal_le_one.trans h2d
  rw [min_eq_right hs1.le]
  have : Nontrivial (Rd d) := by
    have : NeZero d := ⟨by omega⟩
    infer_instance
  set T := sphere (0 : Rd d) 1 ∩ closedBall w s with hT
  set a := 1 - s with ha
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  -- the measures involved
  have hV0 : 0 < volume (ball (0 : Rd d) 1) := measure_ball_pos _ _ one_pos
  have hVt : volume (ball (0 : Rd d) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hXt : volume (Ioo (0 : ℝ) 1 • T) ≠ ⊤ :=
    ne_top_of_le_ne_top hVt (measure_mono (Ioo_smul_sphere_inter_subset_ball _))
  set V := (volume (ball (0 : Rd d) 1)).toReal with hV
  set X := (volume (Ioo (0 : ℝ) 1 • T)).toReal with hX
  have hVpos : 0 < V := ENNReal.toReal_pos hV0.ne' hVt
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  -- the key inequality `X ≤ a^d X + (2s)^d V`
  have key : X ≤ a ^ d * X + (2 * s) ^ d * V := by
    have h1 := (measure_mono (Ioo_smul_sphere_inter_closedBall_subset hs1 w)).trans
      (measure_union_le (μ := (volume : Measure (Rd d))) _ _)
    rw [Measure.addHaar_smul_of_nonneg _ ha0, Measure.addHaar_closedBall _ _ (by positivity),
      finrank_rd] at h1
    have h2 := ENNReal.toReal_mono (by finiteness) h1
    rwa [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at h2
  have hapow : a ^ d ≤ a := pow_le_of_le_one ha0 ha1 (by omega)
  have hsX : s * X ≤ 2 ^ d * s ^ d * V := by
    have : s * X ≤ (1 - a ^ d) * X := mul_le_mul_of_nonneg_right (by linarith) hX0
    calc s * X ≤ (1 - a ^ d) * X := this
      _ ≤ (2 * s) ^ d * V := by linarith
      _ = 2 ^ d * s ^ d * V := by rw [mul_pow]
  have hsd : s ^ d = s * s ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ d by omega)]
  have hX' : X ≤ 2 ^ d * s ^ (d - 1) * V := by
    rw [hsd] at hsX
    have : s * X ≤ s * (2 ^ d * s ^ (d - 1) * V) := by linarith
    exact le_of_mul_le_mul_left this hs
  have hsd1 : s ^ (d - 1) ≤ s := pow_le_of_le_one hs.le hs1.le (by omega)
  have hσ : (unitSphereProb d).real (closedBall w s) = V⁻¹ * X := by
    rw [measureReal_def, unitSphereProb_apply_eq (by omega) measurableSet_closedBall,
      ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [hσ]
  calc V⁻¹ * X ≤ V⁻¹ * (2 ^ d * s ^ (d - 1) * V) :=
        mul_le_mul_of_nonneg_left hX' (inv_nonneg.2 hVpos.le)
    _ = 2 ^ d * s ^ (d - 1) := by field_simp
    _ ≤ 2 ^ d * s := mul_le_mul_of_nonneg_left hsd1 (by positivity)

/-- `σ` has HigherDimLFPP's linear growth bound at scale `1` with constant `2^d` (`d ≥ 2`). -/
theorem growthBound_unitSphereProb (hd : 2 ≤ d) :
    HigherDimLFPP.GrowthBound (unitSphereProb d) (2 ^ d) 1 := by
  intro w s hs
  rw [div_one]
  exact unitSphereProb_closedBall_le hd w hs

/-- `σ(B̄(w, s)) ≤ 2^d s` for all `s > 0` (`d ≥ 2`). -/
theorem unitSphereProb_closedBall_le_mul (hd : 2 ≤ d) (w : Rd d) {s : ℝ} (hs : 0 < s) :
    (unitSphereProb d).real (closedBall w s) ≤ 2 ^ d * s :=
  (unitSphereProb_closedBall_le hd w hs).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))

end HigherDimLQGMetric

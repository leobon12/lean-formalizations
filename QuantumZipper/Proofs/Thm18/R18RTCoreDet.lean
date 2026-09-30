import QuantumZipper.Proofs.Thm18.R18RTMask
import QuantumZipper.Proofs.GFF.CircleContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT2-core (D82), deterministic part: off-curve agreement of the field read off the curve

Sheffield, arXiv:1012.4797, §4.1 p. 48 ("`h` may be defined arbitrarily on the measure-zero set
`η`"); Berestycki–Powell, arXiv:2404.16642, Thm 8.16 and Rem 8.10 (p. 283). The field
`readOffField (offData x)` read from the masked data agrees with `x.1` at every regularized circle
average whose circle stays off the curve (`avgReg_readOffField_eq_of_circleOff`), and its raw values
are bounded by those of `x.1` (`abs_readOffField_offData_le`). Hence, for a finite measure `ν`
carried by a bounded set, if the raw circle averages of `x.1` grow at most linearly in the scale
index `k` (log growth in the radius `2^{-k}`) and the `ν`-mass of the set of centres whose circle
of radius `2^{-k}` is not off the curve decays geometrically in `k`, then the two regularized
pairings with `ν` coincide (`evalReg_eq_readOffField_of_bounds`): the difference of the `k`-th
terms is at most `2 (C(k+1) + |junk|) · Cm qᵏ → 0`, and two sequences with vanishing difference
have the same `limUnder` (both limits, or both the junk value; `limUnder_eq_of_sub_tendsto_zero_RT`).

Own elementary bookkeeping (junk-value handling and the dominated difference estimate); the
analytic inputs are the two estimates in `R18RTCore.lean`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm CoordsFull

/-! ## Junk values of `limUnder` -/

/-- The junk value of `lim` on `ℝ` (the value of `Classical.epsilon` with no witness). -/
def junkRT : ℝ := Classical.epsilon fun _ : ℝ => False

theorem epsilon_eq_junkRT {p : ℝ → Prop} (hp : ¬ ∃ a, p a) : Classical.epsilon p = junkRT := by
  unfold junkRT Classical.epsilon Classical.strongIndefiniteDescription
  split <;> split <;> first | rfl | (exfalso; simp_all)

theorem limUnder_eq_junkRT {f : ℕ → ℝ} (hf : ¬ ∃ a, Tendsto f atTop (𝓝 a)) :
    limUnder atTop f = junkRT :=
  epsilon_eq_junkRT hf

/-- Two real sequences whose difference tends to `0` have the same `limUnder`. -/
theorem limUnder_eq_of_sub_tendsto_zero_RT {f g : ℕ → ℝ}
    (h : Tendsto (fun k => f k - g k) atTop (𝓝 0)) : limUnder atTop f = limUnder atTop g := by
  by_cases hf : ∃ a, Tendsto f atTop (𝓝 a)
  · obtain ⟨a, ha⟩ := hf
    have hg : Tendsto g atTop (𝓝 a) := by
      have := ha.sub h
      simpa using this
    rw [ha.limUnder_eq, hg.limUnder_eq]
  · have hg : ¬ ∃ a, Tendsto g atTop (𝓝 a) := by
      rintro ⟨a, ha⟩
      exact hf ⟨a, by simpa using ha.add h⟩
    rw [limUnder_eq_junkRT hf, limUnder_eq_junkRT hg]

/-- `limUnder` of a sequence bounded by `M` is bounded by `max M |junk|`. -/
theorem abs_limUnder_le_RT {f : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |f n| ≤ M) :
    |limUnder atTop f| ≤ max M |junkRT| := by
  by_cases hf : ∃ a, Tendsto f atTop (𝓝 a)
  · obtain ⟨a, ha⟩ := hf
    rw [ha.limUnder_eq]
    exact (le_of_tendsto' ((continuous_abs.tendsto a).comp ha) hM).trans (le_max_left _ _)
  · rw [limUnder_eq_junkRT hf]
    exact le_max_right _ _

/-! ## The read field -/

theorem abs_readOffField_offData_le (x : FieldSample × (ℝ → ℝ)) (μ : Measure ℂ) :
    |readOffField (offData x) μ| ≤ |x.1 μ| := by
  classical
  unfold readOffField
  split_ifs with hex
  · obtain ⟨h1, -⟩ := Nat.find_spec hex
    simp only [offData, lawDataOff]
    split_ifs
    · simp only [coordsFull]
      exact (congrArg (fun m => |x.1 m|) h1).le
    · simp
  · simp

/-- Off-curve agreement of the regularized circle averages. -/
theorem avgReg_readOffField_eq_of_circleOff {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2)
    (h0 : x.2 0 = 0) {k : ℕ} {w : ℂ} (hoff : CircleOff (curveOf x.2) w (radius k)) :
    avgReg x.1 k w = avgReg (readOffField (offData x)) k w := by
  obtain ⟨δ, hδ, hW⟩ := hoff
  have hev : ∀ᶠ n : ℕ in atTop, ‖dyadicRoundC n w - w‖ < δ / 2 := by
    have h2 : Tendsto (fun n : ℕ => 2 * (1 / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
      simpa [one_div, inv_pow] using this
    filter_upwards [h2.eventually (gt_mem_nhds (half_pos hδ))] with n hn
    exact (CircleCont.norm_dyadicRoundC_sub_le n w).trans_lt hn
  have heq : (fun n => x.1 (foldedCircle (dyadicRoundC n w) (radius k))) =ᶠ[atTop]
      fun n => readOffField (offData x) (foldedCircle (dyadicRoundC n w) (radius k)) := by
    filter_upwards [hev] with n hn
    obtain ⟨i, hi⟩ := fullIndex_surj n w 1 one_pos k
    rw [← radius_eq_div] at hi
    have hoff' : CircleOff (curveOf x.2) (fullIndex i).1 (fullIndex i).2 := by
      rw [hi]
      refine ⟨δ / 2, half_pos hδ, fun u hu => hW u ?_⟩
      simp only at hu
      have t1 := dist_triangle u (dyadicRoundC n w) w
      have t2 := dist_triangle u w (dyadicRoundC n w)
      rw [dist_comm w (dyadicRoundC n w), dist_eq_norm (dyadicRoundC n w) w] at t2
      rw [dist_eq_norm (dyadicRoundC n w) w] at t1
      rw [abs_lt] at hu ⊢
      constructor <;> linarith [hu.1, hu.2]
    have h := readOffField_offData hc h0 hoff'
    rw [hi] at h
    exact h.symm
  unfold avgReg limUnder
  rw [Filter.map_congr heq]

/-! ## Deterministic assembly -/

/-- **Deterministic core**: log growth of the raw circle averages on a bounded set carrying `ν`,
plus geometric decay of the `ν`-mass of the centres whose circle meets the curve, give equality of
the regularized pairings of the field and of the field read off the curve. -/
theorem evalReg_eq_readOffField_of_bounds {x : FieldSample × (ℝ → ℝ)} (hc : Continuous x.2)
    (h0 : x.2 0 = 0) {ν : Measure ℂ} [IsFiniteMeasure ν] {Rr C Cm q : ℝ} (hC : 0 ≤ C)
    (hCm : 0 ≤ Cm) (hq0 : 0 ≤ q) (hq1 : q < 1) (hsupp : ν {w | ¬ ‖w‖ ≤ Rr} = 0)
    (hgrow : ∀ (k n : ℕ) (w : ℂ), ‖w‖ ≤ Rr →
      |x.1 (foldedCircle (dyadicRoundC n w) (radius k))| ≤ C * (k + 1))
    (hmass : ∀ k : ℕ, ν {w | ¬ CircleOff (curveOf x.2) w (radius k)} ≤
      ENNReal.ofReal (Cm * q ^ k)) :
    evalReg x.1 ν = evalReg (readOffField (offData x)) ν := by
  set R := readOffField (offData x) with hRdef
  unfold evalReg
  apply limUnder_eq_of_sub_tendsto_zero_RT
  have hgood : ∀ᵐ w ∂ν, ‖w‖ ≤ Rr := by
    rw [ae_iff]; exact hsupp
  set Bk : ℕ → ℝ := fun k => max (C * (k + 1)) |junkRT| with hBk
  have hBx : ∀ k, ∀ w, ‖w‖ ≤ Rr → |avgReg x.1 k w| ≤ Bk k := fun k w hw =>
    abs_limUnder_le_RT fun n => hgrow k n w hw
  have hBR : ∀ k, ∀ w, ‖w‖ ≤ Rr → |avgReg R k w| ≤ Bk k := fun k w hw =>
    abs_limUnder_le_RT fun n => (abs_readOffField_offData_le x _).trans (hgrow k n w hw)
  have hmeas : ∀ (y : FieldSample) (k : ℕ), Measurable fun w => avgReg y k w := fun y k =>
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  have hint : ∀ (y : FieldSample) (k : ℕ), (∀ w, ‖w‖ ≤ Rr → |avgReg y k w| ≤ Bk k) →
      Integrable (fun w => avgReg y k w) ν := fun y k hb =>
    Integrable.of_bound (hmeas y k).aestronglyMeasurable (Bk k)
      (by filter_upwards [hgood] with w hw; rw [Real.norm_eq_abs]; exact hb w hw)
  have hbound : ∀ k : ℕ, ‖(∫ w, avgReg x.1 k w ∂ν) - ∫ w, avgReg R k w ∂ν‖ ≤
      2 * Bk k * (Cm * q ^ k) := by
    intro k
    set T := toMeasurable ν {w | ¬ CircleOff (curveOf x.2) w (radius k)} with hT
    have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
    rw [← integral_sub (hint _ k (hBx k)) (hint _ k (hBR k))]
    have hle : ‖∫ w, (avgReg x.1 k w - avgReg R k w) ∂ν‖ ≤
        ∫ w, T.indicator (fun _ => 2 * Bk k) w ∂ν := by
      refine norm_integral_le_of_norm_le ((integrable_const _).indicator hTm) ?_
      filter_upwards [hgood] with w hw
      by_cases hwo : CircleOff (curveOf x.2) w (radius k)
      · rw [avgReg_readOffField_eq_of_circleOff hc h0 hwo, sub_self, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) _
      · have hwT : w ∈ T := subset_toMeasurable _ _ hwo
        rw [Set.indicator_of_mem hwT, Real.norm_eq_abs]
        have := abs_sub (avgReg x.1 k w) (avgReg R k w)
        linarith [hBx k w hw, hBR k w hw]
    refine hle.trans ?_
    rw [integral_indicator_const _ hTm, smul_eq_mul, mul_comm]
    have hBk0 : 0 ≤ Bk k := (abs_nonneg _).trans (le_max_right _ _)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Measure.real, hT, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hmass k)
  refine squeeze_zero_norm hbound ?_
  have hBk_le : ∀ k : ℕ, Bk k ≤ C * k + (C + |junkRT|) := fun k =>
    max_le (by nlinarith [abs_nonneg junkRT]) (by nlinarith [abs_nonneg junkRT])
  have hlim1 := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).const_mul (2 * Cm * C)
  have hlim2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul
    (2 * Cm * (C + |junkRT|))
  have hsum := hlim1.add hlim2
  simp only [mul_zero, add_zero] at hsum
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hsum
  · have hBk0 : 0 ≤ Bk k := (abs_nonneg _).trans (le_max_right _ _)
    positivity
  · have hqk : 0 ≤ q ^ k := pow_nonneg hq0 k
    have := hBk_le k
    have h2 : 2 * Bk k * (Cm * q ^ k) ≤ 2 * (C * k + (C + |junkRT|)) * (Cm * q ^ k) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [h2]

end R18
end QuantumZipper

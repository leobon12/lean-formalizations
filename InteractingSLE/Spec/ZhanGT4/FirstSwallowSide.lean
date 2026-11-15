/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBessel

/-!
# Either real side can be swallowed first (Part A.4.1)

Packet PROVE-ZHAN-GT4-A. Source: Astra, *Follow-up proofs and dependency audit*, §A.4.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L726–L741, ruling R38):

> For deterministic `p₋ < 0 < p₊`, let `τ₋, τ₊` be their ordinary swallowing times. Both events `τ₋ < τ₊` and
> `τ₊ < τ₋` have positive probability. Indeed, before the first swallowing, write `L = W − g(p₋) > 0`,
> `R = g(p₊) − W > 0`, and `Z = log(R/L)`. … Its scale density is `s′(z) = cosh(z/2)^{8/κ−2}` (G4). Its integral
> is finite at both ends. The physical first swallowing time is finite by the Bessel fact. Since `L + R`
> increases, just one of the two gaps can vanish there … Optional sampling of the bounded normalized scale
> function gives two strictly positive endpoint probabilities.

## Proof in Lean

No time change is needed. With the centered flows `a = g(p₋) − W < 0 < b = g(p₊) − W` the ratio
`w = b/(b − a) = R/(R + L) ∈ (0, 1)` is a monotone function of `Z` (`w = e^Z/(1 + e^Z)`), and in this variable the
scale density (G4) becomes `(w(1 − w))^{−4/κ}` (up to the constant `2^{2−8/κ}`): `Φ(w) = ∫_{1/2}^w (v(1 − v))^{−4/κ} dv`
(`oppScale`). It is finite at both ends exactly when `4/κ < 1`. The function `F(a, b) = Φ(b/(b − a))` is harmonic for
the two-point generator (`dynkinGen_oppF`; the same algebra as `dynkinGen_twoPointF`, on the other component of
`w ≠ 1`), bounded by `Φ(0)` and `Φ(1)`, so QuantumZipper's local Dynkin formula stopped on leaving
`{b ≥ 1/L, a ≤ −1/L}` gives `E g_L = F(p₋, p₊)` for the stopped values `g_L`. If `p₊` is swallowed while `p₋` is alive,
then `g_L → Φ(0)` (`tendsto_stopped_opp_of_alive`); dominated convergence on the event where `g_L → Φ(0)` gives a
positive probability to its complement, on which `p₋` is swallowed first (the two points are never swallowed at the
same time: `not_realSwallowAt_both`, since `g(p₊) − g(p₋)` does not decrease). Reflection gives the other side.

## Main results

* `exists_measurableSet_swallow_neg_first`: for `κ > 4` and `p₋ < 0 < p₊`, an event `E` of positive probability,
  measurable for the driving path, on which almost surely `p₋` is swallowed at a time `σ` at which `p₊` is still
  alive.
* `exists_measurableSet_swallow_pos_first`: the reflected statement.
* `not_realSwallowAt_both`: two real points on opposite sides of `0` are never swallowed at the same time.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE.ZhanGT4

/-! ### The scale function on `(0, 1)` -/

section Scale

variable {κ : ℝ}

/-- The scale density `(v(1 − v))^{−4/κ}` of the ratio `w = b/(b − a)` of two real flows on opposite sides of the
driver ((G4) in the variable `w = e^Z/(1 + e^Z)`). -/
def oppDens (κ v : ℝ) : ℝ := (v * (1 - v)) ^ (-(4 / κ))

/-- The scale function `Φ(w) = ∫_{1/2}^w (v(1 − v))^{−4/κ} dv`. -/
def oppScale (κ w : ℝ) : ℝ := ∫ v in (1 / 2 : ℝ)..w, oppDens κ v

theorem oppDens_pos {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : 0 < oppDens κ v :=
  Real.rpow_pos_of_pos (mul_pos hv.1 (sub_pos.2 hv.2)) _

theorem oppDens_one_sub (v : ℝ) : oppDens κ (1 - v) = oppDens κ v := by
  simp only [oppDens]; congr 1; ring

theorem continuousAt_oppDens {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : ContinuousAt (oppDens κ) v :=
  ContinuousAt.rpow_const (by fun_prop) (Or.inl (mul_pos hv.1 (sub_pos.2 hv.2)).ne')

theorem continuousOn_oppDens : ContinuousOn (oppDens κ) (Ioo 0 1) :=
  fun _ hv => (continuousAt_oppDens hv).continuousWithinAt

theorem hasDerivAt_oppDens {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (oppDens κ) ((1 - 2 * v) * -(4 / κ) * (v * (1 - v)) ^ (-(4 / κ) - 1)) v := by
  have h : HasDerivAt (fun v : ℝ => v * (1 - v)) (1 - 2 * v) v :=
    ((hasDerivAt_id' v).mul ((hasDerivAt_id' v).const_sub 1)).congr_deriv (by ring)
  exact h.rpow_const (Or.inl (mul_pos hv.1 (sub_pos.2 hv.2)).ne')

theorem contDiffOn_oppDens : ContDiffOn ℝ 2 (oppDens κ) (Ioo 0 1) :=
  (by fun_prop : ContDiffOn ℝ 2 (fun v : ℝ => v * (1 - v)) (Ioo 0 1)).rpow_const_of_ne
    fun v hv => (mul_pos hv.1 (sub_pos.2 hv.2)).ne'

theorem intervalIntegrable_oppDens {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (oppDens κ) volume a b := by
  refine (continuousOn_oppDens.mono fun v hv => ?_).intervalIntegrable
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hv; exact ⟨ha.1.trans_le hv.1, hv.2.trans_lt hb.2⟩
  · rw [uIcc_of_ge hab] at hv; exact ⟨hb.1.trans_le hv.1, hv.2.trans_lt ha.2⟩

/-- The density is integrable at `0` (exponent `−4/κ > −1`). -/
theorem intervalIntegrable_oppDens_zero (hκ : 4 < κ) :
    IntervalIntegrable (oppDens κ) volume 0 (1 / 2) := by
  have hκ0 : 0 < κ := by linarith
  have hr : -1 < -(4 / κ) := by
    have : 4 / κ < 1 := (div_lt_one hκ0).2 hκ
    linarith
  have h1 : IntervalIntegrable (fun v : ℝ => v ^ (-(4 / κ))) volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have h2 : ContinuousOn (fun v : ℝ => (1 - v) ^ (-(4 / κ))) (uIcc 0 (1 / 2)) := fun v hv => by
    rw [uIcc_of_le (by norm_num)] at hv
    have h1v : (1 - v) ≠ 0 := by linarith [hv.2]
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl h1v)).comp
      (continuousAt_const.sub continuousAt_id)).continuousWithinAt
  refine (h1.continuousOn_mul h2).congr fun v hv => ?_
  rw [uIoc_of_le (by norm_num)] at hv
  simp only [oppDens]
  rw [Real.mul_rpow hv.1.le (by linarith [hv.2]), mul_comm]

/-- The density is integrable at `1`, by the symmetry `v ↦ 1 − v`. -/
theorem intervalIntegrable_oppDens_one (hκ : 4 < κ) :
    IntervalIntegrable (oppDens κ) volume (1 / 2) 1 := by
  have h := ((intervalIntegrable_oppDens_zero hκ).comp_sub_left 1).symm
  norm_num at h
  exact h.congr fun v _ => oppDens_one_sub v

theorem intervalIntegrable_oppDens_Icc (hκ : 4 < κ) :
    IntervalIntegrable (oppDens κ) volume 0 1 :=
  (intervalIntegrable_oppDens_zero hκ).trans (intervalIntegrable_oppDens_one hκ)

theorem hasDerivAt_oppScale {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (oppScale κ) (oppDens κ w) w :=
  intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_oppDens ⟨by norm_num, by norm_num⟩ hw)
    (continuousOn_oppDens.stronglyMeasurableAtFilter isOpen_Ioo w hw)
    (continuousAt_oppDens hw)

theorem deriv_oppScale_eventuallyEq {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    deriv (oppScale κ) =ᶠ[𝓝 w] oppDens κ := by
  filter_upwards [isOpen_Ioo.mem_nhds hw] with v hv
  exact (hasDerivAt_oppScale hv).deriv

theorem contDiffOn_oppScale : ContDiffOn ℝ 3 (oppScale κ) (Ioo 0 1) := by
  rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun w hw => (hasDerivAt_oppScale hw).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  exact contDiffOn_oppDens.congr fun w hw => (hasDerivAt_oppScale hw).deriv

/-- `Φ` is continuous on the closed interval `[0, 1]` (the density is integrable there). -/
theorem continuousOn_oppScale (hκ : 4 < κ) : ContinuousOn (oppScale κ) (Icc 0 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_oppDens_Icc hκ)
    (a := 1 / 2) (by rw [uIcc_of_le zero_le_one]; norm_num)
  rwa [uIcc_of_le zero_le_one] at h

/-- `Φ` is monotone on `[0, 1]`. -/
theorem monotoneOn_oppScale (hκ : 4 < κ) : MonotoneOn (oppScale κ) (Icc 0 1) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) (continuousOn_oppScale hκ)
    (fun _ hw => (hasDerivAt_oppScale (by rwa [interior_Icc] at hw)).hasDerivWithinAt)
    (fun _ hw => (oppDens_pos (by rwa [interior_Icc] at hw)).le)

/-- `Φ` is strictly monotone on `[0, 1]`. -/
theorem strictMonoOn_oppScale (hκ : 4 < κ) : StrictMonoOn (oppScale κ) (Icc 0 1) :=
  strictMonoOn_of_deriv_pos (convex_Icc 0 1) (continuousOn_oppScale hκ) fun w hw => by
    rw [interior_Icc] at hw
    rw [(hasDerivAt_oppScale hw).deriv]
    exact oppDens_pos hw

/-- `Φ(w) → Φ(0)` as `w ↓ 0`. -/
theorem tendsto_oppScale_zero (hκ : 4 < κ) :
    Tendsto (oppScale κ) (𝓝[>] 0) (𝓝 (oppScale κ 0)) := by
  have h := (continuousOn_oppScale hκ).continuousWithinAt (x := 0) ⟨le_rfl, zero_le_one⟩
  refine h.tendsto.mono_left ?_
  refine nhdsWithin_le_iff.2 ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with w hw h1
  exact ⟨le_of_lt hw, le_of_lt h1⟩

end Scale

/-! ### The two-point harmonic function on opposite sides -/

section TwoPoint

variable {κ : ℝ}

/-- The domain `a < 0 < b` of two real flows on opposite sides of the driver. -/
def oppDom : Set (ℝ × ℝ) := {q | q.1 < 0 ∧ 0 < q.2}

/-- **The two-point harmonic function** `F(a, b) = Φ(b/(b − a))`. -/
def oppF (κ : ℝ) (q : ℝ × ℝ) : ℝ := oppScale κ (q.2 / (q.2 - q.1))

/-- The tamed two-point drift `(−2/max(−a, c), 2/max(b, c))`. -/
def oppDrift (c : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (-realDrift c (-q.1), realDrift c q.2)

theorem isOpen_oppDom : IsOpen oppDom :=
  (isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_const continuous_snd)

theorem div_mem_Ioo_of_mem_oppDom {q : ℝ × ℝ} (hq : q ∈ oppDom) :
    q.2 / (q.2 - q.1) ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := hq
  have hd : 0 < q.2 - q.1 := by linarith
  exact ⟨div_pos h2 hd, (div_lt_one hd).2 (by linarith)⟩

theorem contDiffOn_oppF : ContDiffOn ℝ 3 (oppF κ) oppDom := by
  have hg : ContDiffOn ℝ 3 (fun q : ℝ × ℝ => q.2 / (q.2 - q.1)) oppDom :=
    contDiffOn_snd.div (contDiffOn_snd.sub contDiffOn_fst) fun q hq => by
      have h1 := hq.1; have h2 := hq.2
      exact (by linarith : (0 : ℝ) < q.2 - q.1).ne'
  exact contDiffOn_oppScale.comp hg fun q hq => div_mem_Ioo_of_mem_oppDom hq

theorem lipschitzWith_oppDrift {c : ℝ} (hc : 0 < c) :
    LipschitzWith (Real.toNNReal (2 / c ^ 2)) (oppDrift c) := by
  have h1 : LipschitzWith 1 (fun q : ℝ × ℝ => -q.1) := LipschitzWith.prod_fst.neg
  have h2 := ((lipschitz_realDrift hc).comp h1).neg
  exact (LipschitzWith.prodMk h2 ((lipschitz_realDrift hc).comp LipschitzWith.prod_snd)).weaken
    (by simp)

theorem norm_oppDrift_le {c : ℝ} (hc : 0 < c) (q : ℝ × ℝ) : ‖oppDrift c q‖ ≤ 2 / c := by
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  simp only [oppDrift, abs_neg]
  exact ⟨abs_realDrift_le hc _, abs_realDrift_le hc _⟩

/-- **`F` is harmonic for the two-point generator** (`da = 2/a dt − √κ dB`, `db = 2/b dt − √κ dB`, same `B`):
along the noise direction `w = b/(b − a)` moves affinely, and `Φ'' = −(4/κ)(1 − 2w)Φ'/(w(1 − w))` cancels the drift.
This is the scale density (G4) of §A.4.1 in the variable `w`. -/
theorem dynkinGen_oppF (hκ : 0 < κ) {c s : ℝ} (hs : s * s = κ) {q : ℝ × ℝ}
    (hq : q ∈ oppDom) (hc1 : c ≤ -q.1) (hc2 : c ≤ q.2) :
    dynkinGen (oppDrift c) (-s, -s) (oppF κ) q = 0 := by
  obtain ⟨a, b⟩ := q
  obtain ⟨ha, hb⟩ := hq
  simp only at ha hb hc1 hc2
  have hba : 0 < b - a := by linarith
  have hd : ContDiffAt ℝ 3 (oppF κ) (a, b) :=
    contDiffOn_oppF.contDiffAt (isOpen_oppDom.mem_nhds ⟨ha, hb⟩)
  set w := b / (b - a) with hwdef
  have hw : w ∈ Ioo (0 : ℝ) 1 := div_mem_Ioo_of_mem_oppDom (q := (a, b)) ⟨ha, hb⟩
  have hdrift : oppDrift c (a, b) = (2 / a, 2 / b) := by
    simp only [oppDrift]
    rw [realDrift_of_le hc1, realDrift_of_le hc2, div_neg, neg_neg]
  rw [dynkinGen, hdrift, FrozenMart.fderiv_apply_eq_deriv_line (hd.differentiableAt (by simp)),
    FrozenMart.iteratedFDeriv_two_eq_deriv_deriv_line (hd.of_le (by norm_num))]
  -- first order term
  set g : ℝ → ℝ := fun r => (b + r * (2 / b)) / ((b + r * (2 / b)) - (a + r * (2 / a))) with hgdef
  have hline1 : (fun r : ℝ => oppF κ ((a, b) + r • (2 / a, 2 / b))) =
      fun r => oppScale κ (g r) := by
    funext r; simp [oppF, hgdef]
  have hg0 : g 0 = w := by simp [hgdef, hwdef]
  have hg : HasDerivAt g (((2 / b) * (b - a) - b * (2 / b - 2 / a)) / (b - a) ^ 2) 0 := by
    have hc1' : HasDerivAt (fun r : ℝ => b + r * (2 / b)) (2 / b) 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const (2 / b)).const_add b
    have hc2' : HasDerivAt (fun r : ℝ => a + r * (2 / a)) (2 / a) 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const (2 / a)).const_add a
    have h := hc1'.div (hc1'.sub hc2') (by simp; exact hba.ne')
    refine h.congr_deriv ?_
    simp
  have hfirst : deriv (fun r : ℝ => oppScale κ (g r)) 0 =
      oppDens κ w * (((2 / b) * (b - a) - b * (2 / b - 2 / a)) / (b - a) ^ 2) := by
    have h := (hasDerivAt_oppScale (κ := κ) (hg0 ▸ hw)).comp 0 hg
    rw [hg0] at h
    exact h.deriv
  -- second order term
  set h : ℝ → ℝ := fun r => w - r * (s / (b - a)) with hhdef
  have hline2 : (fun r : ℝ => oppF κ ((a, b) + r • (-s, -s))) = fun r => oppScale κ (h r) := by
    funext r
    simp only [oppF, hhdef, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
    congr 1
    have e : b + r * -s - (a + r * -s) = b - a := by ring
    rw [e, hwdef]
    field_simp
    ring
  have hh0 : h 0 = w := by simp [hhdef]
  have hhc : ContDiffAt ℝ 2 h 0 := by fun_prop
  have hΨc : ContDiffAt ℝ 2 (oppScale κ) (h 0) := by
    rw [hh0]
    exact (contDiffOn_oppScale.contDiffAt (isOpen_Ioo.mem_nhds hw)).of_le (by norm_num)
  have hsecond := RS.deriv_deriv_comp_zero hΨc hhc
  have hdh : deriv h = fun _ => -(s / (b - a)) := by
    funext r
    have : HasDerivAt h (-(s / (b - a))) r := by
      simpa using ((hasDerivAt_id' r).mul_const (s / (b - a))).const_sub w
    exact this.deriv
  have hddh : deriv (deriv h) 0 = 0 := by rw [hdh]; simp
  have hdΨ : deriv (oppScale κ) w = oppDens κ w := (hasDerivAt_oppScale hw).deriv
  have hddΨ : deriv (deriv (oppScale κ)) w =
      (1 - 2 * w) * -(4 / κ) * (w * (1 - w)) ^ (-(4 / κ) - 1) := by
    rw [(deriv_oppScale_eventuallyEq hw).deriv_eq]
    exact (hasDerivAt_oppDens hw).deriv
  rw [hline1, hfirst, hline2, hsecond, hh0, hddh, hdΨ, hddΨ, hdh]
  have hww : w * (1 - w) ≠ 0 := (mul_pos hw.1 (sub_pos.2 hw.2)).ne'
  rw [Real.rpow_sub_one hww]
  simp only [oppDens]
  set P := (w * (1 - w)) ^ (-(4 / κ)) with hPdef
  have hw1 : 1 - w = -a / (b - a) := by rw [hwdef]; field_simp; ring
  have hwsq : w * (1 - w) = -(a * b) / (b - a) ^ 2 := by
    rw [hw1, hwdef]; field_simp
  have h2w : 1 - 2 * w = -(b + a) / (b - a) := by rw [hwdef]; field_simp; ring
  rw [hwsq, h2w]
  have hs2 : s ^ 2 = κ := by rw [sq]; exact hs
  have ha0 : a ≠ 0 := ha.ne
  have hb0 : b ≠ 0 := hb.ne'
  field_simp
  rw [hs2]
  ring

/-- Bounds of the two-point function on its domain. -/
theorem oppF_mem_Icc (hκ : 4 < κ) {q : ℝ × ℝ} (hq : q ∈ oppDom) :
    oppF κ q ∈ Icc (oppScale κ 0) (oppScale κ 1) := by
  have hw := div_mem_Ioo_of_mem_oppDom hq
  have hmono := monotoneOn_oppScale hκ
  exact ⟨hmono ⟨le_rfl, zero_le_one⟩ ⟨hw.1.le, hw.2.le⟩ hw.1.le,
    hmono ⟨hw.1.le, hw.2.le⟩ ⟨zero_le_one, le_rfl⟩ hw.2.le⟩

/-- The two-point function lies strictly between its end values. -/
theorem oppF_mem_Ioo (hκ : 4 < κ) {q : ℝ × ℝ} (hq : q ∈ oppDom) :
    oppF κ q ∈ Ioo (oppScale κ 0) (oppScale κ 1) := by
  have hw := div_mem_Ioo_of_mem_oppDom hq
  have hmono := strictMonoOn_oppScale hκ
  exact ⟨hmono ⟨le_rfl, zero_le_one⟩ ⟨hw.1.le, hw.2.le⟩ hw.1,
    hmono ⟨hw.1.le, hw.2.le⟩ ⟨zero_le_one, le_rfl⟩ hw.2⟩

end TwoPoint

/-! ### Real flows on the negative side, by reflection -/

section Negative

variable {W : ℝ → ℝ}

/-- The tamed real flow of a point on the negative side: the reflection `x ↦ −x`, `W ↦ −W` of QuantumZipper's
tamed flow `realTamed`. While it stays `≤ −c` it is the true centered flow (`isForwardSol_negTamed`). -/
def negTamed (W : ℝ → ℝ) (c x t : ℝ) : ℝ := -realTamed (fun s => -W s) c (-x) t

theorem isForwardSol_negTamed (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ} (hle : ∀ t ∈ Icc (0 : ℝ) T, negTamed W c x t ≤ -c) :
    IsForwardSol W (x : ℂ) T (fun t => (negTamed W c x t : ℂ)) := by
  have h := isForwardSol_realTamed (W := fun s => -W s) hW.neg hc hT (x := -x) fun t ht => by
    have := hle t ht
    simp only [negTamed] at this
    linarith
  refine (isForwardSol_neg_iff (W := W) (z := (x : ℂ))).1 ?_
  convert h using 2
  · push_cast; ring
  · simp [negTamed]

/-- A solution from `x < 0` stays below a negative constant on `[0, T]`. -/
theorem exists_pos_re_le_neg_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ}
    (hx : x < 0) (hT : 0 ≤ T) {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) :
    ∃ m > 0, ∀ t ∈ Icc (0 : ℝ) T, (v t).re ≤ -m := by
  have h := isForwardSol_neg hv
  rw [← Complex.ofReal_neg] at h
  obtain ⟨m, hm, hle⟩ := exists_pos_le_re_of_isForwardSol (W := fun s => -W s) hW.neg
    (by simp [hW0]) (neg_pos.2 hx) hT h
  refine ⟨m, hm, fun t ht => ?_⟩
  have := hle t ht
  simp only [Complex.neg_re] at this
  linarith

/-- The reflected form of `exists_realSwallowAt`: a negative point that is not alive on `[0, T]` is swallowed at
some `σ ≤ T`. -/
theorem exists_realSwallowAt_of_neg (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hx : x < 0)
    (hT : 0 ≤ T) (hdead : ¬ ∃ v, IsForwardSol W (x : ℂ) T v) :
    ∃ σ ∈ Ioc 0 T, RealSwallowAt W x σ := by
  obtain ⟨σ, hσ, h⟩ := exists_realSwallowAt (W := fun s => -W s) hW.neg (by simp [hW0])
    (neg_pos.2 hx) hT (by rwa [exists_isForwardSol_neg_iff])
  exact ⟨σ, hσ, realSwallowAt_neg_iff.1 h⟩

/-- The uncentered flow of a positive point is at least its starting point. -/
theorem le_re_add_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hx : 0 < x)
    (hT : 0 ≤ T) {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) : x ≤ (v T).re + W T := by
  have hmono := re_add_monotoneOn hW hW0 hx hT hv
  have h0 : (v 0).re + W 0 = x := by
    have := (hv.2 0 ⟨le_rfl, hT⟩).2
    rw [this, hW0]; simp
  rw [← h0]
  exact hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT

/-- The uncentered flow of a negative point is at most its starting point. -/
theorem re_add_le_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hx : x < 0)
    (hT : 0 ≤ T) {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) : (v T).re + W T ≤ x := by
  have h := isForwardSol_neg hv
  rw [← Complex.ofReal_neg] at h
  have := le_re_add_of_isForwardSol (W := fun s => -W s) hW.neg (by simp [hW0]) (neg_pos.2 hx) hT h
  simp only [Complex.neg_re] at this
  linarith

/-- **Two real points on opposite sides of `0` are never swallowed at the same time** (§A.4.1: "Since `L + R`
increases, just one of the two gaps can vanish there"): `g(p₊) − g(p₋) ≥ p₊ − p₋` while both are alive, whereas at a
common swallowing time both centered flows would tend to `0`. -/
theorem not_realSwallowAt_both (hW : Continuous W) (hW0 : W 0 = 0) {p q σ : ℝ} (hp : p < 0)
    (hq : 0 < q) (hσp : RealSwallowAt W p σ) (hσq : RealSwallowAt W q σ) : False := by
  have hσ0 := hσq.1
  have hlimq := tendsto_fwdMap_of_realSwallowAt hW hW0 hq hσq
  have hlimp' := tendsto_fwdMap_of_realSwallowAt (W := fun s => -W s) hW.neg (by simp [hW0])
    (neg_pos.2 hp) (realSwallowAt_neg_iff.2 hσp)
  have hev : ∀ᶠ s in 𝓝[<] σ, s ∈ Ioo 0 σ := Ioo_mem_nhdsLT hσ0
  -- the flow of `p` tends to `0`
  have hlimp : Tendsto (fun s => fwdMap W s p) (𝓝[<] σ) (𝓝 0) := by
    have h2 := hlimp'.neg
    rw [neg_zero] at h2
    refine h2.congr' ?_
    filter_upwards [hev] with s hs
    obtain ⟨v, hv⟩ := hσp.2.1 s ⟨hs.1.le, hs.2⟩
    rw [fwdMap_neg_real hW hv ⟨hs.1.le, le_rfl⟩, neg_neg]
  have hsub := hlimq.sub hlimp
  rw [sub_zero] at hsub
  have hdiff := (Complex.continuous_re.tendsto 0).comp hsub
  rw [Complex.zero_re] at hdiff
  have hbound : ∀ᶠ s in 𝓝[<] σ, q - p ≤ Complex.re (fwdMap W s q - fwdMap W s p) := by
    filter_upwards [hev] with s hs
    obtain ⟨vq, hvq⟩ := hσq.2.1 s ⟨hs.1.le, hs.2⟩
    obtain ⟨vp, hvp⟩ := hσp.2.1 s ⟨hs.1.le, hs.2⟩
    have h1 := le_re_add_of_isForwardSol hW hW0 hq hs.1.le hvq
    have h2 := re_add_le_of_isForwardSol hW hW0 hp hs.1.le hvp
    rw [Complex.sub_re, fwdMap_eq_of_isForwardSol hW hvq ⟨hs.1.le, le_rfl⟩,
      fwdMap_eq_of_isForwardSol hW hvp ⟨hs.1.le, le_rfl⟩]
    linarith
  have := ge_of_tendsto hdiff hbound
  linarith

end Negative

/-! ### The stopped two-point process -/

section Stopped

/-- The stopping region at level `L`: `a ≤ −1/L`, `b ≥ 1/L`. -/
def oppK (L : ℝ) : Set (ℝ × ℝ) := {q | q.1 ≤ -(1 / L) ∧ 1 / L ≤ q.2}

/-- The exit set at level `L`. -/
def oppCl (L : ℝ) : Set (ℝ × ℝ) := {q | -(1 / L) ≤ q.1} ∪ {q | q.2 ≤ 1 / L}

theorem isClosed_oppK (L : ℝ) : IsClosed (oppK L) :=
  (isClosed_le continuous_fst continuous_const).inter (isClosed_le continuous_const continuous_snd)

theorem isClosed_oppCl (L : ℝ) : IsClosed (oppCl L) :=
  (isClosed_le continuous_const continuous_fst).union (isClosed_le continuous_snd continuous_const)

theorem compl_oppCl_subset (L : ℝ) : (oppCl L)ᶜ ⊆ oppK L := by
  intro q hq
  simp only [oppCl, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_le] at hq
  exact ⟨hq.1.le, hq.2.le⟩

theorem oppK_subset {L : ℝ} (hL : 0 < L) : oppK L ⊆ oppDom := by
  intro q hq
  have h : 0 < 1 / L := by positivity
  exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

/-- **Pathwise identification of the stopped two-point value.** Let `q` be swallowed at `σ` and `p < 0` alive on
`[0, σ]` (solution `wp`) with `Re wp < −1/L` there. Then the tamed two-point path at level `c ≤ 1/L` first leaves
`oppK L` at a time `τ < σ`, through `b_τ = 1/L`, with `a_τ = Re wp(τ)`. -/
theorem stopped_opp_eq {Ω : Type*} {W : ℝ → ℝ} (hW : Continuous W)
    {p q σ L c : ℝ} (hσ : RealSwallowAt W q σ) {wp : ℝ → ℂ}
    (hwp : IsForwardSol W (p : ℂ) σ wp) (hc : 0 < c) (hcL : c ≤ 1 / L)
    {T : ℝ≥0} (hσT : σ < T) (hpL : ∀ t ∈ Icc (0 : ℝ) σ, (wp t).re < -(1 / L))
    {V : ℝ≥0 → Ω → ℝ × ℝ} {ω : Ω} (hV : ∀ t : ℝ≥0, V t ω = (negTamed W c p t, realTamed W c q t))
    (hVc : Continuous fun t => V t ω) (hV0 : V 0 ω ∈ oppK L) :
    ((hittingBtwn V (oppCl L) 0 T ω : ℝ≥0) : ℝ) < σ ∧
      (V (hittingBtwn V (oppCl L) 0 T ω) ω).2 = 1 / L ∧
      (V (hittingBtwn V (oppCl L) 0 T ω) ω).1 =
        (wp ((hittingBtwn V (oppCl L) 0 T ω : ℝ≥0) : ℝ)).re := by
  set τ := hittingBtwn V (oppCl L) 0 T ω with hτdef
  have hσ0 := hσ.1
  have hK : ∀ t ≤ τ, V t ω ∈ oppK L := by
    intro t ht
    refine mem_of_forall_lt_of_isClosed (isClosed_oppK L) hVc hV0 fun r hr => ?_
    exact compl_oppCl_subset L (notMem_of_lt_hittingBtwn (hr.trans_le ht) zero_le)
  have hge : ∀ t : ℝ, t ∈ Icc (0 : ℝ) τ →
      negTamed W c p t ≤ -(1 / L) ∧ 1 / L ≤ realTamed W c q t := by
    intro t ht
    have h := hK t.toNNReal ((Real.toNNReal_le_iff_le_coe).2 ht.2)
    rw [hV, Real.coe_toNNReal _ ht.1] at h
    exact h
  have hsolq : IsForwardSol W (q : ℂ) τ (fun t => (realTamed W c q t : ℂ)) :=
    isForwardSol_realTamed hW hc τ.coe_nonneg fun t ht => hcL.trans (hge t ht).2
  have hsolp : IsForwardSol W (p : ℂ) τ (fun t => (negTamed W c p t : ℂ)) :=
    isForwardSol_negTamed hW hc τ.coe_nonneg fun t ht => by linarith [(hge t ht).1]
  have hτσ : (τ : ℝ) < σ := by
    by_contra h
    push Not at h
    exact hσ.2.2 ⟨_, isForwardSol_restrict hsolq hσ0.le h⟩
  have hτmem : (τ : ℝ) ∈ Icc (0 : ℝ) τ := ⟨τ.coe_nonneg, le_rfl⟩
  have hpτ : negTamed W c p τ = (wp τ).re := by
    have h1 := fwdMap_eq_of_isForwardSol hW hsolp hτmem
    have h2 := fwdMap_eq_of_isForwardSol hW hwp ⟨τ.coe_nonneg, hτσ.le⟩
    rw [h1] at h2
    have := congrArg Complex.re h2
    simpa using this
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) T, V j ω ∈ oppCl L := by
    by_contra hne
    push Not at hne
    have hgeT : ∀ t ∈ Icc (0 : ℝ) T, c ≤ realTamed W c q t := by
      intro t ht
      have h := compl_oppCl_subset L (hne t.toNNReal ⟨zero_le,
        (Real.toNNReal_le_iff_le_coe).2 ht.2⟩)
      rw [hV, Real.coe_toNNReal _ ht.1] at h
      exact hcL.trans h.2
    exact hσ.2.2 ⟨_, isForwardSol_restrict (isForwardSol_realTamed hW hc T.coe_nonneg hgeT)
      hσ0.le hσT.le⟩
  have hmem := hittingBtwn_mem_of_isClosed' (isClosed_oppCl L) hVc hex
  rw [← hτdef, hV] at hmem
  have hKτ := hK τ le_rfl
  rw [hV] at hKτ
  refine ⟨hτσ, ?_, ?_⟩
  · rw [hV]
    rcases hmem with h | h
    · exfalso
      have := hpL τ ⟨τ.coe_nonneg, hτσ.le⟩
      simp only [mem_ofPred_eq] at h
      rw [hpτ] at h
      linarith
    · exact le_antisymm h hKτ.2
  · rw [hV]; exact hpτ

end Stopped

/-! ### Either side is swallowed first with positive probability -/

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
/-- The integral equation of the negative tamed flow driven by `s B`, in the form required by QuantumZipper's local
Dynkin formula. -/
theorem negTamed_sDrive_eq (hBc : ∀ ω, Continuous (B · ω)) (s : ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ)
    (ω : Ω) (t : ℝ≥0) :
    negTamed (sDrive s B ω) c x t =
      x + (∫ r in (0 : ℝ)..t, -realDrift c (-negTamed (sDrive s B ω) c x (r.toNNReal : ℝ))) +
        B t ω • (-s) := by
  have e : (fun r => -sDrive s B ω r) = sDrive s (-B) ω := by
    funext r; simp [sDrive]
  have h := realTamed_sDrive_eq (B := -B) (fun ω => (hBc ω).neg) s hc (-x) ω t
  simp only [negTamed, e, neg_neg]
  rw [h, intervalIntegral.integral_neg]
  simp only [Pi.neg_apply, smul_eq_mul]
  ring

/-- **The negative point is swallowed first with positive probability** (§A.4.1). For ordinary chordal `SLE_κ`,
`κ > 4`, and real points `p < 0 < q`, there is an event `E`, measurable for the σ-algebra of the driving Brownian
path, with `P(E) > 0`, on which almost surely `p` is swallowed at a time `σ` at which `q` is still alive (a solution
of the centered flow from `q` exists on `[0, σ]`).

Proof: `F(a, b) = Φ(b/(b − a))` is harmonic for the two-point process (`dynkinGen_oppF`) and bounded between `Φ(0)`
and `Φ(1)`. QuantumZipper's local Dynkin formula, stopped on leaving `{a ≤ −1/L, b ≥ 1/L}`, gives `E g_L = F(p, q) >
Φ(0)` for the stopped values `g_L`. If `q` is swallowed at `σ` (a.s., `ae_exists_realSwallowAt`) while `p` is alive,
then `g_L → Φ(0)` (`stopped_opp_eq`); dominated convergence on the event where `g_L → Φ(0)` bounds the probability of
its complement `E` below by `(F(p, q) − Φ(0))/(Φ(1) − Φ(0))`. On `E`, `p` is swallowed by time `σ`, and not at `σ`
itself (`not_realSwallowAt_both`). -/
theorem exists_measurableSet_swallow_neg_first (hB : IsBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 4 < κ) {p q : ℝ} (hp : p < 0) (hq : 0 < q) :
    ∃ E : Set Ω,
      MeasurableSet[MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω) MeasurableSpace.pi] E ∧
      0 < P E ∧ ∀ᵐ ω ∂P, ω ∈ E →
        ∃ σ, RealSwallowAt (drive κ B ω) p σ ∧ ∃ v, IsForwardSol (drive κ B ω) (q : ℂ) σ v := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hκ0 : 0 < κ := by linarith
  set s := √κ with hsdef
  have hs : s * s = κ := Real.mul_self_sqrt hκ0.le
  have hmB : MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω) MeasurableSpace.pi ≤ mΩ :=
    (measurable_pi_iff.2 hBm).comap_le
  set L₀ := oppScale κ 0 with hL₀
  set L₁ := oppScale κ 1 with hL₁
  set A₀ := max (1 / q) (1 / -p) with hA₀
  set lev : ℕ → ℝ := fun n => (⌈A₀⌉₊ : ℝ) + 2 + n with hlev
  have hlevA : ∀ n, A₀ + 2 ≤ lev n := fun n => by
    simp only [hlev]; linarith [Nat.le_ceil A₀, (n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hA₀pos : 0 ≤ A₀ := (le_max_left _ _).trans' (by positivity)
  have hlevpos : ∀ n, 0 < lev n := fun n => by linarith [hlevA n]
  set c : ℕ → ℝ := fun n => 1 / (2 * lev n) with hcdef
  have hc : ∀ n, 0 < c n := fun n => by have := hlevpos n; positivity
  have hcL : ∀ n, c n ≤ 1 / lev n := fun n => by
    have := hlevpos n
    simp only [hcdef]
    rw [div_le_div_iff₀ (by positivity) this]; linarith
  set T : ℕ → ℝ≥0 := fun n => (lev n).toNNReal with hTdef
  have hTlev : ∀ n, (T n : ℝ) = lev n := fun n => Real.coe_toNNReal _ (hlevpos n).le
  set U : ℕ → ℝ≥0 → Ω → ℝ × ℝ := fun n t ω =>
    (negTamed (sDrive s B ω) (c n) p t, realTamed (sDrive s B ω) (c n) q t) with hUdef
  have hcontP : ∀ n ω, Continuous fun r : ℝ =>
      realDrift (c n) (realTamed (sDrive s B ω) (c n) q (r.toNNReal : ℝ)) := by
    intro n ω
    have h1 := (lipschitz_realDrift (hc n)).continuous
    have h2 : Continuous fun r : ℝ => realTamed (sDrive s B ω) (c n) q (r.toNNReal : ℝ) :=
      (Dynkin.continuous_of_integralEq (U := fun t ω => realTamed (sDrive s B ω) (c n) q t) hBc h1
        (fun y => by rw [Real.norm_eq_abs]; exact abs_realDrift_le (hc n) y)
        (fun ω t => realTamed_sDrive_eq hBc s (hc n) q ω t) ω).comp continuous_real_toNNReal
    exact h1.comp h2
  have hcontN : ∀ n ω, Continuous fun r : ℝ =>
      -realDrift (c n) (-negTamed (sDrive s B ω) (c n) p (r.toNNReal : ℝ)) := by
    intro n ω
    have h1 : Continuous fun y : ℝ => -realDrift (c n) (-y) :=
      ((lipschitz_realDrift (hc n)).continuous.comp continuous_neg).neg
    have h2 : Continuous fun r : ℝ => negTamed (sDrive s B ω) (c n) p (r.toNNReal : ℝ) :=
      (Dynkin.continuous_of_integralEq (U := fun t ω => negTamed (sDrive s B ω) (c n) p t) hBc h1
        (fun y => by rw [Real.norm_eq_abs, abs_neg]; exact abs_realDrift_le (hc n) _)
        (fun ω t => negTamed_sDrive_eq hBc s (hc n) p ω t) ω).comp continuous_real_toNNReal
    exact h1.comp h2
  have hUeq : ∀ n ω (t : ℝ≥0), U n t ω = (p, q) +
      (∫ r in (0 : ℝ)..t, oppDrift (c n) (U n r.toNNReal ω)) + B t ω • ((-s, -s) : ℝ × ℝ) := by
    intro n ω t
    have hI := intervalIntegral_prodMk (hcontN n ω) (hcontP n ω) 0 t
    simp only [hUdef, oppDrift]
    rw [hI, negTamed_sDrive_eq hBc s (hc n) p ω t, realTamed_sDrive_eq hBc s (hc n) q ω t]
    simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul]
  have hUc : ∀ n ω, Continuous (U n · ω) := fun n =>
    Dynkin.continuous_of_integralEq hBc (lipschitzWith_oppDrift (hc n)).continuous
      (norm_oppDrift_le (hc n)) (hUeq n)
  have hU0 : ∀ n ω, U n 0 ω = (p, q) := fun n ω => by rw [hUeq n ω 0]; simp [hB0 ω]
  have hxyK : ∀ n, (p, q) ∈ oppK (lev n) := by
    intro n
    have hA := hlevA n
    refine ⟨?_, ?_⟩
    · show p ≤ -(1 / lev n)
      have h1 : 1 / -p ≤ lev n := by linarith [le_max_right (1 / q) (1 / -p)]
      rw [div_le_iff₀ (neg_pos.2 hp)] at h1
      rw [le_neg, div_le_iff₀ (hlevpos n)]
      linarith
    · show 1 / lev n ≤ q
      have h1 : 1 / q ≤ lev n := by linarith [le_max_left (1 / q) (1 / -p)]
      rw [div_le_iff₀ hq] at h1
      rw [div_le_iff₀ (hlevpos n)]
      linarith
  set Cl : ℕ → Set (ℝ × ℝ) := fun n => oppCl (lev n) with hCldef
  set K : ℕ → Set (ℝ × ℝ) := fun n => oppK (lev n) with hKdef
  have hUK : ∀ n ω (t : ℝ≥0), t ≤ T n → (∀ r < t, U n r ω ∉ Cl n) → U n t ω ∈ K n :=
    fun n ω t _ ht => mem_of_forall_lt_of_isClosed (isClosed_oppK _) (hUc n ω)
      (by rw [hU0]; exact hxyK n) fun r hr => compl_oppCl_subset _ (ht r hr)
  set Mb := max |L₀| |L₁| with hMb
  have hFbd : ∀ x ∈ oppDom, |oppF κ x| ≤ Mb := fun x hx => by
    have h := oppF_mem_Icc hκ hx
    exact abs_le_max_abs_abs h.1 h.2
  have hgen : ∀ n, ∀ x ∈ K n, x ∉ Cl n → dynkinGen (oppDrift (c n)) (-s, -s) (oppF κ) x = 0 :=
    fun n x hx _ => dynkinGen_oppF hκ0 hs (oppK_subset (hlevpos n) hx)
      (by have := hx.1; linarith [hcL n]) ((hcL n).trans hx.2)
  have hmart : ∀ n, Martingale (fun t ω => oppF κ (U n (min t
      (hittingBtwn (U n) (Cl n) 0 (T n) ω)) ω)) (NonSwallow.bmFilt hBm) P := fun n =>
    FrozenMart.martingale_localDynkin_stopped hB.toIsPreBrownianReal hBc (NonSwallow.bmFilt hBm)
      (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm)
      (lipschitzWith_oppDrift (hc n)) (norm_oppDrift_le (hc n)) (hUeq n)
      isOpen_oppDom (isClosed_oppCl _) (isClosed_oppK _)
      (oppK_subset (hlevpos n)) contDiffOn_oppF (hgen n)
      (T n) (hUK n) fun x hx => hFbd x (oppK_subset (hlevpos n) hx)
  set τ : ℕ → Ω → ℝ≥0 := fun n => hittingBtwn (U n) (Cl n) 0 (T n) with hτdef
  set g : ℕ → Ω → ℝ := fun n ω => oppF κ (U n (min (T n) (τ n ω)) ω) with hgdef
  have hgint : ∀ n, ∫ ω, g n ω ∂P = oppF κ (p, q) := by
    intro n
    have h := (hmart n).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T n) MeasurableSet.univ
    simp only [setIntegral_univ] at h
    have hleft : ∫ ω, oppF κ (U n (min 0 (τ n ω)) ω) ∂P = oppF κ (p, q) := by
      have : ∀ ω, oppF κ (U n (min 0 (τ n ω)) ω) = oppF κ (p, q) := fun ω => by
        rw [min_eq_left zero_le, hU0]
      rw [integral_congr_ae (ae_of_all _ this)]
      simp
    rw [hleft] at h
    exact h.symm
  have hgK : ∀ n ω, U n (min (T n) (τ n ω)) ω ∈ K n := fun n ω => by
    rw [min_eq_right (hittingBtwn_le ω)]
    exact hUK n ω _ (hittingBtwn_le ω) fun q hq => notMem_of_lt_hittingBtwn hq zero_le
  have hgbd : ∀ n ω, g n ω ∈ Icc L₀ L₁ := fun n ω =>
    oppF_mem_Icc hκ (oppK_subset (hlevpos n) (hgK n ω))
  have hgmeas : ∀ n, Measurable[MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω)
      MeasurableSpace.pi] (g n) := fun n =>
    (((hmart n).1 (T n)).measurable).mono (bmFilt_le_comap hBm _) le_rfl
  set E : Set Ω := ⋃ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n),
    {ω | L₀ + 1 / ((k : ℝ) + 1) ≤ g n ω} with hEdef
  have hEm : MeasurableSet[MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω)
      MeasurableSpace.pi] E :=
    MeasurableSet.iUnion fun k => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun _ => measurableSet_le measurable_const (hgmeas n)
  have hEm' : MeasurableSet E := hmB _ hEm
  have hEc : ∀ ω ∈ Eᶜ, Tendsto (fun n => g n ω) atTop (𝓝 L₀) := by
    intro ω hω
    have hω' : ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → g n ω < L₀ + 1 / ((k : ℝ) + 1) := by
      intro k
      by_contra hcon
      push Not at hcon
      exact hω (mem_iUnion.2 ⟨k, mem_iInter.2 fun N => by
        obtain ⟨n, hn, hgn⟩ := hcon N
        exact mem_iUnion₂.2 ⟨n, hn, hgn⟩⟩)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := hω' k
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := (hgbd n ω).1
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  -- the probability of `E`
  have hFxy : L₀ < oppF κ (p, q) := (oppF_mem_Ioo hκ (q := (p, q)) ⟨hp, hq⟩).1
  have hgi : ∀ n, Integrable (g n) P := fun n => (hmart n).integrable (T n) |>.congr
    (ae_of_all _ fun ω => rfl)
  have hlim : Tendsto (fun n => ∫ ω in Eᶜ, g n ω ∂P) atTop (𝓝 (∫ ω in Eᶜ, L₀ ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Mb)
      (fun n => ((hgmeas n).mono hmB le_rfl).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun ω => ?_) (ae_restrict_of_forall_mem hEm'.compl hEc)
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hgbd n ω).1 (hgbd n ω).2
  have hle : ∀ n, oppF κ (p, q) ≤ L₁ * P.real E + ∫ ω in Eᶜ, g n ω ∂P := by
    intro n
    rw [← hgint n, ← integral_add_compl hEm' (hgi n)]
    gcongr
    calc ∫ ω in E, g n ω ∂P ≤ ∫ ω in E, L₁ ∂P :=
          setIntegral_mono (hgi n).integrableOn (integrable_const _) fun ω => (hgbd n ω).2
      _ = L₁ * P.real E := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hfin : oppF κ (p, q) ≤ L₁ * P.real E + L₀ * P.real Eᶜ := by
    have h := ge_of_tendsto' (hlim.const_add (L₁ * P.real E)) hle
    rw [setIntegral_const, smul_eq_mul] at h
    linarith
  rw [probReal_compl_eq_one_sub hEm'] at hfin
  have hpos : 0 < P.real E := by
    by_contra h
    push Not at h
    have h0 : P.real E = 0 := le_antisymm h measureReal_nonneg
    rw [h0] at hfin
    linarith
  have hPE : 0 < P E := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [measureReal_def, h, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  refine ⟨E, hEm, hPE, ?_⟩
  -- pathwise: on `E`, `p` is swallowed while `q` is alive
  filter_upwards [ae_exists_realSwallowAt hB hBm hBc hB0 hκ hq] with ω ⟨σ, hσ⟩ hωE
  set W := drive κ B ω with hWdef
  have hW : Continuous W := drive_continuous (hBc ω)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, hB0 ω]
  have hσ0 := hσ.1
  by_cases halive : ∃ wp, IsForwardSol W (p : ℂ) σ wp
  swap
  · obtain ⟨σp, hσp, hsw⟩ := exists_realSwallowAt_of_neg hW hW0 hp hσ0.le halive
    have hlt : σp < σ := by
      rcases hσp.2.lt_or_eq with h | h
      · exact h
      · exact (not_realSwallowAt_both hW hW0 hp hq hsw (h ▸ hσ)).elim
    exact ⟨σp, hsw, hσ.2.1 σp ⟨hσp.1.le, hlt⟩⟩
  exfalso
  obtain ⟨wp, hwp⟩ := halive
  obtain ⟨m, hm, hmle⟩ := exists_pos_re_le_neg_of_isForwardSol hW hW0 hp hσ0.le hwp
  -- eventually the level exceeds all the bounds
  have hlevtop : Tendsto lev atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n in atTop, max σ (1 / m) < lev n :=
    hlevtop.eventually (eventually_gt_atTop _)
  have hεm : ∀ᶠ n in atTop, 0 < 1 / lev n ∧ 1 / lev n < m := by
    filter_upwards [hev] with n hn
    have h4 : 1 / m < lev n := lt_of_le_of_lt (le_max_right _ _) hn
    refine ⟨by have := hlevpos n; positivity, ?_⟩
    rw [div_lt_iff₀ (hlevpos n)]; rw [div_lt_iff₀ hm] at h4; linarith
  have hbnd : ∀ᶠ n in atTop, g n ω ≤ oppScale κ ((1 / lev n) / (1 / lev n + m)) := by
    filter_upwards [hev, hεm] with n hn hε
    have h3 : σ < lev n := lt_of_le_of_lt (le_max_left _ _) hn
    have hpL : ∀ t ∈ Icc (0 : ℝ) σ, (wp t).re < -(1 / lev n) := fun t ht => by
      linarith [hmle t ht, hε.2]
    obtain ⟨hτσ, hY, hX⟩ := stopped_opp_eq (Ω := Ω) (V := U n) (ω := ω) hW hσ hwp
      (hc n) (hcL n) (by rw [hTlev]; exact h3) hpL (fun t => rfl) (hUc n ω)
      (by rw [hU0]; exact hxyK n)
    have hmin : min (T n) (τ n ω) = τ n ω := min_eq_right (hittingBtwn_le ω)
    simp only [hgdef, hmin, oppF]
    rw [hX, hY]
    set Xτ := (wp (τ n ω : ℝ)).re with hXτ
    have hXm : Xτ ≤ -m := hmle _ ⟨(τ n ω).coe_nonneg, hτσ.le⟩
    set ε := 1 / lev n with hεdef
    have hε0 := hε.1
    refine monotoneOn_oppScale hκ ?_ ?_ ?_
    · exact ⟨(div_pos hε0 (by linarith)).le, ((div_le_one (by linarith)).2 (by linarith))⟩
    · exact ⟨(div_pos hε0 (by linarith)).le, ((div_le_one (by linarith)).2 (by linarith))⟩
    · rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  have hbtend : Tendsto (fun n => oppScale κ ((1 / lev n) / (1 / lev n + m))) atTop (𝓝 L₀) := by
    refine (tendsto_oppScale_zero hκ).comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · have h1 : Tendsto (fun n => 1 / lev n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hlevtop
      have h2 := h1.div (h1.add tendsto_const_nhds) (by rw [zero_add]; exact hm.ne')
      rwa [zero_div] at h2
    · filter_upwards [hεm] with n hε
      exact div_pos hε.1 (by linarith [hε.1])
  have hgt : Tendsto (fun n => g n ω) atTop (𝓝 L₀) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbtend
      (Eventually.of_forall fun n => (hgbd n ω).1) hbnd
  -- contradiction with `ω ∈ E`
  obtain ⟨k, hk⟩ := mem_iUnion.1 hωE
  have hev2 : ∀ᶠ n in atTop, g n ω < L₀ + 1 / ((k : ℝ) + 1) :=
    hgt.eventually (gt_mem_nhds (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                                    linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev2
  obtain ⟨n, hn, hgn⟩ := mem_iUnion₂.1 (mem_iInter.1 hk N)
  have := hN n hn
  simp only [mem_ofPred_eq] at hgn
  linarith

/-- **The positive point is swallowed first with positive probability** (§A.4.1, the reflected statement): for
`κ > 4` and `p < 0 < q` there is an event `E` of positive probability, measurable for the driving path, on which
almost surely `q` is swallowed at a time `σ` at which `p` is still alive. Reflection `B ↦ −B`, `x ↦ −x` of
`exists_measurableSet_swallow_neg_first`. -/
theorem exists_measurableSet_swallow_pos_first (hB : IsBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 4 < κ) {p q : ℝ} (hp : p < 0) (hq : 0 < q) :
    ∃ E : Set Ω,
      MeasurableSet[MeasurableSpace.comap (fun ω (r : ℝ≥0) => B r ω) MeasurableSpace.pi] E ∧
      0 < P E ∧ ∀ᵐ ω ∂P, ω ∈ E →
        ∃ σ, RealSwallowAt (drive κ B ω) q σ ∧ ∃ v, IsForwardSol (drive κ B ω) (p : ℂ) σ v := by
  obtain ⟨E, hEm, hEP, hE⟩ := exists_measurableSet_swallow_neg_first hB.neg
    (fun r => (hBm r).neg) (fun ω => (hBc ω).neg) (fun ω => by simp [hB0 ω]) hκ
    (p := -q) (q := -p) (by linarith) (by linarith)
  refine ⟨E, ?_, hEP, ?_⟩
  · obtain ⟨S, hS, rfl⟩ := hEm
    exact ⟨(fun f : ℝ≥0 → ℝ => fun r => -f r) ⁻¹' S, measurable_neg hS, rfl⟩
  · filter_upwards [hE] with ω hω hωE
    obtain ⟨σ, h1, h2⟩ := hω hωE
    have hdrive : drive κ (-B) ω = fun t => -drive κ B ω t := by
      funext t; simp [drive]
    rw [hdrive] at h1 h2
    exact ⟨σ, realSwallowAt_neg_iff.1 h1, exists_isForwardSol_neg_iff.1 h2⟩

end Main

end InteractingSLE.ZhanGT4

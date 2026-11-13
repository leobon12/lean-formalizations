import InteractingSLE.SLE8.ChangeOfMeasure.Core
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import QuantumZipper.Proofs.Probability.StrongMarkov
import MathFin.Probability.Brownian.ExpMartingaleBrownian

/-!
# The critical change of measure (SLE₈ note, Lemma 3.1, (3.6)–(3.9), (3.2))

SLE₈ note `source/sle8-continuity.pdf`, §3.1, pp. 4–5 (transcription `source/sle8/sle8-continuity.md`,
anchors `lem-3.1`, `lem-3.1-proof`).

Setting: `B` a Brownian motion with every path continuous, measurable coordinates and `B 0 = 0`,
whose reverse flow from `iy` (`0 < y ≤ 1`) reaches height `√5` along every path (`ReachesTop`; the
general case is reduced to this one in `InteractingSLE.SLE8.ChangeOfMeasure`).

The height parameter is shifted to start at `0`: `v = u − u₀ = log (Y / y)`, with horizon
`vTop = U − u₀ = log (√5 / y)`.

* `vClock B y v`: the capacity time at which the height parameter reaches `v` (the inverse of the
  note's time change `𝔰`, (3.6)), continued after `vTop` by `topTime + (v − vTop)`;
* `vFilt B y`: the filtration `𝓖_v = 𝓕_{vClock v}` (`𝓕` the natural filtration of `B`);
* `tiltDensity B y = 𝓜_{U} = Φ̂_U² cosh J_U` (3.9), `tiltMeasure = 𝓜_U · P` (the note's `ℚ`);
* `tiltBM B y v`: `J_{u₀+v}/2` for `v ≤ vTop`, continued after `vTop` by the increments of `B` after
  `topTime`.

Main results: `isProbabilityMeasure_tiltMeasure`, `isBrownianReal_tiltBM` (under `ℚ`, `J_{u₀+·} = 2β` with
`β` a Brownian motion: the note's "Brownian motion of variance rate 4"), and `measure_le_tilt` ((3.2)).

The proof is Itô-free: `expTest θ = 𝓜 · e^{θ J − 2θ² u}` has zero Dynkin generator for every `θ`
(`dynkinGen_expTest`), and optional sampling at the height clock (`setLIntegral_stoppedValue_eq`)
gives the exponential-martingale characterization of `J/2` under `ℚ` in the filtration `𝓖`
(MathFin's `isBrownianReal_of_expMartingale`). This replaces the note's SDE construction in the height
parameter, Lévy's characterization and Girsanov's theorem; the true-martingale property of `𝓜`
(Novikov) is the case `θ = 0`.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal

namespace InteractingSLE.SLE8.ChangeOfMeasure

open QuantumZipper QuantumZipper.RS FwdHolo FrozenMart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {y : ℝ}

/-! ### The height-parameter horizon and clock -/

/-- The horizon `vTop = U − u₀ = log (√5 / y)` of the shifted height parameter. -/
def vTop (y : ℝ) : ℝ≥0 := (Real.log (√5 / y)).toNNReal

theorem one_lt_sqrt_five : (1 : ℝ) < √5 := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem coe_vTop (hy : 0 < y) (hy1 : y ≤ 1) : (vTop y : ℝ) = Real.log (√5 / y) := by
  refine Real.coe_toNNReal _ (Real.log_nonneg ?_)
  rw [le_div_iff₀ hy, one_mul]
  exact hy1.trans one_lt_sqrt_five.le

theorem mul_exp_vTop (hy : 0 < y) (hy1 : y ≤ 1) : y * Real.exp (vTop y) = √5 := by
  rw [coe_vTop hy hy1, Real.exp_log (div_pos (by positivity) hy)]
  field_simp

/-- The level `y e^{min v vTop}` of the height. -/
theorem level_le (hy : 0 < y) (hy1 : y ≤ 1) (v : ℝ≥0) :
    y * Real.exp (min (v : ℝ) (vTop y)) ≤ √5 := by
  rw [← mul_exp_vTop hy hy1]
  gcongr
  exact min_le_right _ _

theorem le_level (hy : 0 < y) (v : ℝ≥0) : y ≤ y * Real.exp (min (v : ℝ) (vTop y)) := by
  have : 1 ≤ Real.exp (min (v : ℝ) (vTop y)) :=
    Real.one_le_exp (le_min v.coe_nonneg (vTop y).coe_nonneg)
  nlinarith

/-- The clock of the shifted height parameter: the time at which `log (Y / y)` reaches `v` for
`v ≤ vTop`, continued by `topTime + (v − vTop)`. -/
def vClock (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (v : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  hitTime (drive 8 B ω) y (y * Real.exp (min (v : ℝ) (vTop y))) + (v - vTop y)

omit mΩ in
theorem vClock_of_le (v : ℝ≥0) (hv : v ≤ vTop y) (ω : Ω) :
    vClock B y v ω = hitTime (drive 8 B ω) y (y * Real.exp v) := by
  rw [vClock, tsub_eq_zero_of_le hv, add_zero, min_eq_left (by exact_mod_cast hv)]

omit mΩ in
theorem vClock_vTop (hy : 0 < y) (hy1 : y ≤ 1) (ω : Ω) : vClock B y (vTop y) ω = topTime B y ω := by
  rw [vClock_of_le _ le_rfl, mul_exp_vTop hy hy1, topTime]

omit mΩ in
theorem vClock_of_ge (hy : 0 < y) (hy1 : y ≤ 1) (v : ℝ≥0) (hv : vTop y ≤ v) (ω : Ω) :
    vClock B y v ω = topTime B y ω + (v - vTop y) := by
  rw [vClock, min_eq_right (by exact_mod_cast hv), mul_exp_vTop hy hy1, topTime]

omit mΩ in
theorem reach_level (hreach : ReachesTop B y) (hy : 0 < y) (hy1 : y ≤ 1) (v : ℝ≥0) (ω : Ω) :
    ∃ s : ℝ≥0, y * Real.exp (min (v : ℝ) (vTop y)) ≤ (htZ (drive 8 B ω) y s).im :=
  let ⟨s, hs⟩ := hreach ω; ⟨s, (level_le hy hy1 v).trans hs⟩

theorem vClock_mono (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (hy1 : y ≤ 1)
    (hreach : ReachesTop B y) (ω : Ω) : Monotone fun v => vClock B y v ω := by
  intro v w hvw
  simp only [vClock]
  refine add_le_add (hitTime_mono (continuous_drive8 hBc ω) hy ?_
    (reach_level hreach hy hy1 w ω)) (tsub_le_tsub_right hvw _)
  gcongr

theorem vClock_le_topTime (hy : 0 < y) (hy1 : y ≤ 1) (hBc : ∀ ω, Continuous (B · ω))
    (hreach : ReachesTop B y) {v : ℝ≥0} (hv : v ≤ vTop y) (ω : Ω) :
    vClock B y v ω ≤ topTime B y ω := by
  rw [← vClock_vTop hy hy1 ω]
  exact vClock_mono hBc hy hy1 hreach ω hv

/-- The clock is a stopping time of the natural filtration. -/
theorem isStoppingTime_vClock (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    (hy : 0 < y) (hy1 : y ≤ 1) (hreach : ReachesTop B y) (v : ℝ≥0) :
    IsStoppingTime (NonSwallow.bmFilt hBm) (fun ω => ((vClock B y v ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  by_cases hdt : v - vTop y ≤ t
  · have : {ω | ((vClock B y v ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        {ω | y * Real.exp (min (v : ℝ) (vTop y)) ≤ (stProc B y (t - (v - vTop y)) ω).1.im} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, vClock, stProc_fst]
      rw [← hitTime_le_iff (continuous_drive8 hBc ω) hy (reach_level hreach hy hy1 v ω)]
      constructor
      · intro h; exact le_tsub_of_add_le_right h
      · intro h
        calc hitTime (drive 8 B ω) y (y * Real.exp (min (v : ℝ) (vTop y))) + (v - vTop y)
            ≤ (t - (v - vTop y)) + (v - vTop y) := by gcongr
          _ = t := tsub_add_cancel_of_le hdt
    rw [this]
    refine (NonSwallow.bmFilt hBm).mono (tsub_le_self : t - (v - vTop y) ≤ t) _ ?_
    exact measurableSet_le measurable_const
      (Complex.measurable_im.comp (measurable_fst.comp (measurable_stProc hBc hBm hy _)))
  · have : {ω | ((vClock B y v ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, vClock, mem_empty_iff_false, iff_false,
        not_le]
      exact lt_of_lt_of_le (not_le.1 hdt) le_add_self
    rw [this]
    exact @MeasurableSet.empty _ (NonSwallow.bmFilt hBm t)

/-- The filtration `𝓖_v = 𝓕_{vClock v}` of the height parameter. -/
def vFilt (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t)) (hy : 0 < y)
    (hy1 : y ≤ 1) (hreach : ReachesTop B y) : Filtration ℝ≥0 mΩ where
  seq v := (isStoppingTime_vClock hBc hBm hy hy1 hreach v).measurableSpace
  mono' _ _ hvw := IsStoppingTime.measurableSpace_mono _ _ fun ω =>
    WithTop.coe_le_coe.2 (vClock_mono hBc hy hy1 hreach ω hvw)
  le' _ := IsStoppingTime.measurableSpace_le _

theorem continuous_vClock (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (hy1 : y ≤ 1)
    (hreach : ReachesTop B y) (ω : Ω) : Continuous fun v => vClock B y v ω := by
  have hW := continuous_drive8 hBc ω
  have hc := continuousOn_hitTime hW hy (cmax := √5) (hy1.trans one_lt_sqrt_five.le) (hreach ω)
  have h1 : Continuous fun v : ℝ≥0 => y * Real.exp (min (v : ℝ) (vTop y)) := by fun_prop
  have h2 : Continuous fun v : ℝ≥0 => (hitTime (drive 8 B ω) y
      (y * Real.exp (min (v : ℝ) (vTop y))) : ℝ) :=
    hc.comp_continuous h1 fun v => level_le hy hy1 v
  have h3 : Continuous fun v : ℝ≥0 => hitTime (drive 8 B ω) y
      (y * Real.exp (min (v : ℝ) (vTop y))) :=
    continuous_induced_rng.2 h2
  exact h3.add (continuous_id.sub continuous_const)

/-! ### The processes and the tilted measure -/

/-- `J_{u₀+v} = arsinh (X / Y)` at the clock, frozen after `vTop`. -/
def vJ (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  jFun (stProc B y (vClock B y (min v (vTop y)) ω) ω).1

/-- `Φ̂_{u₀+v} = e^{L}` at the clock, frozen after `vTop`. -/
def vPhi (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (stProc B y (vClock B y (min v (vTop y)) ω) ω).2

/-- The Brownian motion of the change of measure: `β_v = J_{u₀+v} / 2` for `v ≤ vTop`, continued by the
increments of `B` after `topTime`. -/
def tiltBM (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  vJ B y v ω / 2 + (B (vClock B y (max v (vTop y)) ω) ω - B (topTime B y ω) ω)

/-- The density `𝓜_U = Φ̂_U² cosh J_U` of (3.9) at the horizon. -/
def tiltDensity (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (ω : Ω) : ℝ :=
  expTest 0 (stProc B y (topTime B y ω) ω)

/-- The note's `ℚ`: `dℚ = 𝓜_U dP`. -/
def tiltMeasure (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (y : ℝ) : Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (tiltDensity B y ω)

theorem measurable_jFun : Measurable jFun := by
  unfold jFun
  have : Measurable Real.arsinh := Real.continuous_arsinh.measurable
  fun_prop

theorem continuousOn_jFun : ContinuousOn jFun {z : ℂ | 0 < z.im} := by
  unfold jFun
  refine Real.continuous_arsinh.comp_continuousOn ?_
  exact Complex.continuous_re.continuousOn.div Complex.continuous_im.continuousOn
    fun z hz => (ne_of_gt hz)

omit mΩ in
theorem stProc_vClock_eq_stoppedValue (v : ℝ≥0) (ω : Ω) :
    stProc B y (vClock B y v ω) ω =
      stoppedValue (stProc B y) (fun ω => ((vClock B y v ω : ℝ≥0) : WithTop ℝ≥0)) ω := rfl

section Processes

variable (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t)) (hy : 0 < y) (hy1 : y ≤ 1)
  (hreach : ReachesTop B y)
include hBc hBm hy hy1 hreach

theorem measurable_stProc_vClock {v w : ℝ≥0} (hvw : v ≤ w) :
    Measurable[vFilt hBc hBm hy hy1 hreach w] fun ω => stProc B y (vClock B y v ω) ω := by
  have hprog : IsStronglyProgressive (NonSwallow.bmFilt hBm) (stProc B y) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (measurable_stProc hBc hBm hy t).stronglyMeasurable) (continuous_stProc hBc hy)
  have h := measurable_stoppedValue hprog (isStoppingTime_vClock hBc hBm hy hy1 hreach v)
  refine h.mono ?_ le_rfl
  exact IsStoppingTime.measurableSpace_mono _ (isStoppingTime_vClock hBc hBm hy hy1 hreach w)
    fun ω => WithTop.coe_le_coe.2 (vClock_mono hBc hy hy1 hreach ω hvw)

theorem measurable_B_vClock {v w : ℝ≥0} (hvw : v ≤ w) :
    Measurable[vFilt hBc hBm hy hy1 hreach w] fun ω => B (vClock B y v ω) ω := by
  have hprog : IsStronglyProgressive (NonSwallow.bmFilt hBm) B :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (NonSwallow.bmFilt_adapted hBm t).stronglyMeasurable) hBc
  have h := measurable_stoppedValue hprog (isStoppingTime_vClock hBc hBm hy hy1 hreach v)
  refine h.mono ?_ le_rfl
  exact IsStoppingTime.measurableSpace_mono _ (isStoppingTime_vClock hBc hBm hy hy1 hreach w)
    fun ω => WithTop.coe_le_coe.2 (vClock_mono hBc hy hy1 hreach ω hvw)

theorem measurable_vJ (v : ℝ≥0) : Measurable[vFilt hBc hBm hy hy1 hreach v] (vJ B y v) :=
  measurable_jFun.comp (measurable_fst.comp
    (measurable_stProc_vClock hBc hBm hy hy1 hreach (min_le_left v (vTop y))))

theorem measurable_vPhi (v : ℝ≥0) : Measurable[vFilt hBc hBm hy hy1 hreach v] (vPhi B y v) :=
  Real.measurable_exp.comp (measurable_snd.comp
    (measurable_stProc_vClock hBc hBm hy hy1 hreach (min_le_left v (vTop y))))

theorem measurable_tiltBM (v : ℝ≥0) : Measurable[vFilt hBc hBm hy hy1 hreach v] (tiltBM B y v) := by
  refine ((measurable_vJ hBc hBm hy hy1 hreach v).div_const 2).add ?_
  rcases le_total v (vTop y) with hv | hv
  · have : (fun ω => B (vClock B y (max v (vTop y)) ω) ω - B (topTime B y ω) ω) = fun _ => 0 := by
      funext ω
      rw [max_eq_right hv, vClock_vTop hy hy1, sub_self]
    rw [this]
    exact measurable_const
  · have h1 := measurable_B_vClock hBc hBm hy hy1 hreach (le_of_eq (max_eq_left hv))
    have h2 := measurable_B_vClock hBc hBm hy hy1 hreach hv
    have e : (fun ω => B (vClock B y (max v (vTop y)) ω) ω - B (topTime B y ω) ω) =
        fun ω => B (vClock B y (max v (vTop y)) ω) ω - B (vClock B y (vTop y) ω) ω := by
      funext ω; rw [vClock_vTop hy hy1]
    rw [e]
    exact h1.sub h2

theorem measurable_tiltDensity :
    Measurable[vFilt hBc hBm hy hy1 hreach (vTop y)] (tiltDensity B y) := by
  have e : tiltDensity B y = fun ω => expTest 0 (stProc B y (vClock B y (vTop y) ω) ω) := by
    funext ω; rw [tiltDensity, vClock_vTop hy hy1]
  rw [e]
  exact (measurable_expTest 0).comp (measurable_stProc_vClock hBc hBm hy hy1 hreach le_rfl)

omit hBm in
theorem continuous_stProc_vClock (ω : Ω) :
    Continuous fun v => stProc B y (vClock B y v ω) ω :=
  (continuous_stProc hBc hy ω).comp (continuous_vClock hBc hy hy1 hreach ω)

omit hBm in
theorem continuous_vJ (ω : Ω) : Continuous fun v => vJ B y v ω := by
  have h := (continuous_stProc_vClock hBc hy hy1 hreach ω).comp
    (continuous_id.min (continuous_const : Continuous fun _ : ℝ≥0 => vTop y))
  refine continuousOn_jFun.comp_continuous (continuous_fst.comp h) fun v => ?_
  exact hy.trans_le (le_im_stProc hBc hy _ ω)

omit hBm in
theorem continuous_vPhi (ω : Ω) : Continuous fun v => vPhi B y v ω := by
  have h := (continuous_stProc_vClock hBc hy hy1 hreach ω).comp
    (continuous_id.min (continuous_const : Continuous fun _ : ℝ≥0 => vTop y))
  exact Real.continuous_exp.comp (continuous_snd.comp h)

omit hBm in
theorem continuous_tiltBM (ω : Ω) : Continuous fun v => tiltBM B y v ω := by
  have h1 := continuous_vJ hBc hy hy1 hreach ω
  have h2 : Continuous fun v => B (vClock B y (max v (vTop y)) ω) ω :=
    (hBc ω).comp ((continuous_vClock hBc hy hy1 hreach ω).comp
      (continuous_id.max continuous_const))
  exact (h1.div_const 2).add (h2.sub continuous_const)

omit hBm in
/-- The height at the clock: `Y_{vClock v} = y e^v` for `v ≤ vTop`. -/
theorem im_stProc_vClock {v : ℝ≥0} (hv : v ≤ vTop y) (ω : Ω) :
    (stProc B y (vClock B y v ω) ω).1.im = y * Real.exp v := by
  rw [vClock_of_le v hv, stProc_fst]
  have hreach' := reach_level hreach hy hy1 v ω
  rw [min_eq_left (by exact_mod_cast hv)] at hreach'
  exact im_hitTime (continuous_drive8 hBc ω) hy
    (by nlinarith [Real.one_le_exp v.coe_nonneg]) hreach'

omit mΩ hBc hBm hreach in
theorem tiltBM_of_le {v : ℝ≥0} (hv : v ≤ vTop y) (ω : Ω) :
    tiltBM B y v ω = jFun (stProc B y (vClock B y v ω) ω).1 / 2 := by
  rw [tiltBM, vJ, max_eq_right hv, vClock_vTop hy hy1, sub_self, add_zero, min_eq_left hv]

omit hBm hreach in
theorem tiltBM_zero (hB0 : ∀ ω, B 0 ω = 0) (ω : Ω) : tiltBM B y 0 ω = 0 := by
  rw [tiltBM_of_le hy hy1 (zero_le : (0 : ℝ≥0) ≤ vTop y),
    vClock_of_le 0 (zero_le : (0 : ℝ≥0) ≤ vTop y), NNReal.coe_zero,
    Real.exp_zero, mul_one, hitTime_eq_zero (continuous_drive8 hBc ω) hy le_rfl,
    stProc_zero hBc hB0 hy]
  simp [jFun]

omit hBm in
/-- **The exponential identity.** At the clock, for `v ≤ vTop`,
`𝓜 · e^{θ β_v − θ² v / 2} = y^{θ²/2} · expTest (θ/2)`. -/
theorem expTest_zero_mul_exp {v : ℝ≥0} (hv : v ≤ vTop y) (θ : ℝ) (ω : Ω) :
    expTest 0 (stProc B y (vClock B y v ω) ω) *
        Real.exp (θ * tiltBM B y v ω - θ ^ 2 * (v : ℝ) / 2) =
      y ^ (θ ^ 2 / 2) * expTest (θ / 2) (stProc B y (vClock B y v ω) ω) := by
  rw [tiltBM_of_le hy hy1 hv]
  have hY := im_stProc_vClock hBc hy hy1 hreach hv ω
  have hpos : 0 < (stProc B y (vClock B y v ω) ω).1.im := by rw [hY]; positivity
  rw [expTest_eq_exp 0 hpos, expTest_eq_exp (θ / 2) hpos, Real.rpow_def_of_pos hy, hY,
    Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]
  simp only [jFun]
  rw [hY, mul_assoc, ← Real.exp_add, show ∀ a b c : ℝ, Real.exp a * (b * Real.exp c) =
    b * Real.exp (a + c) from fun a b c => by rw [Real.exp_add]; ring]
  congr 2
  ring

end Processes

/-- `E e^{θ X − θ² r / 2} = 1` for `X ∼ N(0, r)`. -/
theorem lintegral_ofReal_exp_of_hasLaw {X : Ω → ℝ} {r : ℝ≥0} (hX : HasLaw X (gaussianReal 0 r) P)
    (θ : ℝ) : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω - θ ^ 2 * (r : ℝ) / 2)) ∂P = 1 := by
  rw [hX.lintegral_comp (f := fun x => ENNReal.ofReal (Real.exp (θ * x - θ ^ 2 * (r : ℝ) / 2)))
    (by fun_prop)]
  have hi : Integrable (fun x : ℝ => Real.exp (θ * x - θ ^ 2 * (r : ℝ) / 2)) (gaussianReal 0 r) := by
    have := (integrable_exp_mul_gaussianReal (μ := 0) (v := r) θ).mul_const
      (Real.exp (-(θ ^ 2 * (r : ℝ) / 2)))
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only
    rw [← Real.exp_add]; ring_nf
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]
  have h1 : ∫ x, Real.exp (θ * x - θ ^ 2 * (r : ℝ) / 2) ∂gaussianReal 0 r =
      mgf id (gaussianReal 0 r) θ * Real.exp (-(θ ^ 2 * (r : ℝ) / 2)) := by
    rw [mgf, ← integral_mul_const]
    congr 1
    funext x
    simp only [id]
    rw [← Real.exp_add]; ring_nf
  rw [h1, mgf_id_gaussianReal, ← Real.exp_add]
  simp only [zero_mul, zero_add]
  rw [show (r : ℝ) * θ ^ 2 / 2 + -(θ ^ 2 * (r : ℝ) / 2) = 0 by ring, Real.exp_zero,
    ENNReal.ofReal_one]

/-! ### Optional sampling for the exponential test functions -/

theorem y_le_sqrt5 (hy1 : y ≤ 1) : y ≤ √5 := hy1.trans one_lt_sqrt_five.le

section Tilt

variable (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
  (hB0 : ∀ ω, B 0 ω = 0) (hy : 0 < y) (hy1 : y ≤ 1) (hreach : ReachesTop B y)
include hB hBc hBm hB0 hy hy1 hreach

/-- Optional sampling for `expTest θ` between two clock times below the horizon. -/
theorem setLIntegral_expTest_eq (θ : ℝ) {v w : ℝ≥0} (hvw : v ≤ w) (hw : w ≤ vTop y) {A : Set Ω}
    (hA : MeasurableSet[vFilt hBc hBm hy hy1 hreach v] A) :
    ∫⁻ ω in A, ENNReal.ofReal (expTest θ (stProc B y (vClock B y w ω) ω)) ∂P =
      ∫⁻ ω in A, ENNReal.ofReal (expTest θ (stProc B y (vClock B y v ω) ω)) ∂P :=
  setLIntegral_stoppedValue_eq hB hBc hBm hB0 hy (y_le_sqrt5 hy1)
    (contDiffOn_expTest θ) (measurable_expTest θ) (fun _ hx hxy => dynkinGen_expTest θ hx hxy)
    (domConst_pos θ y).le (fun _ h1 h2 h3 => expTest_sq_le θ hy h1 h2 h3)
    (fun _ hx => (expTest_pos θ hx).le) (isStoppingTime_vClock hBc hBm hy hy1 hreach v)
    (isStoppingTime_vClock hBc hBm hy hy1 hreach w)
    (fun ω => WithTop.coe_le_coe.2 (vClock_mono hBc hy hy1 hreach ω hvw))
    (fun ω => WithTop.coe_le_coe.2 (vClock_le_topTime hy hy1 hBc hreach hw ω)) hA

/-- The density against a `𝓖_v`-measurable weight: `∫ ξ 𝓜_U = ∫ ξ 𝓜_{u₀+v}`. -/
theorem lintegral_mul_tiltDensity {v : ℝ≥0} (hv : v ≤ vTop y) {ξ : Ω → ℝ≥0∞}
    (hξ : Measurable[vFilt hBc hBm hy hy1 hreach v] ξ) :
    ∫⁻ ω, ξ ω * ENNReal.ofReal (tiltDensity B y ω) ∂P =
      ∫⁻ ω, ξ ω * ENNReal.ofReal (expTest 0 (stProc B y (vClock B y v ω) ω)) ∂P := by
  have h := lintegral_mul_stoppedValue_eq hB hBc hBm hB0 hy (y_le_sqrt5 hy1)
    (contDiffOn_expTest 0) (measurable_expTest 0) (fun _ hx hxy => dynkinGen_expTest 0 hx hxy)
    (domConst_pos 0 y).le (fun _ h1 h2 h3 => expTest_sq_le 0 hy h1 h2 h3)
    (fun _ hx => (expTest_pos 0 hx).le) (isStoppingTime_vClock hBc hBm hy hy1 hreach v)
    (isStoppingTime_vClock hBc hBm hy hy1 hreach (vTop y))
    (fun ω => WithTop.coe_le_coe.2 (vClock_mono hBc hy hy1 hreach ω hv))
    (fun ω => WithTop.coe_le_coe.2 (vClock_le_topTime hy hy1 hBc hreach le_rfl ω)) hξ
  have e : ∀ ω, stoppedValue (stProc B y) (fun ω => ((vClock B y (vTop y) ω : ℝ≥0) : WithTop ℝ≥0))
      ω = stProc B y (topTime B y ω) ω := fun ω => by
    rw [← stProc_vClock_eq_stoppedValue, vClock_vTop hy hy1]
  simp only [e] at h
  exact h

omit hB hBm hB0 hy1 hreach in
theorem tiltDensity_nonneg (ω : Ω) : 0 ≤ tiltDensity B y ω :=
  (expTest_pos 0 (hy.trans_le (le_im_stProc hBc hy _ ω))).le

omit hB hB0 in
theorem measurable_tiltDensity' : Measurable (tiltDensity B y) :=
  (measurable_tiltDensity hBc hBm hy hy1 hreach).mono ((vFilt hBc hBm hy hy1 hreach).le _) le_rfl

/-- `ℚ` is a probability measure (`E 𝓜_U = 1`). -/
theorem isProbabilityMeasure_tiltMeasure : IsProbabilityMeasure (tiltMeasure P B y) := by
  constructor
  rw [tiltMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := lintegral_mul_tiltDensity hB hBc hBm hB0 hy hy1 hreach
    (zero_le : (0 : ℝ≥0) ≤ vTop y) (ξ := fun _ => 1) measurable_const
  simp only [one_mul] at h
  rw [h]
  have e : ∀ ω, stProc B y (vClock B y 0 ω) ω = (((y : ℂ) * I), 0) := fun ω => by
    rw [vClock_of_le 0 (zero_le : (0 : ℝ≥0) ≤ vTop y), NNReal.coe_zero, Real.exp_zero, mul_one,
      hitTime_eq_zero (continuous_drive8 hBc ω) hy le_rfl, stProc_zero hBc hB0 hy]
  simp only [e]
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h1 : expTest 0 (((y : ℂ) * I), 0) = 1 := by
    simp [expTest, expProfile]
  rw [h1, ENNReal.ofReal_one, lintegral_const, measure_univ, one_mul]

/-- The exponential weight `e^{θ β_v − θ² v / 2}`. -/
def expWeight (B : ℝ≥0 → Ω → ℝ) (y θ : ℝ) (v : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ * tiltBM B y v ω - θ ^ 2 * (v : ℝ) / 2))

omit hB hB0 in
theorem measurable_expWeight (θ : ℝ) (v : ℝ≥0) :
    Measurable[vFilt hBc hBm hy hy1 hreach v] (expWeight B y θ v) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((measurable_tiltBM hBc hBm hy hy1 hreach v).const_mul θ).sub_const _))

/-- Below the horizon, the tilted exponential weight is `y^{θ²/2} expTest (θ/2)` under `P`. -/
theorem setLIntegral_expWeight_tilt (θ : ℝ) {v : ℝ≥0} (hv : v ≤ vTop y) {A : Set Ω}
    (hA : MeasurableSet[vFilt hBc hBm hy hy1 hreach v] A) :
    ∫⁻ ω in A, expWeight B y θ v ω ∂tiltMeasure P B y =
      ENNReal.ofReal (y ^ (θ ^ 2 / 2)) *
        ∫⁻ ω in A, ENNReal.ofReal (expTest (θ / 2) (stProc B y (vClock B y v ω) ω)) ∂P := by
  have hAm : MeasurableSet A := (vFilt hBc hBm hy hy1 hreach).le v A hA
  have hwm := measurable_expWeight hBc hBm hy hy1 hreach θ v
  rw [tiltMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _
    (measurable_tiltDensity' hBc hBm hy hy1 hreach).ennreal_ofReal
    (hwm.mono ((vFilt hBc hBm hy hy1 hreach).le v) le_rfl) hAm]
  rw [← lintegral_indicator hAm]
  have e1 : A.indicator ((fun ω => ENNReal.ofReal (tiltDensity B y ω)) * expWeight B y θ v) =
      fun ω => A.indicator (expWeight B y θ v) ω * ENNReal.ofReal (tiltDensity B y ω) := by
    funext ω
    by_cases h : ω ∈ A <;> simp [h, mul_comm]
  rw [e1, lintegral_mul_tiltDensity hB hBc hBm hB0 hy hy1 hreach hv
    ((hwm.indicator hA))]
  rw [← lintegral_indicator hAm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  by_cases h : ω ∈ A
  · simp only [Set.indicator_of_mem h, expWeight]
    rw [mul_comm, ← ENNReal.ofReal_mul (expTest_pos 0
      (hy.trans_le (le_im_stProc hBc hy _ ω))).le,
      expTest_zero_mul_exp hBc hy hy1 hreach hv θ ω,
      ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _)]
  · simp [Set.indicator_of_notMem h]

/-- **The exponential martingale below the horizon.** -/
theorem setLIntegral_expWeight_eq_of_le_vTop (θ : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ vTop y)
    {A : Set Ω} (hA : MeasurableSet[vFilt hBc hBm hy hy1 hreach s] A) :
    ∫⁻ ω in A, expWeight B y θ t ω ∂tiltMeasure P B y =
      ∫⁻ ω in A, expWeight B y θ s ω ∂tiltMeasure P B y := by
  have hAt : MeasurableSet[vFilt hBc hBm hy hy1 hreach t] A :=
    (vFilt hBc hBm hy hy1 hreach).mono hst A hA
  rw [setLIntegral_expWeight_tilt hB hBc hBm hB0 hy hy1 hreach θ ht hAt,
    setLIntegral_expWeight_tilt hB hBc hBm hB0 hy hy1 hreach θ (hst.trans ht) hA,
    setLIntegral_expTest_eq hB hBc hBm hB0 hy hy1 hreach (θ / 2) hst ht hA]

omit mΩ hB hBc hBm hB0 hreach in
/-- After the horizon the clock runs at unit speed. -/
theorem vClock_add {s t : ℝ≥0} (hst : s ≤ t) (hs : vTop y ≤ s) (ω : Ω) :
    vClock B y t ω = vClock B y s ω + (t - s) := by
  rw [vClock_of_ge hy hy1 t (hs.trans hst), vClock_of_ge hy hy1 s hs, add_assoc,
    add_comm (s - vTop y), tsub_add_tsub_cancel hst hs]

omit mΩ hB hBc hBm hB0 hreach in
theorem tiltBM_sub {s t : ℝ≥0} (hst : s ≤ t) (hs : vTop y ≤ s) (ω : Ω) :
    tiltBM B y t ω - tiltBM B y s ω =
      StrongMarkov.smShift B (vClock B y s) (t - s) ω := by
  simp only [tiltBM, vJ, StrongMarkov.smShift, max_eq_left hs, max_eq_left (hs.trans hst),
    min_eq_right hs, min_eq_right (hs.trans hst)]
  rw [vClock_add hy hy1 hst hs]
  ring

omit hB0 in
/-- **The exponential martingale after the horizon** (strong Markov property of `B` at the clock). -/
theorem setLIntegral_expWeight_eq_of_vTop_le (θ : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (hs : vTop y ≤ s)
    {A : Set Ω} (hA : MeasurableSet[vFilt hBc hBm hy hy1 hreach s] A) :
    ∫⁻ ω in A, expWeight B y θ t ω ∂tiltMeasure P B y =
      ∫⁻ ω in A, expWeight B y θ s ω ∂tiltMeasure P B y := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hle := (vFilt hBc hBm hy hy1 hreach).le s
  have hAm : MeasurableSet A := hle A hA
  have hτ := isStoppingTime_vClock hBc hBm hy hy1 hreach s
  have hind := fun r => StrongMarkov.indep_shift_of_le_past hB (NonSwallow.bmFilt_le_past hBm) r
  have hDm : Measurable[vFilt hBc hBm hy hy1 hreach s]
      (fun ω => ENNReal.ofReal (tiltDensity B y ω)) :=
    ENNReal.measurable_ofReal.comp ((measurable_tiltDensity hBc hBm hy hy1 hreach).mono
      ((vFilt hBc hBm hy hy1 hreach).mono hs) le_rfl)
  have hws := measurable_expWeight hBc hBm hy hy1 hreach θ s
  have hwt := measurable_expWeight hBc hBm hy hy1 hreach θ t
  -- the increment factor
  set g : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (θ * p (t - s) - θ ^ 2 * ((t - s : ℝ≥0) : ℝ) / 2)) with hg
  have hgm : Measurable g := by
    simp only [hg]
    fun_prop
  have hsplit : ∀ ω, expWeight B y θ t ω =
      expWeight B y θ s ω * g (StrongMarkov.smPath B (vClock B y s) ω) := by
    intro ω
    have h := tiltBM_sub (B := B) hy hy1 hst hs ω
    simp only [expWeight, hg, StrongMarkov.smPath]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← h, NNReal.coe_sub hst]
    congr 2
    ring
  set f : Ω → ℝ≥0∞ := A.indicator fun ω => ENNReal.ofReal (tiltDensity B y ω) *
    expWeight B y θ s ω with hf
  have hfm : Measurable[vFilt hBc hBm hy hy1 hreach s] f := (hDm.mul hws).indicator hA
  have hindep : IndepFun f (g ∘ StrongMarkov.smPath B (vClock B y s)) P := by
    have := StrongMarkov.indepFun_smPath hB hBc hBm hind hτ (ξ := f) hfm
    exact this.comp measurable_id hgm
  have hBM := StrongMarkov.isBrownianReal_smShift hB hBc hBm hind hτ
  have hone : ∫⁻ ω, (g ∘ StrongMarkov.smPath B (vClock B y s)) ω ∂P = 1 := by
    simp only [hg, StrongMarkov.smPath, Function.comp]
    exact lintegral_ofReal_exp_of_hasLaw (hBM.toIsPreBrownianReal.hasLaw_eval (t - s)) θ
  have hsm : Measurable (g ∘ StrongMarkov.smPath B (vClock B y s)) :=
    hgm.comp (StrongMarkov.measurable_smPath hBc hBm (StrongMarkov.measurable_of_isStoppingTime hτ))
  rw [tiltMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _ (hDm.mono hle le_rfl)
      (hwt.mono ((vFilt hBc hBm hy hy1 hreach).le t) le_rfl) hAm,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (hDm.mono hle le_rfl) (hws.mono hle le_rfl) hAm,
    ← lintegral_indicator hAm, ← lintegral_indicator hAm]
  have e1 : A.indicator ((fun ω => ENNReal.ofReal (tiltDensity B y ω)) * expWeight B y θ t) =
      f * (g ∘ StrongMarkov.smPath B (vClock B y s)) := by
    funext ω
    by_cases h : ω ∈ A
    · simp only [hf, Set.indicator_of_mem h, Pi.mul_apply, Function.comp, hsplit ω]
      ring
    · simp [hf, Set.indicator_of_notMem h]
  have e2 : A.indicator ((fun ω => ENNReal.ofReal (tiltDensity B y ω)) * expWeight B y θ s) = f := by
    funext ω
    simp only [hf]
    rfl
  rw [e1, e2, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hfm.mono hle le_rfl) hsm hindep,
    hone, mul_one]

/-- **The exponential martingale identity** for all times. -/
theorem setLIntegral_expWeight_eq (θ : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[vFilt hBc hBm hy hy1 hreach s] A) :
    ∫⁻ ω in A, expWeight B y θ t ω ∂tiltMeasure P B y =
      ∫⁻ ω in A, expWeight B y θ s ω ∂tiltMeasure P B y := by
  rcases le_total t (vTop y) with ht | ht
  · exact setLIntegral_expWeight_eq_of_le_vTop hB hBc hBm hB0 hy hy1 hreach θ hst ht hA
  rcases le_total (vTop y) s with hs | hs
  · exact setLIntegral_expWeight_eq_of_vTop_le hB hBc hBm hy hy1 hreach θ hst hs hA
  have hA' : MeasurableSet[vFilt hBc hBm hy hy1 hreach (vTop y)] A :=
    (vFilt hBc hBm hy hy1 hreach).mono hs A hA
  rw [setLIntegral_expWeight_eq_of_vTop_le hB hBc hBm hy hy1 hreach θ ht le_rfl hA',
    setLIntegral_expWeight_eq_of_le_vTop hB hBc hBm hB0 hy hy1 hreach θ hs le_rfl hA]

/-- The exponential-martingale data of `β` under `ℚ` (MathFin's `IsExpQMartingale`). -/
theorem isExpQMartingale_tiltBM (T : ℝ≥0) :
    MathFin.IsExpQMartingale (tiltMeasure P B y) (vFilt hBc hBm hy hy1 hreach) (tiltBM B y) T where
  adapted v := (measurable_tiltBM hBc hBm hy hy1 hreach v).stronglyMeasurable
  zero_start := ae_of_all _ fun ω => tiltBM_zero hBc hy hy1 hB0 ω
  martingale θ s t hst _ A hA := by
    have hAm : MeasurableSet A := (vFilt hBc hBm hy hy1 hreach).le s A hA
    have hm : ∀ v : ℝ≥0, Measurable fun ω => Real.exp (θ * tiltBM B y v ω - θ ^ 2 * (v : ℝ) / 2) :=
      fun v => Real.measurable_exp.comp ((((measurable_tiltBM hBc hBm hy hy1 hreach v).mono
        ((vFilt hBc hBm hy hy1 hreach).le v) le_rfl).const_mul θ).sub_const _)
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (Real.exp_pos _).le)
        (hm t).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (Real.exp_pos _).le)
        (hm s).aestronglyMeasurable]
    exact congrArg ENNReal.toReal (setLIntegral_expWeight_eq hB hBc hBm hB0 hy hy1 hreach θ hst hA)

/-- **Under `ℚ`, `β` is a Brownian motion** (and `J_{u₀+v} = 2 β_v` for `v ≤ vTop`). -/
theorem isBrownianReal_tiltBM : IsBrownianReal (tiltBM B y) (tiltMeasure P B y) := by
  have := isProbabilityMeasure_tiltMeasure hB hBc hBm hB0 hy hy1 hreach
  exact MathFin.isBrownianReal_of_expMartingale
    (fun T => isExpQMartingale_tiltBM hB hBc hBm hB0 hy hy1 hreach T)
    (ae_of_all _ fun ω => continuous_tiltBM hBc hy hy1 hreach ω)

/-! ### The bound (3.2) -/

/-- The critical martingale `𝓜_{u₀+v} = Φ̂² cosh J` in the height parameter (frozen after `vTop`). -/
def critMart (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  expTest 0 (stProc B y (vClock B y (min v (vTop y)) ω) ω)

/-- The height parameter `τ_T − u₀ = log (Y_T / y)` of the terminal time `T`. -/
def termLevel (B : ℝ≥0 → Ω → ℝ) (y T : ℝ) (ω : Ω) : ℝ≥0 :=
  (Real.log ((htZ (drive 8 B ω) y T).im / y)).toNNReal

theorem setIntegral_critMart_eq {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[vFilt hBc hBm hy hy1 hreach s] A) :
    ∫ ω in A, critMart B y t ω ∂P = ∫ ω in A, critMart B y s ω ∂P := by
  rcases le_total (vTop y) s with hs | hs
  · simp only [critMart, min_eq_right hs, min_eq_right (hs.trans hst)]
  have hA' : MeasurableSet[(isStoppingTime_vClock hBc hBm hy hy1 hreach
      (min s (vTop y))).measurableSpace] A := by
    rw [min_eq_left hs]; exact hA
  exact setIntegral_stoppedValue_eq hB hBc hBm hB0 hy (y_le_sqrt5 hy1)
    (contDiffOn_expTest 0) (measurable_expTest 0) (fun _ hx hxy => dynkinGen_expTest 0 hx hxy)
    (domConst_pos 0 y).le (fun _ h1 h2 h3 => expTest_sq_le 0 hy h1 h2 h3)
    (isStoppingTime_vClock hBc hBm hy hy1 hreach (min s (vTop y)))
    (isStoppingTime_vClock hBc hBm hy hy1 hreach (min t (vTop y)))
    (fun ω => WithTop.coe_le_coe.2 (vClock_mono hBc hy hy1 hreach ω (min_le_min hst le_rfl)))
    (fun ω => WithTop.coe_le_coe.2 (vClock_le_topTime hy hy1 hBc hreach (min_le_right _ _) ω)) hA'

theorem integrable_critMart (v : ℝ≥0) : Integrable (critMart B y v) P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact (memLp_stoppedValue hB hBc hBm hB0 hy (y_le_sqrt5 hy1)
    (contDiffOn_expTest 0) (measurable_expTest 0) (domConst_pos 0 y).le
    (fun _ h1 h2 h3 => expTest_sq_le 0 hy h1 h2 h3)
    (isStoppingTime_vClock hBc hBm hy hy1 hreach (min v (vTop y)))
    (fun ω => WithTop.coe_le_coe.2 (vClock_le_topTime hy hy1 hBc hreach (min_le_right _ _) ω))
    ).integrable (by norm_num)

omit hB hB0 in
theorem measurable_critMart (v : ℝ≥0) :
    Measurable[vFilt hBc hBm hy hy1 hreach v] (critMart B y v) :=
  (measurable_expTest 0).comp (measurable_stProc_vClock hBc hBm hy hy1 hreach (min_le_left _ _))

/-- `𝓜` is a martingale in the height filtration. -/
theorem martingale_critMart : Martingale (critMart B y) (vFilt hBc hBm hy hy1 hreach) P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun v => (measurable_critMart hBc hBm hy hy1 hreach v).stronglyMeasurable,
    fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((vFilt hBc hBm hy hy1 hreach).le s)
    (integrable_critMart hB hBc hBm hB0 hy hy1 hreach t)
    (fun A _ _ => (integrable_critMart hB hBc hBm hB0 hy hy1 hreach s).integrableOn)
    (fun A hA _ => (setIntegral_critMart_eq hB hBc hBm hB0 hy hy1 hreach hst hA).symm)
    (measurable_critMart hBc hBm hy hy1 hreach s).aestronglyMeasurable).symm

omit hB hBm hB0 in
theorem continuous_critMart (ω : Ω) : Continuous fun v => critMart B y v ω :=
  (contDiffOn_expTest 0).continuousOn.comp_continuous
    ((continuous_stProc_vClock hBc hy hy1 hreach ω).comp
      (continuous_id.min (continuous_const : Continuous fun _ : ℝ≥0 => vTop y)))
    fun _ => hy.trans_le (le_im_stProc hBc hy _ ω)

omit hB hBm hB0 hreach in
theorem termLevel_le {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) (ω : Ω) : termLevel B y T ω ≤ vTop y := by
  have hW := continuous_drive8 hBc ω
  have hY := im_htZ_pos hW hy hT.1
  have h5 : (htZ (drive 8 B ω) y T).im ≤ √5 := by
    have h := im_htZ_sq_le hW hy hT.1
    rw [← Real.sqrt_sq hY.le]
    exact Real.sqrt_le_sqrt (by nlinarith [hT.2])
  rw [termLevel, vTop]
  refine Real.toNNReal_le_toNNReal (Real.log_le_log (div_pos hY hy) ?_)
  exact div_le_div_of_nonneg_right h5 hy.le

omit hB hBm hB0 hreach in
/-- The clock at the terminal level is the terminal time: `𝔰(τ_T) = T`. -/
theorem vClock_termLevel {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) (ω : Ω) :
    (vClock B y (termLevel B y T ω) ω : ℝ) = T := by
  have hW := continuous_drive8 hBc ω
  have hY := im_htZ_pos hW hy hT.1
  rw [vClock_of_le _ (termLevel_le hBc hy hy1 hT ω), termLevel,
    Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hy).2 (le_im_htZ hW hy hT.1))),
    Real.exp_log (div_pos hY hy), mul_div_cancel₀ _ hy.ne']
  have := hitTime_im hW hy T.toNNReal
  rw [Real.coe_toNNReal T hT.1] at this
  rw [this, Real.coe_toNNReal T hT.1]

omit hB hB0 in
/-- `τ_T` is a stopping time of the height filtration. -/
theorem isStoppingTime_termLevel {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) :
    IsStoppingTime (vFilt hBc hBm hy hy1 hreach)
      (fun ω => ((termLevel B y T ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro v
  rcases le_total (vTop y) v with hv | hv
  · have : {ω | ((termLevel B y T ω : ℝ≥0) : WithTop ℝ≥0) ≤ v} = univ := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_univ, iff_true]
      exact (termLevel_le hBc hy hy1 hT ω).trans hv
    rw [this]
    exact @MeasurableSet.univ _ (vFilt hBc hBm hy hy1 hreach v)
  · have : {ω | ((termLevel B y T ω : ℝ≥0) : WithTop ℝ≥0) ≤ v} =
        {ω | ((T.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ((vClock B y v ω : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
      have hW := continuous_drive8 hBc ω
      have hreach' := reach_level hreach hy hy1 v ω
      rw [min_eq_left (by exact_mod_cast hv)] at hreach'
      have hc : y ≤ y * Real.exp v := by nlinarith [Real.one_le_exp v.coe_nonneg]
      have hY := im_htZ_pos hW hy hT.1
      rw [vClock_of_le v hv, termLevel, Real.toNNReal_le_iff_le_coe,
        Real.log_le_iff_le_exp (div_pos hY hy), div_le_iff₀ hy, mul_comm (Real.exp _)]
      have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.1
      constructor
      · intro h
        by_contra hlt
        push Not at hlt
        have h1 := le_im_hitTime hW hy hreach'
        have h2 : (htZ (drive 8 B ω) y (hitTime (drive 8 B ω) y (y * Real.exp v))).im <
            (htZ (drive 8 B ω) y (T.toNNReal : ℝ)).im := strictMono_im_htZ_nnreal hW hy hlt
        rw [hTT] at h2
        linarith
      · intro h
        calc (htZ (drive 8 B ω) y T).im = (htZ (drive 8 B ω) y (T.toNNReal : ℝ)).im := by rw [hTT]
          _ ≤ (htZ (drive 8 B ω) y (hitTime (drive 8 B ω) y (y * Real.exp v))).im :=
              monotone_im_htZ_nnreal hW hy h
          _ = y * Real.exp v := im_hitTime hW hy hc hreach'
    rw [this]
    exact (isStoppingTime_vClock hBc hBm hy hy1 hreach v).measurableSet_ge' _

/-- **(3.2).** For `a > 0` and `E ∈ 𝓖_{τ_T}` with `y Φ_T ≥ a` a.s. on `E`: `P(E) ≤ y² a⁻² ℚ(E)`. -/
theorem measure_le_tilt {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) {a : ℝ} (ha : 0 < a) {E : Set Ω}
    (hE : MeasurableSet[(isStoppingTime_termLevel hBc hBm hy hy1 hreach hT).measurableSpace] E)
    (hEa : ∀ᵐ ω ∂P, ω ∈ E → a ≤ y * ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖) :
    P E ≤ ENNReal.ofReal (y ^ 2 * a ^ (-2 : ℝ)) * tiltMeasure P B y E := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hτ := isStoppingTime_termLevel hBc hBm hy hy1 hreach hT
  have hEm : MeasurableSet E := hτ.measurableSpace_le E hE
  -- optional sampling in the height filtration
  have hos := setIntegral_stoppedValue_eq_of_rightContinuous
    (martingale_critMart hB hBc hBm hB0 hy hy1 hreach)
    (fun ω t => (continuous_critMart hBc hy hy1 hreach ω).continuousWithinAt) hτ
    (isStoppingTime_const _ (vTop y))
    (fun ω => WithTop.coe_le_coe.2 (termLevel_le hBc hy hy1 hT ω)) (T := vTop y)
    (fun ω => le_rfl) hE
  have hL : ∀ ω, stoppedValue (critMart B y) (fun ω => ((termLevel B y T ω : ℝ≥0) :
      WithTop ℝ≥0)) ω = expTest 0 (stProc B y T.toNNReal ω) := by
    intro ω
    show critMart B y (termLevel B y T ω) ω = _
    simp only [critMart, min_eq_left (termLevel_le hBc hy hy1 hT ω)]
    congr 2
    apply NNReal.eq
    rw [vClock_termLevel hBc hy hy1 hT ω, Real.coe_toNNReal T hT.1]
  have hR : ∀ ω, stoppedValue (critMart B y) (fun _ => ((vTop y : ℝ≥0) : WithTop ℝ≥0)) ω =
      tiltDensity B y ω := by
    intro ω
    rw [stoppedValue_const]
    simp only [critMart, min_self, vClock_vTop hy hy1, tiltDensity]
  simp only [hL, hR] at hos
  -- integrability
  have hTtop : ∀ ω, ((T.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (topTime B y ω : WithTop ℝ≥0) := by
    intro ω
    refine WithTop.coe_le_coe.2 ?_
    have h := vClock_le_topTime hy hy1 hBc hreach (termLevel_le hBc hy hy1 hT ω) ω
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal T hT.1, ← vClock_termLevel hBc hy hy1 hT ω]
    exact_mod_cast h
  have hint1 : Integrable (fun ω => expTest 0 (stProc B y T.toNNReal ω)) P := by
    have h := (memLp_stoppedValue hB hBc hBm hB0 hy (y_le_sqrt5 hy1)
      (contDiffOn_expTest 0) (measurable_expTest 0) (domConst_pos 0 y).le
      (fun _ h1 h2 h3 => expTest_sq_le 0 hy h1 h2 h3)
      (isStoppingTime_const (NonSwallow.bmFilt hBm) T.toNNReal) hTtop).integrable (by norm_num)
    simpa only [stoppedValue_const] using h
  have hint2 : Integrable (tiltDensity B y) P := by
    have h := integrable_critMart hB hBc hBm hB0 hy hy1 hreach (vTop y)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [critMart, min_self, vClock_vTop hy hy1, tiltDensity]
  have hnn : ∀ ω, 0 ≤ expTest 0 (stProc B y T.toNNReal ω) := fun ω =>
    (expTest_pos 0 (hy.trans_le (le_im_stProc hBc hy _ ω))).le
  have hQ : tiltMeasure P B y E = ∫⁻ ω in E, ENNReal.ofReal (expTest 0 (stProc B y T.toNNReal ω)) ∂P := by
    rw [tiltMeasure, withDensity_apply _ hEm,
      ← ofReal_integral_eq_lintegral_ofReal hint2.integrableOn
        (ae_of_all _ (tiltDensity_nonneg hBc hy)),
      ← ofReal_integral_eq_lintegral_ofReal hint1.integrableOn (ae_of_all _ hnn), hos]
  -- the pointwise lower bound on `E`
  have hlow : ∀ᵐ ω ∂P.restrict E, ENNReal.ofReal ((a / y) ^ 2) ≤
      ENNReal.ofReal (expTest 0 (stProc B y T.toNNReal ω)) := by
    rw [ae_restrict_iff' hEm]
    filter_upwards [hEa] with ω hω hωE
    refine ENNReal.ofReal_le_ofReal ?_
    have hW := continuous_drive8 hBc ω
    have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.1
    have hphi := snd_stProc_eq hBc hy T.toNNReal ω
    rw [hTT] at hphi
    have hd0 : 0 < ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖ :=
      norm_pos_iff.2 (deriv_revMap_ne_zero _ hW hT.1 (mem_H_mul_I hy))
    have h1 : a / y ≤ ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖ := by
      rw [div_le_iff₀ hy, mul_comm]; exact hω hωE
    have h2 : Real.exp (2 * (stProc B y T.toNNReal ω).2) =
        ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖ ^ 2 := by
      rw [hphi, mul_comm, Real.exp_mul, Real.exp_log hd0]; norm_cast
    have h3 : Real.exp (2 * (stProc B y T.toNNReal ω).2) ≤ expTest 0 (stProc B y T.toNNReal ω) := by
      simp only [expTest, expProfile]
      have : 1 ≤ √(1 + ((stProc B y T.toNNReal ω).1.re / (stProc B y T.toNNReal ω).1.im) ^ 2) :=
        Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ((stProc B y T.toNNReal ω).1.re /
          (stProc B y T.toNNReal ω).1.im)])
      rw [show (-2 : ℝ) * 0 ^ 2 = 0 by norm_num, Real.rpow_zero, mul_one, zero_mul, Real.exp_zero,
        mul_one]
      nlinarith [Real.exp_pos (2 * (stProc B y T.toNNReal ω).2)]
    calc (a / y) ^ 2 ≤ ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = Real.exp (2 * (stProc B y T.toNNReal ω).2) := h2.symm
      _ ≤ _ := h3
  have hmono : ENNReal.ofReal ((a / y) ^ 2) * P E ≤ tiltMeasure P B y E := by
    rw [hQ, ← setLIntegral_const]
    exact lintegral_mono_ae hlow
  have hc : ENNReal.ofReal (y ^ 2 * a ^ (-2 : ℝ)) * ENNReal.ofReal ((a / y) ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_neg ha.le, Real.rpow_two, div_pow]
    rw [show y ^ 2 * (a ^ 2)⁻¹ * (a ^ 2 / y ^ 2) = 1 by field_simp, ENNReal.ofReal_one]
  calc P E = ENNReal.ofReal (y ^ 2 * a ^ (-2 : ℝ)) * ENNReal.ofReal ((a / y) ^ 2) * P E := by
        rw [hc, one_mul]
    _ = ENNReal.ofReal (y ^ 2 * a ^ (-2 : ℝ)) * (ENNReal.ofReal ((a / y) ^ 2) * P E) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (y ^ 2 * a ^ (-2 : ℝ)) * tiltMeasure P B y E := by gcongr

end Tilt

end InteractingSLE.SLE8.ChangeOfMeasure

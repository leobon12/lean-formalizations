import SmallGammaGeodesics.CC.ZoomExt
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Zoom + near-identity coupling (track CC, packet CC4; CC0 Details D6)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D6** (NIC applied to the
global extension, and the sup bound), consumed by CC6 (**D9**, D10); rulings G10, G19, G20, G24.

* `supDev k ρ = sup_{|y| ≤ ρ} |k(y) − k(0)|` in `[0, ∞]`, with `measurable_supDev` (the supremum
  equals one over a countable dense set, by continuity);
* `abs_sub_le_five_circleAverage`: for `k` harmonic on `B_R` and `|y| ≤ R/2`,
  `|k(y) − k(0)| ≤ 5 · avg_{|x| = 3R/4} |k(x) − k(0)|` (Poisson integral formula, Mathlib
  `HarmonicOnNhd.circleAverage_poissonKernel_smul`; the Poisson kernel is at most
  `(3R/4 + R/2)/(3R/4 − R/2) = 5`). This replaces D6's area mean value property;
* `lintegral_supDev_le`: `E sup_{|y| ≤ R/2} |K(y) − K(0)| ≤ 5 √B` when `E(K(x) − K(0))² ≤ B` on the
  circle `|x| = 3R/4` (Tonelli over the circle and `E|X| ≤ (E X²)^{1/2}`);
* `exists_measurable_contExt`: a measurable `C(ℂ, ℝ)`-valued extension of `K` from `B̄_ρ` (D9's `K̃`);
* `IsNICCoupling`: the conclusions of `NICInput` for one near-identity pair, as a structure;
* **`zoom_nic`**: the target of packet CC4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## The supremum of the increments -/

/-- `sup_{|y| ≤ ρ} |k(y) − k(0)|`, in `[0, ∞]` -/
def supDev (k : ℂ → ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  ⨆ y ∈ closedBall (0 : ℂ) ρ, ENNReal.ofReal |k y - k 0|

theorem ofReal_abs_sub_le_supDev {k : ℂ → ℝ} {ρ : ℝ} {y : ℂ} (hy : y ∈ closedBall (0 : ℂ) ρ) :
    ENNReal.ofReal |k y - k 0| ≤ supDev k ρ :=
  le_iSup₂ (f := fun y (_ : y ∈ closedBall (0 : ℂ) ρ) => ENNReal.ofReal |k y - k 0|) y hy

/-- `supDev k ρ < ∞` for `k` continuous on `B̄_ρ` -/
theorem supDev_lt_top {k : ℂ → ℝ} {ρ : ℝ} (hk : ContinuousOn k (closedBall 0 ρ)) :
    supDev k ρ < ⊤ := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
    (hk.sub continuousOn_const)
  refine lt_of_le_of_lt (iSup₂_le fun y hy => ?_) (ENNReal.ofReal_lt_top (r := M))
  refine ENNReal.ofReal_le_ofReal ?_
  have := hM y hy
  rwa [Real.norm_eq_abs] at this

/-- `|k(y) − k(0)| ≤ (supDev k ρ).toReal` on `B̄_ρ`, for `k` continuous on `B̄_ρ` -/
theorem abs_sub_le_toReal_supDev {k : ℂ → ℝ} {ρ : ℝ} (hk : ContinuousOn k (closedBall 0 ρ))
    {y : ℂ} (hy : y ∈ closedBall (0 : ℂ) ρ) : |k y - k 0| ≤ (supDev k ρ).toReal := by
  have h := ofReal_abs_sub_le_supDev (k := k) hy
  rwa [← ENNReal.ofReal_toReal (supDev_lt_top hk).ne,
    ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at h

/-- **Measurability of the supremum**: by continuity it is a supremum over a countable dense subset
of `B̄_ρ`. -/
theorem measurable_supDev {Ω : Type*} [MeasurableSpace Ω] {K : Ω → ℂ → ℝ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hKm : Measurable (fun p : Ω × ℂ => K p.1 p.2))
    (hK : ∀ ω, ContinuousOn (K ω) (ball 0 R)) : Measurable (fun ω => supDev (K ω) ρ) := by
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense ℂ
  set D : Set ℂ := ball (0 : ℂ) ρ ∩ D₀ with hD
  have hDc : D.Countable := hD₀c.mono inter_subset_right
  have hclos : closedBall (0 : ℂ) ρ ⊆ closure D := by
    rw [← closure_ball (0 : ℂ) hρ.ne']
    exact closure_minimal (hD₀d.open_subset_closure_inter isOpen_ball) isClosed_closure
  have hDsub : ∀ y ∈ D, y ∈ closedBall (0 : ℂ) ρ := fun y hy => ball_subset_closedBall hy.1
  have heq : ∀ ω, supDev (K ω) ρ = ⨆ y ∈ D, ENNReal.ofReal |K ω y - K ω 0| := fun ω => by
    refine le_antisymm (iSup₂_le fun y hy => ?_) (biSup_mono hDsub)
    set S := ⨆ y ∈ D, ENNReal.ofReal |K ω y - K ω 0| with hS
    by_contra hlt
    push Not at hlt
    have hyR : y ∈ ball (0 : ℂ) R :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hy) hρR)
    have hcont : ContinuousAt (fun x => ENNReal.ofReal |K ω x - K ω 0|) y :=
      ENNReal.continuous_ofReal.continuousAt.comp
        (continuous_abs.continuousAt.comp
          (((hK ω).continuousAt (isOpen_ball.mem_nhds hyR)).sub continuousAt_const))
    have hev : ∀ᶠ x in 𝓝 y, S < ENNReal.ofReal |K ω x - K ω 0| :=
      Filter.Tendsto.eventually_const_lt hlt hcont
    obtain ⟨x, hxD, hx⟩ := ((mem_closure_iff_frequently.1 (hclos hy)).and_eventually hev).exists
    exact absurd (le_iSup₂ (f := fun x (_ : x ∈ D) => ENNReal.ofReal |K ω x - K ω 0|) x hxD)
      (not_le.2 hx)
  simp_rw [heq]
  refine Measurable.biSup D hDc fun y _ => ?_
  have h1 : Measurable fun ω => K ω y := hKm.comp (measurable_id.prodMk measurable_const)
  have h0 : Measurable fun ω => K ω 0 := hKm.comp (measurable_id.prodMk measurable_const)
  exact (continuous_abs.measurable.comp (h1.sub h0)).ennreal_ofReal

/-! ## The Poisson bound -/

/-- On the circle `|x| = a`, the Poisson kernel at `y` with `|y| ≤ R/2`, `a = 3R/4`, lies in
`[0, 5]`. -/
theorem poissonKernel_mem_Icc {R : ℝ} (hR : 0 < R) {x y : ℂ} (hx : ‖x‖ = 3 * R / 4)
    (hy : ‖y‖ ≤ R / 2) : 0 ≤ poissonKernel 0 y x ∧ poissonKernel 0 y x ≤ 5 := by
  simp only [poissonKernel_def, sub_zero]
  have hd : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
  have hy0 := norm_nonneg y
  have hpos : 0 < ‖x - y‖ := by linarith
  have hden : 0 < ‖x - y‖ ^ 2 := by positivity
  have hd' : 0 ≤ ‖x‖ - ‖y‖ := by linarith
  refine ⟨div_nonneg ?_ hden.le, (div_le_iff₀ hden).2 ?_⟩
  · have h1 : 0 ≤ (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) := mul_nonneg hd' (by linarith)
    nlinarith [h1]
  · have hsq : (‖x‖ - ‖y‖) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ hd' hd 2
    have h1 : 0 ≤ (‖x‖ - ‖y‖) * (4 * ‖x‖ - 6 * ‖y‖) := mul_nonneg hd' (by linarith)
    nlinarith [h1, hsq]

/-- **Sup bound by the Poisson integral formula**: for `k` harmonic on `B_R` and `|y| ≤ R/2`,
`|k(y) − k(0)| ≤ 5 · avg_{|x| = 3R/4} |k(x) − k(0)|`. -/
theorem abs_sub_le_five_circleAverage {k : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hk : InnerProductSpace.HarmonicOnNhd k (ball 0 R)) {y : ℂ} (hy : ‖y‖ ≤ R / 2) :
    |k y - k 0| ≤ 5 * Real.circleAverage (fun x => |k x - k 0|) 0 (3 * R / 4) := by
  set u : ℂ → ℝ := fun x => k x - k 0 with hu
  have hu_harm : InnerProductSpace.HarmonicOnNhd u (ball 0 R) :=
    hk.sub (InnerProductSpace.harmonicOnNhd_const (k 0))
  have hsub : closedBall (0 : ℂ) (3 * R / 4) ⊆ ball 0 R := closedBall_subset_ball (by linarith)
  have hyb : y ∈ ball (0 : ℂ) (3 * R / 4) := mem_ball_zero_iff.2 (by linarith)
  have hpoisson := (hu_harm.mono hsub).circleAverage_poissonKernel_smul hyb
  have habsR : |3 * R / 4| = 3 * R / 4 := abs_of_pos (by positivity)
  have hsph : ∀ x ∈ sphere (0 : ℂ) |3 * R / 4|, ‖x‖ = 3 * R / 4 := fun x hx => by
    rw [habsR] at hx; simpa using hx
  have hsph_ball : sphere (0 : ℂ) |3 * R / 4| ⊆ ball 0 R := fun x hx =>
    mem_ball_zero_iff.2 (by rw [hsph x hx]; linarith)
  have hucont : ContinuousOn u (sphere (0 : ℂ) |3 * R / 4|) :=
    (hu_harm.continuousOn).mono hsph_ball
  have hPcont : ContinuousOn (poissonKernel 0 y) (sphere (0 : ℂ) |3 * R / 4|) := by
    have hne : ∀ x ∈ sphere (0 : ℂ) |3 * R / 4|, ‖x - 0 - (y - 0)‖ ^ 2 ≠ 0 := fun x hx => by
      have hx' := hsph x hx
      have : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
      rw [sub_zero, sub_zero]
      have : 0 < ‖x - y‖ := by linarith
      positivity
    have e : poissonKernel 0 y =
        fun x => (‖x - 0‖ ^ 2 - ‖y - 0‖ ^ 2) / ‖x - 0 - (y - 0)‖ ^ 2 :=
      funext fun x => poissonKernel_def 0 y x
    rw [e]
    exact ContinuousOn.div (by fun_prop) (by fun_prop) hne
  have hint1 : CircleIntegrable |poissonKernel 0 y • u| 0 (3 * R / 4) :=
    ((hPcont.mul hucont).abs).circleIntegrable'
  have hint2 : CircleIntegrable (fun x => (5 : ℝ) • |u x|) 0 (3 * R / 4) :=
    (continuousOn_const.mul hucont.abs).circleIntegrable'
  calc |k y - k 0| = |u y| := rfl
    _ = |Real.circleAverage (poissonKernel 0 y • u) 0 (3 * R / 4)| := by rw [hpoisson]
    _ ≤ Real.circleAverage |poissonKernel 0 y • u| 0 (3 * R / 4) :=
        Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun x => (5 : ℝ) • |u x|) 0 (3 * R / 4) := by
        refine Real.circleAverage_mono hint1 hint2 fun x hx => ?_
        obtain ⟨hP0, hP5⟩ := poissonKernel_mem_Icc hR (hsph x hx) hy
        simp only [Pi.abs_apply, Pi.mul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hP0]
        exact mul_le_mul_of_nonneg_right hP5 (abs_nonneg _)
    _ = 5 * Real.circleAverage (fun x => |k x - k 0|) 0 (3 * R / 4) := by
        rw [Real.circleAverage_fun_smul, smul_eq_mul]

/-! ## The expectation of the supremum -/

/-- `E|X| ≤ (E X²)^{1/2}` -/
theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, |X ω| ∂P ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) := by
  have hvar := variance_eq_sub hX.abs
  have hnn := variance_nonneg (|X|) P
  have e : ∫ ω, (|X| ^ 2) ω ∂P = ∫ ω, X ω ^ 2 ∂P := by
    congr 1; funext ω; simp [sq_abs]
  rw [e] at hvar
  refine (Real.le_sqrt (integral_nonneg fun ω => abs_nonneg _)
    (integral_nonneg fun ω => sq_nonneg _)).2 ?_
  have e2 : ∫ ω, |X| ω ∂P = ∫ ω, |X ω| ∂P := rfl
  rw [e2] at hvar
  linarith

/-- **`E sup_{|y| ≤ R/2} |K(y) − K(0)| ≤ 5 √B`** (CC0 D6), for `K` jointly measurable and harmonic
on `B_R`, with `K(x) − K(0) ∈ L²` and `E(K(x) − K(0))² ≤ B` on the circle `|x| = 3R/4`. -/
theorem lintegral_supDev_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {K : Ω → ℂ → ℝ} {R B : ℝ} (hR : 0 < R)
    (hKm : Measurable (fun p : Ω × ℂ => K p.1 p.2))
    (hK : ∀ ω, InnerProductSpace.HarmonicOnNhd (K ω) (ball 0 R))
    (hL2 : ∀ x : ℂ, ‖x‖ = 3 * R / 4 → MemLp (fun ω => K ω x - K ω 0) 2 P)
    (hincr : ∀ x : ℂ, ‖x‖ = 3 * R / 4 → ∫ ω, (K ω x - K ω 0) ^ 2 ∂P ≤ B) :
    ∫⁻ ω, supDev (K ω) (R / 2) ∂P ≤ ENNReal.ofReal (5 * Real.sqrt B) := by
  set a : ℝ := 3 * R / 4 with ha
  have ha0 : 0 < a := by positivity
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 a θ‖ = a := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos ha0]
  have hmemball : ∀ θ : ℝ, circleMap 0 a θ ∈ ball (0 : ℂ) R := fun θ =>
    mem_ball_zero_iff.2 (by rw [hnorm θ]; linarith)
  set G : Ω → ℝ → ℝ := fun ω θ => |K ω (circleMap 0 a θ) - K ω 0| with hG
  have hGcont : ∀ ω, Continuous (G ω) := fun ω =>
    continuous_abs.comp
      (((hK ω).continuousOn.comp_continuous (continuous_circleMap 0 a) hmemball).sub
        continuous_const)
  -- step 1: the pointwise Poisson bound
  have hpt : ∀ ω, supDev (K ω) (R / 2) ≤
      ENNReal.ofReal 5 * ENNReal.ofReal (Real.circleAverage (fun x => |K ω x - K ω 0|) 0 a) :=
    fun ω => by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      refine iSup₂_le fun y hy => ENNReal.ofReal_le_ofReal ?_
      exact abs_sub_le_five_circleAverage hR (hK ω) (mem_closedBall_zero_iff.1 hy)
  -- step 2: the circle average as a set lintegral
  have hcirc : ∀ ω, ENNReal.ofReal (Real.circleAverage (fun x => |K ω x - K ω 0|) 0 a) =
      ENNReal.ofReal (2 * Real.pi)⁻¹ *
        ∫⁻ θ in Ioc 0 (2 * Real.pi), ENNReal.ofReal (G ω θ) := fun ω => by
    rw [Real.circleAverage_def, smul_eq_mul,
      intervalIntegral.integral_of_le Real.two_pi_pos.le,
      ENNReal.ofReal_mul (inv_nonneg.2 Real.two_pi_pos.le)]
    congr 1
    exact ofReal_integral_eq_lintegral_ofReal (hGcont ω).integrableOn_Ioc
      (ae_of_all _ fun θ => abs_nonneg _)
  -- step 3: the bound at one point of the circle
  have hpoint : ∀ θ : ℝ, ∫⁻ ω, ENNReal.ofReal (G ω θ) ∂P ≤ ENNReal.ofReal (Real.sqrt B) :=
    fun θ => by
      have hX := hL2 _ (hnorm θ)
      rw [← ofReal_integral_eq_lintegral_ofReal ((hX.integrable one_le_two).abs)
        (ae_of_all _ fun ω => abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal
        ((integral_abs_le_sqrt_integral_sq hX).trans (Real.sqrt_le_sqrt (hincr _ (hnorm θ))))
  -- step 4: Tonelli
  have hjoint : Measurable (Function.uncurry fun ω θ => ENNReal.ofReal (G ω θ)) := by
    have h1 : Measurable fun q : Ω × ℝ => K q.1 (circleMap 0 a q.2) :=
      hKm.comp (measurable_fst.prodMk ((continuous_circleMap 0 a).measurable.comp measurable_snd))
    have h0 : Measurable fun q : Ω × ℝ => K q.1 0 :=
      hKm.comp (measurable_fst.prodMk measurable_const)
    exact (continuous_abs.measurable.comp (h1.sub h0)).ennreal_ofReal
  have hswap := lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Ioc 0 (2 * Real.pi)))
    hjoint.aemeasurable
  calc ∫⁻ ω, supDev (K ω) (R / 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal 5 * (ENNReal.ofReal (2 * Real.pi)⁻¹ *
          ∫⁻ θ in Ioc 0 (2 * Real.pi), ENNReal.ofReal (G ω θ)) ∂P :=
        lintegral_mono fun ω => (hpt ω).trans_eq (by rw [hcirc ω])
    _ = ENNReal.ofReal 5 * (ENNReal.ofReal (2 * Real.pi)⁻¹ *
          ∫⁻ ω, (∫⁻ θ in Ioc 0 (2 * Real.pi), ENNReal.ofReal (G ω θ)) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal 5 * (ENNReal.ofReal (2 * Real.pi)⁻¹ *
          ∫⁻ θ in Ioc 0 (2 * Real.pi), ∫⁻ ω, ENNReal.ofReal (G ω θ) ∂P) := by
        rw [hswap]
    _ ≤ ENNReal.ofReal 5 * (ENNReal.ofReal (2 * Real.pi)⁻¹ *
          ∫⁻ _θ in Ioc 0 (2 * Real.pi), ENNReal.ofReal (Real.sqrt B)) := by
        gcongr with θ
        exact hpoint θ
    _ = ENNReal.ofReal (5 * Real.sqrt B) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul
          (Real.sqrt_nonneg B), ← ENNReal.ofReal_mul (inv_nonneg.2 Real.two_pi_pos.le),
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        field_simp

/-! ## A measurable continuous extension (the `K̃` of CC0 D9) -/

/-- **A measurable continuous extension of `K` from `B̄_ρ`** (the `K̃` of CC0 D9): for `K` jointly
measurable and continuous on `B_R` and `0 < ρ < R`, there is a measurable `K̃ : Ω → C(ℂ, ℝ)` with
`K̃ ω = K ω` on `B̄_ρ` and `K̃ ω = 0` off `B_R` (`K̃ = b · K` with a bump `b`, `= 1` on `B̄_ρ`,
supported in `B̄_{(ρ+R)/2}`). -/
theorem exists_measurable_contExt {Ω : Type*} [MeasurableSpace Ω] {K : Ω → ℂ → ℝ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hKm : Measurable (fun p : Ω × ℂ => K p.1 p.2))
    (hK : ∀ ω, ContinuousOn (K ω) (ball 0 R)) :
    ∃ Kt : Ω → C(ℂ, ℝ), Measurable Kt ∧ (∀ ω, ∀ x ∈ closedBall (0 : ℂ) ρ, Kt ω x = K ω x) ∧
      ∀ ω x, R ≤ ‖x‖ → Kt ω x = 0 := by
  set b : ContDiffBump (0 : ℂ) := ⟨ρ, (ρ + R) / 2, hρ, by linarith⟩ with hb
  have hzero : ∀ x : ℂ, (ρ + R) / 2 ≤ ‖x‖ → b x = 0 := fun x hx =>
    b.zero_of_le_dist (by rw [dist_zero_right]; exact hx)
  have hcont : ∀ ω, Continuous fun x => b x * K ω x := fun ω => by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ ball (0 : ℂ) R
    · exact b.continuous.continuousAt.mul ((hK ω).continuousAt (isOpen_ball.mem_nhds hx))
    · have hx' : (ρ + R) / 2 < ‖x‖ := by
        rw [mem_ball_zero_iff, not_lt] at hx; linarith
      have hev : (fun x => b x * K ω x) =ᶠ[𝓝 x] fun _ => 0 :=
        Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx')
          fun w hw => by
            show b w * K ω w = 0
            rw [hzero w (le_of_lt hw), zero_mul]
      exact continuousAt_const.congr hev.symm
  refine ⟨fun ω => ⟨fun x => b x * K ω x, hcont ω⟩, ?_, fun ω x hx => ?_, fun ω x hx => ?_⟩
  · exact ContinuousMap.measurable_iff_eval.2 fun x =>
      measurable_const.mul (hKm.comp (measurable_id.prodMk measurable_const))
  · show b x * K ω x = K ω x
    rw [b.one_of_mem_closedBall hx, one_mul]
  · show b x * K ω x = 0
    rw [hzero x (by linarith), zero_mul]

/-! ## The near-identity coupling as a structure -/

/-- **The conclusions of `NICInput`** for one near-identity pair `(Φ, U)` (`Φ = Ψ⁻¹`, `Ψ` holomorphic
on `U`), with increment constant `B` (`= C ε²` in `NICInput`): `h ∘ Ψ = h̄ + K` on `U`, i.e.
`⟨h, |det DΦ| (g ∘ Φ)⟩ = ⟨h̄, g⟩ + ∫ K g` for `g` supported in `U`, with `K` jointly measurable,
harmonic on `U`, with centred Gaussian increments and `E(K z − K w)² ≤ B min(t, 1 + log(1 + t))`. -/
structure IsNICCoupling {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Φ : ℂ → ℂ) (U : Set ℂ)
    (B : ℝ) (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ) : Prop where
  isWholePlaneGFF : IsWholePlaneGFF h P
  isWholePlaneGFF_bar : IsWholePlaneGFF hbar P
  measurable : Measurable (fun p : Ω × ℂ => K p.1 p.2)
  harmonic : ∀ ω, InnerProductSpace.HarmonicOnNhd (K ω) U
  gaussian : IsGaussianProcess (fun (p : U × U) (ω : Ω) => K ω p.1 - K ω p.2) P
  centred : ∀ p : U × U, ∫ ω, (K ω p.1 - K ω p.2) ∂P = 0
  coupling : ∀ᵐ ω ∂P, ∀ g τg : TestC, tsupport (g : ℂ → ℝ) ⊆ U →
      (∀ x, τg x = |LinearMap.det (fderiv ℝ Φ x : ℂ →ₗ[ℝ] ℂ)| * g (Φ x)) →
      h ω τg = hbar ω g + ∫ y, K ω y * g y
  incr : ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ U → closedBall w s ⊆ U →
      ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤ B * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s))

/-- `NICInput`, with its conclusions packaged as `IsNICCoupling`. -/
theorem NICInput.exists_isNICCoupling (hNIC : NICInput) : ∃ ε₀ C₀ : ℝ, 0 < ε₀ ∧ 0 < C₀ ∧
    ∀ (Φ Ψ : ℂ → ℂ) (U : Set ℂ) (ε : ℝ), IsOpen U → 0 ≤ ε → ε ≤ ε₀ →
      IsNearIdDiffeo Φ Ψ U ε →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ), IsNICCoupling P Φ U (C₀ * ε ^ 2) h hbar K := by
  obtain ⟨ε₀, C₀, hε₀, hC₀, hN⟩ := hNIC
  refine ⟨ε₀, C₀, hε₀, hC₀, fun Φ Ψ U ε hU hε0 hε hΦ => ?_⟩
  obtain ⟨Ω, mΩ, P, hP, h, hbar, K, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hN Φ Ψ U ε hU hε0 hε hΦ
  exact ⟨Ω, mΩ, P, hP, h, hbar, K, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- `min(t, 1 + log(1 + t)) ≥ 0` for `t ≥ 0` -/
private theorem min_log_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ min t (1 + Real.log (1 + t)) :=
  le_min ht (by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + t); linarith)

/-- `IsNICCoupling` is monotone in the increment constant. -/
theorem IsNICCoupling.mono {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Φ : ℂ → ℂ}
    {U : Set ℂ} {B B' : ℝ} {h hbar : Ω → DistC} {K : Ω → ℂ → ℝ}
    (hc : IsNICCoupling P Φ U B h hbar K) (hBB' : B ≤ B') : IsNICCoupling P Φ U B' h hbar K :=
  ⟨hc.isWholePlaneGFF, hc.isWholePlaneGFF_bar, hc.measurable, hc.harmonic, hc.gaussian, hc.centred,
    hc.coupling, fun z w s hs hz hw => (hc.incr z w s hs hz hw).trans
      (mul_le_mul_of_nonneg_right hBB' (min_log_nonneg (by positivity)))⟩

/-- **The sup bound for a NIC coupling on `B_R`** (CC0 D6): `sup_{|y| ≤ R/2} |K(y) − K(0)|` is
measurable and `E sup_{|y| ≤ R/2} |K(y) − K(0)| ≤ 5 (6B)^{1/2}`. -/
theorem IsNICCoupling.supDev_bound {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Φ : ℂ → ℂ} {R B : ℝ} {h hbar : Ω → DistC} {K : Ω → ℂ → ℝ}
    (hc : IsNICCoupling P Φ (ball 0 R) B h hbar K) (hR : 0 < R) (hB : 0 ≤ B) :
    Measurable (fun ω => supDev (K ω) (R / 2)) ∧
      ∫⁻ ω, supDev (K ω) (R / 2) ∂P ≤ ENNReal.ofReal (5 * Real.sqrt (6 * B)) := by
  refine ⟨measurable_supDev (by positivity) (by linarith) hc.measurable
    fun ω => (hc.harmonic ω).continuousOn, ?_⟩
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hxR : ∀ x : ℂ, ‖x‖ = 3 * R / 4 → x ∈ ball (0 : ℂ) R := fun x hx =>
    mem_ball_zero_iff.2 (by rw [hx]; linarith)
  refine lintegral_supDev_le hR hc.measurable hc.harmonic (fun x hx => ?_) (fun x hx => ?_)
  · exact (hc.gaussian.hasGaussianLaw_eval (⟨x, hxR x hx⟩, ⟨0, h0⟩)).memLp_two
  · have hs : (0 : ℝ) < R / 8 := by positivity
    have hzs : closedBall x (R / 8) ⊆ ball (0 : ℂ) R := fun w hw => by
      rw [mem_closedBall, dist_eq_norm] at hw
      have : ‖w‖ ≤ ‖w - x‖ + ‖x‖ := by
        calc ‖w‖ = ‖(w - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
      exact mem_ball_zero_iff.2 (by linarith)
    have hws : closedBall (0 : ℂ) (R / 8) ⊆ ball (0 : ℂ) R := closedBall_subset_ball (by linarith)
    refine (hc.incr x 0 (R / 8) hs hzs hws).trans ?_
    have hmin : min (‖x - 0‖ / (R / 8)) (1 + Real.log (1 + ‖x - 0‖ / (R / 8))) ≤ 6 := by
      refine (min_le_left _ _).trans (le_of_eq ?_)
      rw [sub_zero, hx]
      field_simp
      ring
    calc B * min (‖x - 0‖ / (R / 8)) (1 + Real.log (1 + ‖x - 0‖ / (R / 8))) ≤ B * 6 :=
          mul_le_mul_of_nonneg_left hmin hB
      _ = 6 * B := by ring

/-! ## The target -/

/-- **Zoom + near-identity coupling (packet CC4; CC0 Details D6).** Let `IsConfNbhd ϕ W V`, let `ψ`
be a left inverse of `ϕ` on `W`, let `Kc ⊆ V` be compact and `R > 0`. Given the near-identity
coupling `NICInput` (an interface, ruling G10), there are `r₁ > 0` and `C > 0` such that for every
`z ∈ Kc` and `r ∈ (0, r₁]`:
* the global extension `Ξ = zoomExt ϕ ψ z r R` of the zoomed inverse map
  `χ_{z,r}(y) = ϕ'(z) r⁻¹ (ψ(ϕ z + r y) − z)` has an inverse `Ξinv`, with `IsZoomExt` (Taylor bounds,
  `Ξ = χ_{z,r}` on `B̄_R`, `Ξ = id` off `B_{2R}`, and `IsNearIdDiffeo Ξinv Ξ (ball 0 R) (C r)`);
* on a probability space `(Ω, P)` there are whole-plane GFFs `h, h̄` and `K` forming the NIC coupling
  of `(Φ, Ψ, U) = (Ξinv, Ξ, B_R)` (`IsNICCoupling`, increment constant `C r²`): `h ∘ Ξ = h̄ + K` on
  `B_R`, i.e. `h ∘ χ_{z,r} = h̄ + K` there;
* `sup_{|y| ≤ R/2} |K(y) − K(0)|` is measurable and its expectation is at most `C r`.

Moreover `C r₁ ≤ 1/32`, so `NIC.NearIdPair.ofDiffeo` applies to the pair `(Ξinv, Ξ)`. -/
theorem zoom_nic (hNIC : NICInput) {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V)
    (hψ : ∀ x ∈ W, ψ (ϕ x) = x) {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcV : Kc ⊆ V)
    {R : ℝ} (hR : 0 < R) :
    ∃ r₁ C : ℝ, 0 < r₁ ∧ 0 < C ∧ C * r₁ ≤ 1 / 32 ∧ ∀ z ∈ Kc, ∀ r ∈ Ioc (0 : ℝ) r₁,
      ∃ Ξinv : ℂ → ℂ, IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (h hbar : Ω → DistC) (K : Ω → ℂ → ℝ),
        IsNICCoupling P Ξinv (ball 0 R) (C * r ^ 2) h hbar K ∧
        Measurable (fun ω => supDev (K ω) (R / 2)) ∧
        ∫⁻ ω, supDev (K ω) (R / 2) ∂P ≤ ENNReal.ofReal (C * r) := by
  obtain ⟨ε₀, C₀, hε₀, hC₀, hN⟩ := hNIC.exists_isNICCoupling
  obtain ⟨r₁, A, hr₁, hA, hAr₁, hext⟩ := hϕ.exists_zoomExt hψ hKc hKcV hR hε₀
  set C : ℝ := A + C₀ * A ^ 2 + 5 * Real.sqrt (6 * C₀) * A with hCdef
  have hsq0 : 0 ≤ Real.sqrt (6 * C₀) := Real.sqrt_nonneg _
  have hC0 : 0 < C := by positivity
  have hAC : A ≤ C := by
    have : 0 ≤ C₀ * A ^ 2 := by positivity
    have : 0 ≤ 5 * Real.sqrt (6 * C₀) * A := by positivity
    linarith
  set r₂ : ℝ := min r₁ (1 / (32 * C)) with hr₂def
  have hr₂ : 0 < r₂ := lt_min hr₁ (by positivity)
  have hCr₂ : C * r₂ ≤ 1 / 32 :=
    calc C * r₂ ≤ C * (1 / (32 * C)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC0.le
      _ = 1 / 32 := by field_simp
  refine ⟨r₂, C, hr₂, hC0, hCr₂, fun z hz r hr => ?_⟩
  obtain ⟨hr0, hrr₂⟩ := hr
  have hrr₁ : r ≤ r₁ := hrr₂.trans (min_le_left _ _)
  obtain ⟨Ξinv, hZ⟩ := hext z hz r ⟨hr0, hrr₁⟩
  have hεle : A * r ≤ ε₀ := (mul_le_mul_of_nonneg_left hrr₁ hA.le).trans hAr₁
  obtain ⟨Ω, mΩ, P, hP, h, hbar, K, hc⟩ :=
    hN Ξinv (zoomExt ϕ ψ z r R) (ball 0 R) (A * r) isOpen_ball (by positivity) hεle hZ.nearId
  refine ⟨Ξinv, hZ.mono hAC hr0.le, Ω, mΩ, P, hP, h, hbar, K, hc.mono ?_, ?_⟩
  · have : C₀ * A ^ 2 ≤ C := by
      have : 0 ≤ 5 * Real.sqrt (6 * C₀) * A := by positivity
      linarith
    calc C₀ * (A * r) ^ 2 = (C₀ * A ^ 2) * r ^ 2 := by ring
      _ ≤ C * r ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
  · obtain ⟨hmeas, hint⟩ := hc.supDev_bound hR (by positivity)
    refine ⟨hmeas, hint.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have e : Real.sqrt (6 * (C₀ * (A * r) ^ 2)) = Real.sqrt (6 * C₀) * (A * r) := by
      rw [show 6 * (C₀ * (A * r) ^ 2) = (6 * C₀) * (A * r) ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [e]
    have : 5 * Real.sqrt (6 * C₀) * A ≤ C := by
      have : 0 ≤ C₀ * A ^ 2 := by positivity
      linarith
    calc 5 * (Real.sqrt (6 * C₀) * (A * r)) = (5 * Real.sqrt (6 * C₀) * A) * r := by ring
      _ ≤ C * r := mul_le_mul_of_nonneg_right this hr0.le

end SmallGammaGeodesics.CC

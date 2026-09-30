import QuantumZipper.Proofs.GFF.CircleMeanValue
import QuantumZipper.Proofs.GFF.CoordRegHarm
import QuantumZipper.Proofs.LQG.CoordChangeKernel
import QuantumZipper.Proofs.GFF.Admissible

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, step (a): the Neumann energy of a pushed circle minus the image circle

Let `ψ` be analytic near the closed disc `B̄(z, r) ⊆ H̄`, mapping it into `ℍ`, and `η`-close to
an affine map of slope `a ≠ 0` there:
`‖ψ u − ψ w − a (u − w)‖ ≤ η ‖a‖ ‖u − w‖` (`η ≤ 1/2`). Put `c = ψ z`, `ρ = r ‖a‖ ≤ Im c`,
`μ₁ = ψ_* fc(z, r)`, `μ₂ = fc(c, ρ)`. Then (`abs_kernelCov2_push_circle_le`)

  `|kernelCov2 neumannH (μ₁, μ₂) (μ₁, μ₂)| ≤ 4 η`,

i.e. the variance of `X(μ₁) − X(μ₂)` for the free field is `O(η)`; with `a = ψ'(z)` and
Cauchy estimates, `η = O(r)` uniformly on compacts (Koebe-type distortion).

Proof (all integrals exact, by mean values and Jensen-type circle averages):
* the reflected parts cancel: `w ↦ log‖ψ w − p̄‖` is `log` of a nonvanishing holomorphic function
  on the disc (`p ∈ H̄`), so its `fc(z, r)`-mean is `log‖c − p̄‖` (mean value property, mathlib
  `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`), and so is the `fc(c, ρ)`-mean of
  `log‖· − p̄‖` (`integral_log_norm_sub_circleUnif`); every term carries `−log‖c − c̄‖`;
* `∫ log‖x − y‖ dμ₂(y) = log max(ρ, ‖x − c‖)`, which on `supp μ₁` is `log ρ + [0, log(1 + η)]`;
* `∫∫ log‖ψ u − ψ w‖ = ∫∫ log‖u − w‖ + log‖a‖ + [log(1 − η), log(1 + η)] = log ρ + O(η)`.

This is the harmonic-measure computation of the planned proof (module docstring of
`AreaPCReduce.lean`), done here by circle means instead of the maximum principle: the energy of
`μ₁ − μ₂` is `∬ (U₁ − U₂) d(μ₁ − μ₂)` with logarithmic potentials agreeing up to `O(η)` on the
supports. Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (circle-average
variances); Garnett–Marshall, *Harmonic Measure*, Ch. I (harmonic measure, mean value property).
The explicit comparison is an own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ComplexConjugate

namespace QuantumZipper.E6
namespace XAreaPC

/-- An a.e. bounded function on a probability space is integrable, with integral in the bounds. -/
theorem xpc_integral_bounds {μ : Measure ℂ} [IsProbabilityMeasure μ] {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f μ) {lo hi : ℝ} (h : ∀ᵐ x ∂μ, lo ≤ f x ∧ f x ≤ hi) :
    Integrable f μ ∧ lo ≤ ∫ x, f x ∂μ ∧ ∫ x, f x ∂μ ≤ hi := by
  have hint : Integrable f μ := by
    refine (integrable_const (|lo| + |hi|)).mono' hf (h.mono fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [neg_abs_le lo, abs_nonneg hi, hx.1],
      by linarith [le_abs_self hi, abs_nonneg lo, hx.2]⟩
  refine ⟨hint, ?_, ?_⟩
  · have := integral_mono_ae (integrable_const lo) hint (h.mono fun x hx => hx.1)
    simpa using this
  · have := integral_mono_ae hint (integrable_const hi) (h.mono fun x hx => hx.2)
    simpa using this

/-- Inner integral of the Neumann kernel against a folded circle (in the second variable). -/
theorem xpc_inner_fc (c : ℂ) (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ y, neumannH x y ∂foldedCircle c ρ =
      -Real.log (max ρ ‖c - x‖) - Real.log (max ρ ‖c - conj x‖) := by
  rw [show (fun y => neumannH x y) = (fun y => neumannH y x) from
    funext fun y => neumannH_symm x y]
  exact integral_neumannH_foldedCircle c x hρ

/-- Hypotheses: `ψ` is analytic near `B̄(z, r) ⊆ H̄`, maps it into `ℍ`, and is `η`-close to the
affine map of slope `a` there; the image circle `∂B(ψ z, r‖a‖)` lies in `H̄`. -/
structure PushCircHyp (ψ : ℂ → ℂ) (z a : ℂ) (r η : ℝ) : Prop where
  r_pos : 0 < r
  r_le_im : r ≤ z.im
  meas : Measurable ψ
  analytic : AnalyticOnNhd ℂ ψ (closedBall z r)
  im_pos : ∀ u ∈ closedBall z r, 0 < (ψ u).im
  a_ne : a ≠ 0
  eta_nonneg : 0 ≤ η
  eta_le : η ≤ 1 / 2
  lin : ∀ u ∈ closedBall z r, ∀ w ∈ closedBall z r,
    ‖ψ u - ψ w - a * (u - w)‖ ≤ η * ‖a‖ * ‖u - w‖
  rho_le : r * ‖a‖ ≤ (ψ z).im

variable {ψ : ℂ → ℂ} {z a : ℂ} {r η : ℝ}

namespace PushCircHyp

variable (h : PushCircHyp ψ z a r η)
include h

theorem norm_a_pos : 0 < ‖a‖ := norm_pos_iff.2 h.a_ne

theorem rho_pos : 0 < r * ‖a‖ := mul_pos h.r_pos h.norm_a_pos

/-- Two-sided distortion bound. -/
theorem dist_bounds {u w : ℂ} (hu : u ∈ closedBall z r) (hw : w ∈ closedBall z r) :
    (1 - η) * (‖a‖ * ‖u - w‖) ≤ ‖ψ u - ψ w‖ ∧ ‖ψ u - ψ w‖ ≤ (1 + η) * (‖a‖ * ‖u - w‖) := by
  have e := h.lin u hu w hw
  have t1 := norm_sub_norm_le (ψ u - ψ w) (a * (u - w))
  have t2 := norm_sub_norm_le (a * (u - w)) (ψ u - ψ w)
  rw [norm_sub_rev (a * (u - w))] at t2
  rw [norm_mul] at t1 t2
  constructor <;> nlinarith

/-- Log form of the distortion bound, off the diagonal. -/
theorem log_bounds {u w : ℂ} (hu : u ∈ closedBall z r) (hw : w ∈ closedBall z r) (huw : u ≠ w) :
    Real.log ‖u - w‖ + Real.log ((1 - η) * ‖a‖) ≤ Real.log ‖ψ u - ψ w‖ ∧
      Real.log ‖ψ u - ψ w‖ ≤ Real.log ‖u - w‖ + Real.log ((1 + η) * ‖a‖) := by
  have hd : 0 < ‖u - w‖ := norm_pos_iff.2 (sub_ne_zero.2 huw)
  have ha := h.norm_a_pos
  have h1 : 0 < 1 - η := by linarith [h.eta_le]
  have h2 : 0 < 1 + η := by linarith [h.eta_nonneg]
  obtain ⟨b1, b2⟩ := h.dist_bounds hu hw
  have hp : 0 < ‖ψ u - ψ w‖ := lt_of_lt_of_le (by positivity) b1
  constructor
  · rw [← Real.log_mul hd.ne' (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  · rw [← Real.log_mul hd.ne' (by positivity)]
    exact Real.log_le_log hp (by nlinarith)

theorem z_mem_Hbar : z ∈ Hbar := by
  show 0 ≤ z.im
  linarith [h.r_pos, h.r_le_im]

theorem fc_eq : foldedCircle z r = circleUnif z r :=
  foldedCircle_eq_circleUnif h.r_pos.le h.r_le_im

theorem fc_img_eq : foldedCircle (ψ z) (r * ‖a‖) = circleUnif (ψ z) (r * ‖a‖) :=
  foldedCircle_eq_circleUnif h.rho_pos.le h.rho_le

theorem ae_sphere : ∀ᵐ u ∂circleUnif z r, u ∈ closedBall z r ∧ ‖u - z‖ = r := by
  filter_upwards [CircleMV.ae_circleUnif z r] with u hu
  rw [abs_of_pos h.r_pos] at hu
  exact ⟨by rw [mem_closedBall, dist_eq_norm, hu], hu⟩

/-- Mean value property: the `fc(z, r)`-mean of `log‖ψ − p̄‖` for `p ∈ H̄`. -/
theorem integral_log_reflect {p : ℂ} (hp : 0 ≤ p.im) :
    ∫ w, Real.log ‖ψ w - conj p‖ ∂circleUnif z r = Real.log ‖ψ z - conj p‖ := by
  refine CoordReg.integral_log_norm_circleUnif_of_analytic (h.meas.sub_const _) h.r_pos.le
    (h.analytic.sub analyticOnNhd_const) fun u hu => ?_
  intro h0
  have := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
  linarith [h.im_pos u hu]

/-- Continuous-on-the-disc functions are integrable over the circle. -/
theorem integrable_of_continuousOn {g : ℂ → ℝ} (hgm : Measurable g)
    (hg : ContinuousOn g (closedBall z r)) : Integrable g (circleUnif z r) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hg
  refine (integrable_const C).mono' hgm.aestronglyMeasurable ?_
  filter_upwards [h.ae_sphere] with u hu
  exact hC u hu.1

theorem continuousOn_log_reflect {p : ℂ} (hp : 0 ≤ p.im) :
    ContinuousOn (fun w => Real.log ‖ψ w - conj p‖) (closedBall z r) := by
  refine ((h.analytic.continuousOn.sub continuousOn_const).norm).log fun u hu => ?_
  rw [norm_ne_zero_iff]
  intro h0
  have := congrArg Complex.im h0
  simp only [Pi.sub_apply, Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
  linarith [h.im_pos u hu]

theorem integrable_log_reflect {p : ℂ} (hp : 0 ≤ p.im) :
    Integrable (fun w => Real.log ‖ψ w - conj p‖) (circleUnif z r) :=
  h.integrable_of_continuousOn (Real.measurable_log.comp (h.meas.sub_const _).norm)
    (h.continuousOn_log_reflect hp)

/-! ### The image-circle terms -/

theorem kc22 :
    kernelCov neumannH (foldedCircle (ψ z) (r * ‖a‖)) (foldedCircle (ψ z) (r * ‖a‖)) =
      -Real.log (r * ‖a‖) - Real.log ‖ψ z - conj (ψ z)‖ := by
  have hρ := h.rho_pos
  have hc := h.rho_le
  unfold kernelCov
  simp_rw [xpc_inner_fc (ψ z) _ hρ]
  rw [h.fc_img_eq]
  have hae : ∀ᵐ x ∂circleUnif (ψ z) (r * ‖a‖),
      -Real.log (max (r * ‖a‖) ‖ψ z - x‖) - Real.log (max (r * ‖a‖) ‖ψ z - conj x‖) =
        -Real.log (r * ‖a‖) - Real.log ‖x - conj (ψ z)‖ := by
    filter_upwards [CircleMV.ae_circleUnif (ψ z) (r * ‖a‖)] with x hx
    rw [abs_of_pos hρ] at hx
    have m1 : max (r * ‖a‖) ‖ψ z - x‖ = r * ‖a‖ := by rw [norm_sub_rev, hx, max_self]
    have hxim := (abs_le.1 ((Complex.abs_im_le_norm (x - ψ z)).trans hx.le)).1
    rw [Complex.sub_im] at hxim
    have m2 : max (r * ‖a‖) ‖ψ z - conj x‖ = ‖x - conj (ψ z)‖ := by
      rw [norm_sub_conj_comm (ψ z) x]
      apply max_eq_right
      have := Complex.abs_im_le_norm (x - conj (ψ z))
      rw [Complex.sub_im, Complex.conj_im, abs_of_nonneg (by linarith)] at this
      linarith
    rw [m1, m2]
  have hm : max (r * ‖a‖) ‖ψ z - conj (ψ z)‖ = ‖ψ z - conj (ψ z)‖ := by
    apply max_eq_right
    have := Complex.abs_im_le_norm (ψ z - conj (ψ z))
    rw [Complex.sub_im, Complex.conj_im, abs_of_nonneg (by linarith)] at this
    linarith
  rw [integral_congr_ae hae, integral_sub (integrable_const _)
    (CircleMV.integrable_log_norm_sub_circleUnif _ _ _),
    integral_log_norm_sub_circleUnif _ _ hρ, hm]
  simp

theorem A12_bounds :
    Integrable (fun u => Real.log (max (r * ‖a‖) ‖ψ z - ψ u‖)) (circleUnif z r) ∧
      Real.log (r * ‖a‖) ≤ ∫ u, Real.log (max (r * ‖a‖) ‖ψ z - ψ u‖) ∂circleUnif z r ∧
      ∫ u, Real.log (max (r * ‖a‖) ‖ψ z - ψ u‖) ∂circleUnif z r ≤
        Real.log (r * ‖a‖) + Real.log (1 + η) := by
  have hρ := h.rho_pos
  have h2 : 0 < 1 + η := by linarith [h.eta_nonneg]
  refine xpc_integral_bounds (Measurable.aestronglyMeasurable
    (Real.measurable_log.comp (measurable_const.max (measurable_const.sub h.meas).norm))) ?_
  filter_upwards [h.ae_sphere] with u hu
  have hb := (h.dist_bounds (mem_closedBall_self h.r_pos.le) hu.1).2
  rw [norm_sub_rev z u, hu.2] at hb
  constructor
  · exact Real.log_le_log hρ (le_max_left _ _)
  · rw [← Real.log_mul hρ.ne' h2.ne']
    refine Real.log_le_log (lt_max_of_lt_left hρ) (max_le ?_ ?_)
    · nlinarith [h.eta_nonneg]
    · show ‖ψ z - ψ u‖ ≤ r * ‖a‖ * (1 + η)
      linarith

theorem kc12 :
    kernelCov neumannH ((foldedCircle z r).map ψ) (foldedCircle (ψ z) (r * ‖a‖)) =
      -(∫ u, Real.log (max (r * ‖a‖) ‖ψ z - ψ u‖) ∂circleUnif z r) -
        Real.log ‖ψ z - conj (ψ z)‖ := by
  have hρ := h.rho_pos
  unfold kernelCov
  simp_rw [xpc_inner_fc (ψ z) _ hρ]
  rw [h.fc_eq, integral_map h.meas.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))]
  have hae : ∀ᵐ u ∂circleUnif z r,
      -Real.log (max (r * ‖a‖) ‖ψ z - ψ u‖) - Real.log (max (r * ‖a‖) ‖ψ z - conj (ψ u)‖) =
        -Real.log (max (r * ‖a‖) ‖ψ z - ψ u‖) - Real.log ‖ψ u - conj (ψ z)‖ := by
    filter_upwards [h.ae_sphere] with u hu
    have hpos := h.im_pos u hu.1
    have hc := h.rho_le
    rw [norm_sub_conj_comm (ψ z) (ψ u)]
    congr 2
    apply max_eq_right
    have := Complex.abs_im_le_norm (ψ u - conj (ψ z))
    rw [Complex.sub_im, Complex.conj_im, abs_of_nonneg (by linarith)] at this
    linarith
  rw [integral_congr_ae hae, integral_sub (f := fun u => -Real.log (max (r * ‖a‖) ‖ψ z - ψ u‖))
    h.A12_bounds.1.neg
    (h.integrable_log_reflect (p := ψ z) (h.im_pos z (mem_closedBall_self h.r_pos.le)).le),
    integral_neg, h.integral_log_reflect (h.im_pos z (mem_closedBall_self h.r_pos.le)).le]

/-! ### The pushed-circle self term -/

theorem integrable_log_push {u : ℂ} (hu : u ∈ closedBall z r) :
    Integrable (fun w => Real.log ‖ψ u - ψ w‖) (circleUnif z r) := by
  refine ((CircleMV.integrable_log_norm_sub_circleUnif z u r).abs.add
    (integrable_const (|Real.log ((1 - η) * ‖a‖)| + |Real.log ((1 + η) * ‖a‖)|))).mono'
    (Real.measurable_log.comp (measurable_const.sub h.meas).norm).aestronglyMeasurable ?_
  filter_upwards [h.ae_sphere, CoordChange.ae_ne_circleUnif z h.r_pos.ne' u] with w hw hne
  obtain ⟨b1, b2⟩ := h.log_bounds hu hw.1 (Ne.symm hne)
  rw [norm_sub_rev u w] at b1 b2
  rw [Real.norm_eq_abs, Pi.add_apply, abs_le]
  constructor
  · linarith [neg_abs_le (Real.log ‖w - u‖), neg_abs_le (Real.log ((1 - η) * ‖a‖)),
      abs_nonneg (Real.log ((1 + η) * ‖a‖))]
  · linarith [le_abs_self (Real.log ‖w - u‖), le_abs_self (Real.log ((1 + η) * ‖a‖)),
      abs_nonneg (Real.log ((1 - η) * ‖a‖))]

theorem A_bounds {u : ℂ} (hu : u ∈ closedBall z r) (hur : ‖u - z‖ = r) :
    Real.log r + Real.log ((1 - η) * ‖a‖) ≤ ∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r ∧
      ∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r ≤ Real.log r + Real.log ((1 + η) * ‖a‖) := by
  have hI := CircleMV.integrable_log_norm_sub_circleUnif z u r
  have hmean : ∫ w, Real.log ‖w - u‖ ∂circleUnif z r = Real.log r := by
    rw [integral_log_norm_sub_circleUnif z u h.r_pos, norm_sub_rev, hur, max_self]
  have hae : ∀ᵐ w ∂circleUnif z r,
      Real.log ‖w - u‖ + Real.log ((1 - η) * ‖a‖) ≤ Real.log ‖ψ u - ψ w‖ ∧
        Real.log ‖ψ u - ψ w‖ ≤ Real.log ‖w - u‖ + Real.log ((1 + η) * ‖a‖) := by
    filter_upwards [h.ae_sphere, CoordChange.ae_ne_circleUnif z h.r_pos.ne' u] with w hw hne
    obtain ⟨b1, b2⟩ := h.log_bounds hu hw.1 (Ne.symm hne)
    rw [norm_sub_rev u w] at b1 b2
    exact ⟨b1, b2⟩
  constructor
  · have := integral_mono_ae (hI.add (integrable_const _)) (h.integrable_log_push hu)
      (hae.mono fun w hw => hw.1)
    simp only [Pi.add_apply] at this
    rw [integral_add hI (integrable_const _), hmean] at this
    simpa using this
  · have := integral_mono_ae (h.integrable_log_push hu) (hI.add (integrable_const _))
      (hae.mono fun w hw => hw.2)
    simp only [Pi.add_apply] at this
    rw [integral_add hI (integrable_const _), hmean] at this
    simpa using this

theorem measurable_A :
    StronglyMeasurable (fun u => ∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r) := by
  have hm : Measurable (fun p : ℂ × ℂ => Real.log ‖ψ p.1 - ψ p.2‖) :=
    Real.measurable_log.comp ((h.meas.comp measurable_fst).sub (h.meas.comp measurable_snd)).norm
  exact hm.stronglyMeasurable.integral_prod_right'

theorem A_int_bounds :
    Integrable (fun u => ∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r) (circleUnif z r) ∧
      Real.log r + Real.log ((1 - η) * ‖a‖) ≤
        ∫ u, (∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r) ∂circleUnif z r ∧
      ∫ u, (∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r) ∂circleUnif z r ≤
        Real.log r + Real.log ((1 + η) * ‖a‖) := by
  refine xpc_integral_bounds h.measurable_A.aestronglyMeasurable ?_
  filter_upwards [h.ae_sphere] with u hu
  exact h.A_bounds hu.1 hu.2

theorem kc11 :
    kernelCov neumannH ((foldedCircle z r).map ψ) ((foldedCircle z r).map ψ) =
      -(∫ u, (∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r) ∂circleUnif z r) -
        Real.log ‖ψ z - conj (ψ z)‖ := by
  have hz0 : 0 ≤ (ψ z).im := (h.im_pos z (mem_closedBall_self h.r_pos.le)).le
  unfold kernelCov
  rw [h.fc_eq]
  have hF : StronglyMeasurable fun x => ∫ y, neumannH x y ∂(circleUnif z r).map ψ :=
    measurable_neumannH.stronglyMeasurable.integral_prod_right'
  rw [integral_map h.meas.aemeasurable hF.aestronglyMeasurable]
  have hae : ∀ᵐ u ∂circleUnif z r, ∫ y, neumannH (ψ u) y ∂(circleUnif z r).map ψ =
      -(∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r) - Real.log ‖ψ u - conj (ψ z)‖ := by
    filter_upwards [h.ae_sphere] with u hu
    have hu0 : 0 ≤ (ψ u).im := (h.im_pos u hu.1).le
    have hmy : Measurable fun y => neumannH (ψ u) y :=
      measurable_neumannH.comp (measurable_const.prodMk measurable_id)
    rw [integral_map h.meas.aemeasurable hmy.aestronglyMeasurable]
    unfold neumannH
    simp_rw [norm_sub_conj_comm (ψ u)]
    rw [integral_sub (f := fun w => -Real.log ‖ψ u - ψ w‖)
        (h.integrable_log_push hu.1).neg
        (h.integrable_log_reflect hu0),
      integral_neg, h.integral_log_reflect hu0, norm_sub_conj_comm (ψ z) (ψ u)]
  rw [integral_congr_ae hae, integral_sub (f := fun u => -∫ w, Real.log ‖ψ u - ψ w‖ ∂circleUnif z r)
      h.A_int_bounds.1.neg
      (h.integrable_log_reflect hz0),
    integral_neg, h.integral_log_reflect hz0]

/-! ### The energy bound -/

theorem isAdmissibleH_push : IsAdmissibleH ((foldedCircle z r).map ψ) := by
  have h1 : 0 < 1 - η := by linarith [h.eta_le]
  refine isAdmissibleH_map (isAdmissibleH_foldedCircle h.z_mem_Hbar h.r_pos)
    (isCompact_closedBall z r) ?_ h.meas h.analytic.continuousOn ?_
    (mul_pos h1 h.norm_a_pos) ?_
  · rw [h.fc_eq]
    exact ae_iff.1 (CoordReg.ae_mem_closedBall_circleUnif z h.r_pos.le)
  · rintro _ ⟨u, hu, rfl⟩
    exact (h.im_pos u hu).le
  · intro x hx y hy
    have := (h.dist_bounds hx hy).1
    linarith [mul_assoc (1 - η) ‖a‖ ‖x - y‖]

theorem xpc_log_bounds : Real.log (1 + η) ≤ η ∧ 0 ≤ Real.log (1 + η) ∧
    -(2 * η) ≤ Real.log (1 - η) := by
  have h0 := h.eta_nonneg
  have h12 := h.eta_le
  refine ⟨by linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + η by linarith)],
    Real.log_nonneg (by linarith), ?_⟩
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - η by linarith)
  have hinv : (1 - η)⁻¹ ≤ 1 + 2 * η := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  linarith

end PushCircHyp

/-- **Step (a) of X-A-pc: the Neumann energy of `ψ_* fc(z, r) − fc(ψ z, r‖a‖)` is at most `4η`**
when `ψ` is `η`-close to an affine map of slope `a` on `B̄(z, r)` (`PushCircHyp`). -/
theorem abs_kernelCov2_push_circle_le (h : PushCircHyp ψ z a r η) :
    |kernelCov2 neumannH ((foldedCircle z r).map ψ, foldedCircle (ψ z) (r * ‖a‖))
        ((foldedCircle z r).map ψ, foldedCircle (ψ z) (r * ‖a‖))| ≤ 4 * η := by
  have hμ₂ : IsAdmissibleH (foldedCircle (ψ z) (r * ‖a‖)) :=
    isAdmissibleH_foldedCircle (show 0 ≤ (ψ z).im from
      (h.im_pos z (mem_closedBall_self h.r_pos.le)).le) h.rho_pos
  simp only [kernelCov2]
  rw [CoordChange.kernelCov_comm_of_admissible hμ₂ h.isAdmissibleH_push, h.kc11, h.kc12, h.kc22]
  obtain ⟨-, hA1, hA2⟩ := h.A_int_bounds
  obtain ⟨-, hB1, hB2⟩ := h.A12_bounds
  obtain ⟨l1, l2, l3⟩ := h.xpc_log_bounds
  have ha := h.norm_a_pos
  have e1 : Real.log (r * ‖a‖) = Real.log r + Real.log ‖a‖ :=
    Real.log_mul h.r_pos.ne' ha.ne'
  have e2 : Real.log ((1 - η) * ‖a‖) = Real.log (1 - η) + Real.log ‖a‖ :=
    Real.log_mul (by linarith [h.eta_le]) ha.ne'
  have e3 : Real.log ((1 + η) * ‖a‖) = Real.log (1 + η) + Real.log ‖a‖ :=
    Real.log_mul (by linarith [h.eta_nonneg]) ha.ne'
  rw [e1] at hB1 hB2 ⊢
  rw [e2] at hA1
  rw [e3] at hA2
  rw [abs_le]
  constructor <;> linarith [h.eta_nonneg]

end XAreaPC
end QuantumZipper.E6

import QuantumZipper.Proofs.Zipper.UnzipFullSplit
import QuantumZipper.Proofs.Loewner.TwoPointEnergy
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# TREG: test-function regularity of the reverse coupling field (`AUDIT3.md` §4.1)

For a folded circle `σ = fc(w, r)`, `r > 0`, we build explicit smooth test functions
`moll w r ε ∈ TestFun H` (`mollTF`), of mass `1`, with `moll w r ε dz → σ`, and prove that for
`f = revMap W T` (`W` continuous, `T ≥ 0`) and a free-boundary GFF `X` (modulo constants),
`pairRaw (couplingFieldRev κ W T X) (moll w r εₙ) → couplingFieldRev κ W T X σ` in probability
whenever `εₙ → 0` (`tendstoInMeasure_pairRaw_moll`). The same holds for `ofFun h0rev + X`
(`tendstoInMeasure_pairRaw_moll_h0rev`) and for a random driver independent of `X`
(`tendstoInMeasure_pairRaw_moll_random`).

**Construction.** `moll w r ε` is the density of the law of `t + ε (i + u)`, `t ~ σ`,
`u ~ β` independent, where `β` is a fixed smooth bump law supported in `closedBall 0 (1/2)`
(`tdens_moll`). Lifting by `εi` keeps the support in `{Im ≥ ε/2}` (compact in `ℍ`), and the
density is a convolution of the lifted circle with a smooth bump, hence smooth
(`HasCompactSupport.contDiff_convolution_right`, mathlib).

**Energy.** Coupling `t ↦ t + ε(i + u)` with `t` itself, the two-point upper bound
(`TwoPoint.norm_revMap_sub_mul_le_upper`) moves image points by `≤ (3/2) ε M / τ` off the strip
`{Im t < τ}` of `σ`-mass `≤ 18 √(τ/r)` (`TwoPoint.foldedCircle_strip_le`), and the Neumann
potentials of Frostman measures are Hölder (`TwoPoint.abs_neuPot_sub_le`). With `τ = √ε` the
Neumann energy of `f_*(moll dz) − f_*σ` is `O(ε^{1/12})` (`abs_energy_moll_le`). This is the
coupling argument of the energy modulus (E), `TwoPoint.abs_kernelCov2_revMap_foldedCircle_le`
(AUDIT3 §1.3), with the second circle replaced by the mollified one; the Frostman bound (F) for
the mollified measure (`isFrostman_moll`) is `TwoPoint.isFrostman_revMap_foldedCircle` for
translated circles, integrated over the translation. Then Chebyshev for the Gaussian difference.

No published source treats this regularization of the pulled-back field; the argument is our
own and uses only the two-point bounds of AUDIT3 §1.3 and the covariance of the GFF.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal Real

namespace QuantumZipper
namespace TReg

open TwoPoint

/-! ## 1. The bump law -/

/-- A fixed smooth bump on `ℂ`, supported in `ball 0 (1/2)`. -/
def bump0 : ContDiffBump (0 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The normalized bump: a smooth probability density supported in `ball 0 (1/2)`. -/
def psi1 : ℂ → ℝ := bump0.normed volume

theorem psi1_nonneg (u : ℂ) : 0 ≤ psi1 u := bump0.nonneg_normed u

theorem psi1_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi1 := bump0.contDiff_normed

theorem psi1_continuous : Continuous psi1 := psi1_contDiff.continuous

theorem psi1_hasCompactSupport : HasCompactSupport psi1 := bump0.hasCompactSupport_normed

theorem psi1_integral : ∫ u, psi1 u = 1 := bump0.integral_normed

theorem psi1_eq_zero {u : ℂ} (hu : 1 / 2 ≤ ‖u‖) : psi1 u = 0 := by
  have : u ∉ Function.support psi1 := by
    rw [psi1, bump0.support_normed_eq, Metric.mem_ball, dist_zero_right, not_lt]
    exact hu
  simpa using this

theorem psi1_integrable : Integrable psi1 :=
  psi1_continuous.integrable_of_hasCompactSupport psi1_hasCompactSupport

theorem measurable_psi1 : Measurable psi1 := psi1_continuous.measurable

/-- The bump law `β`. -/
def beta : Measure ℂ := volume.withDensity fun u => ENNReal.ofReal (psi1 u)

theorem measurable_ofReal_psi1 : Measurable fun u => ENNReal.ofReal (psi1 u) :=
  ENNReal.measurable_ofReal.comp measurable_psi1

instance : IsProbabilityMeasure beta := ⟨by
  rw [beta, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal psi1_integrable (ae_of_all _ psi1_nonneg),
    psi1_integral, ENNReal.ofReal_one]⟩

theorem beta_ae_norm_le : ∀ᵐ u ∂beta, ‖u‖ ≤ 1 / 2 := by
  rw [beta, ae_withDensity_iff measurable_ofReal_psi1]
  refine ae_of_all _ fun u hu => ?_
  by_contra h
  exact hu (by rw [psi1_eq_zero (not_le.1 h).le, ENNReal.ofReal_zero])

/-! ## 2. The scaled bump and the mollifier -/

/-- `ψ_ε(x) = ε⁻² ψ₁(ε⁻¹ x)`. -/
def psiE (ε : ℝ) (x : ℂ) : ℝ := (ε ^ 2)⁻¹ * psi1 (ε⁻¹ • x)

theorem psiE_nonneg {ε : ℝ} (x : ℂ) : 0 ≤ psiE ε x :=
  mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (psi1_nonneg _)

theorem psiE_contDiff (ε : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiE ε) :=
  contDiff_const.mul (psi1_contDiff.comp (contDiff_id.const_smul ε⁻¹))

theorem psiE_continuous (ε : ℝ) : Continuous (psiE ε) := (psiE_contDiff ε).continuous

theorem psiE_hasCompactSupport {ε : ℝ} (hε : ε ≠ 0) : HasCompactSupport (psiE ε) :=
  (psi1_hasCompactSupport.comp_smul (inv_ne_zero hε)).mul_left

theorem psiE_eq_zero {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : ε / 2 ≤ ‖x‖) : psiE ε x = 0 := by
  rw [psiE, psi1_eq_zero, mul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε), le_inv_mul_iff₀ hε]
  linarith

/-- Change of variables `x = ε u`. -/
theorem lintegral_psiE {ε : ℝ} (hε : 0 < ε) {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x * ENNReal.ofReal (psiE ε x) =
      ∫⁻ u, G ((ε : ℂ) * u) * ENNReal.ofReal (psi1 u) := by
  set h : ℂ → ℝ≥0∞ := fun x => G x * ENNReal.ofReal (psi1 (ε⁻¹ • x)) with hh
  have hhm : Measurable h :=
    hG.mul (ENNReal.measurable_ofReal.comp (measurable_psi1.comp (measurable_const_smul _)))
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure ℂ)) (r := ε) hε.ne'
  have h1 : ∫⁻ u, h (ε • u) = ENNReal.ofReal |(ε ^ Module.finrank ℝ ℂ)⁻¹| * ∫⁻ x, h x := by
    rw [← lintegral_map hhm (measurable_const_smul ε), hmap, lintegral_smul_measure, smul_eq_mul]
  have h2 : ∀ u, h (ε • u) = G ((ε : ℂ) * u) * ENNReal.ofReal (psi1 u) := by
    intro u
    simp only [hh]
    rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul, Complex.real_smul]
  have h3 : ∀ x, G x * ENNReal.ofReal (psiE ε x) = ENNReal.ofReal ((ε ^ 2)⁻¹) * h x := by
    intro x
    simp only [hh, psiE]
    rw [ENNReal.ofReal_mul (by positivity)]
    ring
  rw [lintegral_congr h3, lintegral_const_mul _ hhm, ← lintegral_congr h2, h1,
    Complex.finrank_real_complex, abs_of_pos (by positivity)]

/-- The folded circle lifted by `εi`. -/
def liftFC (w : ℂ) (r ε : ℝ) : Measure ℂ := (foldedCircle w r).map (· + (ε : ℂ) * I)

instance (w : ℂ) (r ε : ℝ) : IsProbabilityMeasure (liftFC w r ε) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_add_const _).aemeasurable).2 inferInstance

/-- The mollifier: the density of `t + ε(i + u)`, `t ~ fc(w,r)`, `u ~ β`. -/
def moll (w : ℂ) (r ε : ℝ) (x : ℂ) : ℝ := ∫ t, psiE ε (x - t) ∂liftFC w r ε

theorem moll_nonneg (w : ℂ) (r ε : ℝ) (x : ℂ) : 0 ≤ moll w r ε x :=
  integral_nonneg fun _ => psiE_nonneg _

theorem moll_eq_convolution (w : ℂ) (r ε : ℝ) :
    moll w r ε = convolution (fun _ : ℂ => (1 : ℝ)) (psiE ε) (ContinuousLinearMap.lsmul ℝ ℝ)
      (liftFC w r ε) := by
  funext x
  simp [moll, convolution]

theorem moll_contDiff (w : ℂ) (r : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (moll w r ε) := by
  rw [moll_eq_convolution]
  exact (psiE_hasCompactSupport hε).contDiff_convolution_right _ (locallyIntegrable_const _)
    (psiE_contDiff ε)

theorem moll_continuous (w : ℂ) (r : ℝ) {ε : ℝ} (hε : ε ≠ 0) : Continuous (moll w r ε) :=
  (moll_contDiff w r hε).continuous

theorem fc_ae_im_pos_norm (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ t ∂foldedCircle w r, 0 < t.im ∧ ‖t‖ ≤ ‖w‖ + r := by
  filter_upwards [foldedCircle_ae_mem_H w hr, foldedCircle_ae_norm_le w hr.le] with t h1 h2
  exact ⟨h1, h2⟩

/-- The support of the mollifier: `moll w r ε x = 0` off `{Im ≥ ε/2} ∩ closedBall 0 (‖w‖+r+2ε)`. -/
theorem moll_eq_zero (w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {x : ℂ}
    (hx : x ∉ {z : ℂ | ε / 2 ≤ z.im} ∩ Metric.closedBall 0 (‖w‖ + r + 2 * ε)) :
    moll w r ε x = 0 := by
  unfold moll liftFC
  have hc : Continuous fun t => psiE ε (x - t) :=
    (psiE_continuous ε).comp (continuous_const.sub continuous_id)
  rw [integral_map (measurable_add_const _).aemeasurable hc.aestronglyMeasurable]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [fc_ae_im_pos_norm w hr] with t ht
  refine psiE_eq_zero hε ?_
  by_contra hlt
  push_neg at hlt
  apply hx
  have hc : ‖(ε : ℂ) * I‖ = ε := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  refine ⟨?_, ?_⟩
  · have him : |(x - (t + ε * I)).im| ≤ ‖x - (t + ε * I)‖ := Complex.abs_im_le_norm _
    simp only [sub_im, add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, sub_zero,
      mul_one, zero_mul, add_zero] at him
    show ε / 2 ≤ x.im
    have := (abs_le.1 (him.trans hlt.le)).1
    linarith [ht.1]
  · rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖x‖ = ‖(x - (t + ε * I)) + t + ε * I‖ := by ring_nf
      _ ≤ ‖x - (t + ε * I)‖ + ‖t‖ + ‖(ε : ℂ) * I‖ := norm_add₃_le
      _ ≤ ‖w‖ + r + 2 * ε := by rw [hc]; linarith [ht.2]

theorem moll_tsupport (w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    tsupport (moll w r ε) ⊆ {z : ℂ | ε / 2 ≤ z.im} ∩ Metric.closedBall 0 (‖w‖ + r + 2 * ε) := by
  refine closure_minimal (fun x hx => ?_)
    ((isClosed_le continuous_const Complex.continuous_im).inter Metric.isClosed_closedBall)
  by_contra h
  exact hx (moll_eq_zero w hr hε h)

theorem moll_hasCompactSupport (w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    HasCompactSupport (moll w r ε) :=
  (isCompact_closedBall 0 _).of_isClosed_subset (isClosed_tsupport _)
    ((moll_tsupport w hr hε).trans inter_subset_right)

theorem moll_tsupport_H (w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    tsupport (moll w r ε) ⊆ H := fun z hz =>
  show 0 < z.im from lt_of_lt_of_le (by linarith) (moll_tsupport w hr hε hz).1

/-- The mollifier as a test function. -/
def mollTF (w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) : TestFun H :=
  ⟨moll w r ε, moll_contDiff w r hε.ne', moll_hasCompactSupport w hr hε, moll_tsupport_H w hr hε⟩

/-! ## 3. The coupling -/

/-- The coupling map `(t, u) ↦ t + ε(i + u)`. -/
def cpl (ε : ℝ) (p : ℂ × ℂ) : ℂ := p.1 + (ε : ℂ) * (I + p.2)

theorem measurable_cpl (ε : ℝ) : Measurable (cpl ε) := by
  unfold cpl; fun_prop

/-- The mollified measure, as the law of the coupling. -/
def mollMeas (w : ℂ) (r ε : ℝ) : Measure ℂ := ((foldedCircle w r).prod beta).map (cpl ε)

instance (w : ℂ) (r ε : ℝ) : IsProbabilityMeasure (mollMeas w r ε) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_cpl ε).aemeasurable).2 inferInstance

theorem integrable_psiE_sub {ε : ℝ} (hε : ε ≠ 0) (μ : Measure ℂ) [IsFiniteMeasure μ] (x : ℂ) :
    Integrable (fun t => psiE ε (x - t)) μ := by
  obtain ⟨C, hC⟩ := (psiE_continuous ε).bounded_above_of_compact_support
    (psiE_hasCompactSupport hε)
  exact Integrable.of_bound ((psiE_continuous ε).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable C (ae_of_all _ fun t => hC _)

/-- **The density of the mollified measure is `moll`.** -/
theorem tdens_moll (w : ℂ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    CharFun.tdens (moll w r ε) = mollMeas w r ε := by
  have hmoll : Measurable fun x => ENNReal.ofReal (moll w r ε x) :=
    ENNReal.measurable_ofReal.comp (moll_continuous w r hε.ne').measurable
  have hpsi : Measurable (psiE ε) := (psiE_continuous ε).measurable
  refine Measure.ext_of_lintegral _ fun G hG => ?_
  rw [CharFun.tdens, lintegral_withDensity_eq_lintegral_mul _ hmoll hG, mollMeas,
    lintegral_map hG (measurable_cpl ε),
    lintegral_prod (fun z => G (cpl ε z)) (hG.comp (measurable_cpl ε)).aemeasurable]
  have hL : ∀ x, ENNReal.ofReal (moll w r ε x) =
      ∫⁻ t, ENNReal.ofReal (psiE ε (x - t)) ∂liftFC w r ε := fun x =>
    ofReal_integral_eq_lintegral_ofReal (integrable_psiE_sub hε.ne' _ x)
      (ae_of_all _ fun t => psiE_nonneg _)
  have hJ : Measurable (Function.uncurry fun (x t : ℂ) => G x * ENNReal.ofReal (psiE ε (x - t))) :=
    (hG.comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp (hpsi.comp (measurable_fst.sub measurable_snd)))
  have hF : Measurable fun p : ℂ × ℂ =>
      G ((ε : ℂ) * p.2 + p.1) * ENNReal.ofReal (psi1 p.2) :=
    (hG.comp ((measurable_const.mul measurable_snd).add measurable_fst)).mul
      (measurable_ofReal_psi1.comp measurable_snd)
  calc ∫⁻ x, ((fun x => ENNReal.ofReal (moll w r ε x)) * G) x
      = ∫⁻ x, (∫⁻ t, G x * ENNReal.ofReal (psiE ε (x - t)) ∂liftFC w r ε) := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, hL, mul_comm]
        exact (lintegral_const_mul (G x) (f := fun t => ENNReal.ofReal (psiE ε (x - t)))
          (ENNReal.measurable_ofReal.comp (hpsi.comp (measurable_const.sub measurable_id)))).symm
    _ = ∫⁻ t, (∫⁻ x, G x * ENNReal.ofReal (psiE ε (x - t))) ∂liftFC w r ε :=
        lintegral_lintegral_swap hJ.aemeasurable
    _ = ∫⁻ t, (∫⁻ u, G ((ε : ℂ) * u + t) * ENNReal.ofReal (psi1 u)) ∂liftFC w r ε := by
        refine lintegral_congr fun t => ?_
        rw [← lintegral_add_right_eq_self _ t]
        simp only [add_sub_cancel_right]
        exact lintegral_psiE hε (G := fun y => G (y + t)) (hG.comp (measurable_add_const t))
    _ = ∫⁻ t, (∫⁻ u, G ((ε : ℂ) * u + (t + ε * I)) * ENNReal.ofReal (psi1 u))
          ∂foldedCircle w r := by
        rw [liftFC, lintegral_map hF.lintegral_prod_right' (measurable_add_const _)]
    _ = ∫⁻ t, (∫⁻ u, G (cpl ε (t, u)) ∂beta) ∂foldedCircle w r := by
        refine lintegral_congr fun t => ?_
        have hGt : Measurable fun u => G (cpl ε (t, u)) :=
          hG.comp ((measurable_cpl ε).comp (measurable_const.prodMk measurable_id))
        rw [beta, lintegral_withDensity_eq_lintegral_mul _ measurable_ofReal_psi1 hGt]
        refine lintegral_congr fun u => ?_
        simp only [Pi.mul_apply, cpl, Function.comp_apply]
        rw [mul_comm]
        congr 2
        ring

theorem tdens_neg_moll (w : ℂ) (r ε : ℝ) : CharFun.tdens (fun z => -moll w r ε z) = 0 := by
  rw [CharFun.tdens]
  have : (fun z => ENNReal.ofReal (-moll w r ε z)) = 0 := by
    funext z
    rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 (moll_nonneg w r ε z))]
    rfl
  rw [this, withDensity_zero]

theorem integral_moll (w : ℂ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) : ∫ z, moll w r ε z = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (moll_nonneg w r ε))
    (moll_continuous w r hε.ne').aestronglyMeasurable]
  have : ∫⁻ z, ENNReal.ofReal (moll w r ε z) = CharFun.tdens (moll w r ε) univ := by
    rw [CharFun.tdens, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [this, tdens_moll w r hε, measure_univ, ENNReal.toReal_one]

/-! ## 4. Frostman bounds -/

variable {W : ℝ → ℝ}

theorem prod_ae (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ p ∂(foldedCircle w r).prod beta, 0 < p.1.im ∧ ‖p.1‖ ≤ ‖w‖ + r ∧ ‖p.2‖ ≤ 1 / 2 := by
  have h1 : ∀ᵐ p ∂(foldedCircle w r).prod beta, 0 < p.1.im ∧ ‖p.1‖ ≤ ‖w‖ + r :=
    (measurePreserving_fst (μ := foldedCircle w r) (ν := beta)).quasiMeasurePreserving.ae
      (fc_ae_im_pos_norm w hr)
  have h2 : ∀ᵐ p ∂(foldedCircle w r).prod beta, ‖p.2‖ ≤ 1 / 2 :=
    (measurePreserving_snd (μ := foldedCircle w r) (ν := beta)).quasiMeasurePreserving.ae
      beta_ae_norm_le
  filter_upwards [h1, h2] with p a b using ⟨a.1, a.2, b⟩

theorem cpl_facts {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {p : ℂ × ℂ} (hp2 : ‖p.2‖ ≤ 1 / 2) :
    p.1.im + ε / 2 ≤ (cpl ε p).im ∧ ‖cpl ε p - p.1‖ ≤ 3 / 2 * ε ∧ ‖cpl ε p‖ ≤ ‖p.1‖ + 2 := by
  have hu : |p.2.im| ≤ 1 / 2 := (Complex.abs_im_le_norm _).trans hp2
  have hn : ‖I + p.2‖ ≤ 3 / 2 := (norm_add_le _ _).trans (by rw [Complex.norm_I]; linarith)
  have hd : cpl ε p - p.1 = (ε : ℂ) * (I + p.2) := by unfold cpl; ring
  have hdn : ‖cpl ε p - p.1‖ ≤ 3 / 2 * ε := by
    rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]; nlinarith
  refine ⟨?_, hdn, ?_⟩
  · have : (cpl ε p).im = p.1.im + ε * (1 + p.2.im) := by
      simp only [cpl, add_im, mul_im, ofReal_re, ofReal_im, I_im, zero_mul, add_zero]
    rw [this]; nlinarith [(abs_le.1 hu).1]
  · calc ‖cpl ε p‖ = ‖p.1 + (cpl ε p - p.1)‖ := by ring_nf
      _ ≤ ‖p.1‖ + ‖cpl ε p - p.1‖ := norm_add_le _ _
      _ ≤ ‖p.1‖ + 2 := by linarith

/-- (F) for a translated folded circle `fc(w,r) + c`, `Im c ≥ 0`: the proof of
`TwoPoint.isFrostman_revMap_foldedCircle`, with the translation carried along. -/
theorem frostman_shift_le (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {w c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c.im) (hwR : ‖w‖ + r + ‖c‖ ≤ R) (p : ℂ) {s : ℝ} (hs : 0 < s) :
    (foldedCircle w r).map (fun x => revMap W T (x + c)) (Metric.closedBall p s) ≤
      ENNReal.ofReal ((18 / Real.sqrt r + 12 * Real.sqrt (R ^ 2 + 4 * T) / r) *
        s ^ (1 / 3 : ℝ)) := by
  have hπ := Real.pi_pos
  have hgm : Measurable fun x => revMap W T (x + c) :=
    (measurable_revMap hW hT).comp (measurable_add_const c)
  set M := Real.sqrt (R ^ 2 + 4 * T) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set t := s ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hs _
  have ht3 : t ^ 3 = s := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  set τ := t ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  set D := 2 * t * M with hD
  have hD0 : 0 ≤ D := by positivity
  set S := {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧
    revMap W T (foldH (circleMap w r θ) + c) ∈ Metric.closedBall p s}
  set Bad := {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap w r θ).im| < τ}
  set Good := {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ τ ≤ |(circleMap w r θ).im| ∧
    revMap W T (foldH (circleMap w r θ) + c) ∈ Metric.closedBall p s}
  have hSsub : S ⊆ Bad ∪ Good := by
    rintro θ ⟨h1, h2⟩
    rcases lt_or_ge |(circleMap w r θ).im| τ with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h1, h, h2⟩
  have hbound : ∀ θ, (foldH (circleMap w r θ) + c).im ≤ R := fun θ =>
    (Complex.im_le_norm _).trans ((norm_add_le _ _).trans (by
      rw [norm_foldH]; linarith [norm_circleMap_le_add w hr.le θ]))
  have himc : ∀ θ, |(circleMap w r θ).im| ≤ (foldH (circleMap w r θ) + c).im := fun θ => by
    rw [add_im, im_foldH]; linarith
  have hGood : volume Good ≤
      ENNReal.ofReal (6 * π * D / r) + ENNReal.ofReal (6 * π * D / r) := by
    rcases Good.eq_empty_or_nonempty with hG | ⟨θ₀, h0, hτ0', hF0⟩
    · rw [hG, measure_empty]; exact zero_le
    set q := foldH (circleMap w r θ₀)
    have hsub : Good ⊆ {θ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap w r θ - q‖ ≤ D} ∪
        {θ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap w r θ - (starRingEnd ℂ) q‖ ≤ D} := by
      rintro θ ⟨h1, hτθ, hFθ⟩
      have hkey := norm_sub_mul_le_of_mem_ball hW hT hτ0
        (hτθ.trans (himc θ)) (hτ0'.trans (himc θ₀)) (hbound θ) (hbound θ₀) hFθ hF0
      rw [add_sub_add_right_eq_sub] at hkey
      have hclose : ‖foldH (circleMap w r θ) - q‖ ≤ D := by
        rw [← ht3] at hkey
        refine le_of_mul_le_mul_right ?_ hτ0
        calc ‖foldH (circleMap w r θ) - q‖ * τ ≤ 2 * t ^ 3 * M := hkey
          _ = D * τ := by rw [hD, hτ]; ring
      rcases foldH_near hclose with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h⟩
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add (volume_arc_le _ _ hr _) (volume_arc_le _ _ hr _)))
  have hBad : volume Bad ≤ ENNReal.ofReal (36 * π * Real.sqrt (τ / r)) :=
    volume_strip_le w hr hτ0
  have ha : (0 : ℝ) ≤ 36 * π * Real.sqrt (τ / r) := by positivity
  have hb : (0 : ℝ) ≤ 6 * π * D / r := by positivity
  have hvol : volume S ≤
      ENNReal.ofReal (36 * π * Real.sqrt (τ / r) + 2 * (6 * π * D / r)) := by
    refine (measure_mono hSsub).trans ((measure_union_le _ _).trans
      ((add_le_add hBad hGood).trans (le_of_eq ?_)))
    rw [← ENNReal.ofReal_add hb hb, ← ENNReal.ofReal_add ha (add_nonneg hb hb)]
    ring_nf
  have hsq : Real.sqrt (τ / r) = t / Real.sqrt r := by
    rw [Real.sqrt_div (by positivity), hτ, Real.sqrt_sq ht0.le]
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have e : (2 * π)⁻¹ * (36 * π * Real.sqrt (τ / r) + 2 * (6 * π * D / r)) =
      (18 / Real.sqrt r + 12 * M / r) * t := by
    rw [hsq, hD]; field_simp; ring
  rw [foldedCircle_map_apply hgm w r Metric.isClosed_closedBall.measurableSet, ← e,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹),
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  exact mul_le_mul' le_rfl hvol

/-- (F) for the pushed-forward mollified measure, uniformly in `ε ∈ (0,1]`. -/
theorem isFrostman_moll (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IsFrostman ((mollMeas w r ε).map (revMap W T)) (1 / 3)
      (18 / Real.sqrt r + 12 * Real.sqrt ((‖w‖ + r + 2) ^ 2 + 4 * T) / r) := by
  intro p s hs
  have hB : MeasurableSet (Metric.closedBall p s) := Metric.isClosed_closedBall.measurableSet
  have hm : Measurable (revMap W T ∘ cpl ε) :=
    (measurable_revMap hW hT).comp (measurable_cpl ε)
  rw [mollMeas, Measure.map_map (measurable_revMap hW hT) (measurable_cpl ε),
    Measure.map_apply hm hB, Measure.prod_apply_symm (hm hB)]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc _ ≤ ∫⁻ _, ENNReal.ofReal ((18 / Real.sqrt r +
          12 * Real.sqrt ((‖w‖ + r + 2) ^ 2 + 4 * T) / r) * s ^ (1 / 3 : ℝ)) ∂beta := by
        refine lintegral_mono_ae ?_
        filter_upwards [beta_ae_norm_le] with u hu
        have hu' : |u.im| ≤ 1 / 2 := (Complex.abs_im_le_norm _).trans hu
        have hc : 0 ≤ ((ε : ℂ) * (I + u)).im := by
          simp only [mul_im, ofReal_re, ofReal_im, add_im, I_im, zero_mul, add_zero]
          nlinarith [(abs_le.1 hu').1]
        have hcn : ‖(ε : ℂ) * (I + u)‖ ≤ 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
          have : ‖I + u‖ ≤ 3 / 2 :=
            (norm_add_le _ _).trans (by rw [Complex.norm_I]; linarith)
          nlinarith [norm_nonneg (I + u)]
        have := frostman_shift_le hW hT hr hc (by linarith : ‖w‖ + r + ‖(ε : ℂ) * (I + u)‖ ≤
          ‖w‖ + r + 2) p hs
        have hmu : Measurable fun x => revMap W T (x + (ε : ℂ) * (I + u)) :=
          (measurable_revMap hW hT).comp (measurable_add_const _)
        rw [Measure.map_apply hmu hB] at this
        exact this
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

theorem ae_push_moll (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) {Bf : ℝ}
    (hBf : ∀ z : ℂ, ‖z‖ ≤ ‖w‖ + r + 2 → ‖revMap W T z‖ ≤ Bf) :
    ∀ᵐ y ∂(mollMeas w r ε).map (revMap W T), ‖y‖ ≤ Bf ∧ 0 < y.im := by
  have hm : Measurable (revMap W T ∘ cpl ε) :=
    (measurable_revMap hW hT).comp (measurable_cpl ε)
  have hS : MeasurableSet {y : ℂ | ‖y‖ ≤ Bf ∧ 0 < y.im} :=
    (isClosed_le continuous_norm continuous_const).measurableSet.inter
      (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  rw [mollMeas, Measure.map_map (measurable_revMap hW hT) (measurable_cpl ε),
    ae_map_iff hm.aemeasurable hS]
  filter_upwards [prod_ae w hr] with p hp
  obtain ⟨h1, -, h3⟩ := cpl_facts hε hε1 hp.2.2
  have hz : 0 < (cpl ε p).im := by linarith [hp.1]
  exact ⟨hBf _ (by linarith [hp.2.1]), im_revMap_pos hW hz hT⟩

theorem ae_push_fc (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) {r : ℝ}
    (hr : 0 < r) {Bf : ℝ} (hBf : ∀ z : ℂ, ‖z‖ ≤ ‖w‖ + r + 2 → ‖revMap W T z‖ ≤ Bf) :
    ∀ᵐ y ∂(foldedCircle w r).map (revMap W T), ‖y‖ ≤ Bf ∧ 0 < y.im := by
  have hS : MeasurableSet {y : ℂ | ‖y‖ ≤ Bf ∧ 0 < y.im} :=
    (isClosed_le continuous_norm continuous_const).measurableSet.inter
      (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  rw [ae_map_iff (measurable_revMap hW hT).aemeasurable hS]
  filter_upwards [fc_ae_im_pos_norm w hr] with t ht
  exact ⟨hBf _ (by linarith [ht.2]), im_revMap_pos hW ht.1 hT⟩

/-! ## 5. The energy estimate -/

/-- The coupling estimate for one potential. -/
theorem abs_D_le (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) {r ε τ : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) {CF Bf : ℝ} (hCF : 0 ≤ CF) (hBf0 : 0 ≤ Bf)
    (hBf : ∀ z : ℂ, ‖z‖ ≤ ‖w‖ + r + 2 → ‖revMap W T z‖ ≤ Bf)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : IsFrostman κ (1 / 3) CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ Bf) (hmκ : κ.real univ = 1) :
    |(∫ y, neuPot κ y ∂(mollMeas w r ε).map (revMap W T)) -
        ∫ y, neuPot κ y ∂(foldedCircle w r).map (revMap W T)| ≤
      holderK CF Bf * (3 / 2 * ε * Real.sqrt ((‖w‖ + r + 2) ^ 2 + 4 * T) / τ) ^
          ((1 / 3 : ℝ) / 2) +
        2 * potMax CF Bf * (18 * Real.sqrt (τ / r)) := by
  set σ := foldedCircle w r with hσ
  set R := ‖w‖ + r + 2 with hR
  set M := Real.sqrt (R ^ 2 + 4 * T) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set Pm := potMax CF Bf
  set KH := holderK CF Bf
  have hPm0 : 0 ≤ Pm := potMax_nonneg hCF hBf0
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hBf0
  have hfm : Measurable (revMap W T) := measurable_revMap hW hT
  have hPb : ∀ x : ℂ, ‖x‖ ≤ Bf → |neuPot κ x| ≤ Pm := fun x hx => by
    have := abs_neuPot_le hFκ (by norm_num) hCF hBf0 hBκ hx
    rwa [hmκ] at this
  have hH : ∀ x x' : ℂ, ‖x‖ ≤ Bf → ‖x'‖ ≤ Bf →
      |neuPot κ x - neuPot κ x'| ≤ KH * ‖x - x'‖ ^ ((1 / 3 : ℝ) / 2) := fun x x' hx hx' => by
    have := abs_neuPot_sub_le hFκ (by norm_num) (by norm_num) hCF hBf0 hBκ hx hx'
    rwa [hmκ] at this
  set A : ℂ × ℂ → ℝ := fun p => neuPot κ (revMap W T (cpl ε p)) with hA
  set B : ℂ × ℂ → ℝ := fun p => neuPot κ (revMap W T p.1) with hB
  have hAm : Measurable A := (measurable_neuPot κ).comp (hfm.comp (measurable_cpl ε))
  have hBm : Measurable B := (measurable_neuPot κ).comp (hfm.comp measurable_fst)
  have e1 : ∫ y, neuPot κ y ∂(mollMeas w r ε).map (revMap W T) = ∫ p, A p ∂σ.prod beta := by
    rw [mollMeas, Measure.map_map hfm (measurable_cpl ε),
      integral_map (hfm.comp (measurable_cpl ε)).aemeasurable
        (measurable_neuPot κ).aestronglyMeasurable]
    rfl
  have e2 : ∫ y, neuPot κ y ∂σ.map (revMap W T) = ∫ p, B p ∂σ.prod beta := by
    rw [integral_map hfm.aemeasurable (measurable_neuPot κ).aestronglyMeasurable]
    conv_lhs => rw [← (measurePreserving_fst (μ := σ) (ν := beta)).map_eq]
    have hmm : Measurable fun x => neuPot κ (revMap W T x) := (measurable_neuPot κ).comp hfm
    rw [integral_map measurable_fst.aemeasurable hmm.aestronglyMeasurable]
    try rfl
  set D0 := KH * (3 / 2 * ε * M / τ) ^ ((1 / 3 : ℝ) / 2) with hD0
  have hD00 : 0 ≤ D0 := by positivity
  set Bad : Set (ℂ × ℂ) := {p | |p.1.im| < τ} with hBad
  have hBadm : MeasurableSet Bad :=
    (isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp continuous_fst))
      continuous_const).measurableSet
  have hpt : ∀ᵐ p ∂σ.prod beta, |A p - B p| ≤ D0 + Bad.indicator (fun _ => 2 * Pm) p := by
    filter_upwards [prod_ae w hr] with p hp
    obtain ⟨c1, c2, c3⟩ := cpl_facts hε hε1 hp.2.2
    have hzR : ‖cpl ε p‖ ≤ R := by rw [hR]; linarith [hp.2.1]
    have hp1R : ‖p.1‖ ≤ R := by rw [hR]; linarith [hp.2.1]
    have hfa := hBf _ hzR
    have hfb := hBf _ hp1R
    by_cases hθ : p ∈ Bad
    · rw [Set.indicator_of_mem hθ]
      have a1 := abs_le.1 (hPb _ hfa)
      have a2 := abs_le.1 (hPb _ hfb)
      rw [abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem hθ, add_zero]
      simp only [hBad, mem_setOf_eq, not_lt] at hθ
      rw [abs_of_pos hp.1] at hθ
      have hu : τ ≤ (cpl ε p).im := by linarith
      have huR : (cpl ε p).im ≤ R := (Complex.im_le_norm _).trans hzR
      have hvR : p.1.im ≤ R := (Complex.im_le_norm _).trans hp1R
      have hkey := norm_revMap_sub_mul_le_upper hW hT hτ hu hθ huR hvR
      have hdisp : ‖revMap W T (cpl ε p) - revMap W T p.1‖ ≤ 3 / 2 * ε * M / τ := by
        rw [le_div_iff₀ hτ]
        calc _ ≤ ‖cpl ε p - p.1‖ * M := hkey
          _ ≤ 3 / 2 * ε * M := mul_le_mul_of_nonneg_right c2 hM0
      exact (hH _ _ hfa hfb).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hdisp (by norm_num)) hKH0)
  have hAi : Integrable A (σ.prod beta) := Integrable.of_bound hAm.aestronglyMeasurable Pm (by
    filter_upwards [prod_ae w hr] with p hp
    obtain ⟨-, -, c3⟩ := cpl_facts hε hε1 hp.2.2
    rw [Real.norm_eq_abs]; exact hPb _ (hBf _ (by rw [hR] at *; linarith [hp.2.1])))
  have hBi : Integrable B (σ.prod beta) := Integrable.of_bound hBm.aestronglyMeasurable Pm (by
    filter_upwards [prod_ae w hr] with p hp
    rw [Real.norm_eq_abs]; exact hPb _ (hBf _ (by linarith [hp.2.1])))
  have hrhs : Integrable (fun p => D0 + Bad.indicator (fun _ => 2 * Pm) p) (σ.prod beta) :=
    (integrable_const D0).add ((integrable_const (2 * Pm)).indicator hBadm)
  have hBadv : (σ.prod beta).real Bad ≤ 18 * Real.sqrt (τ / r) := by
    have : Bad = {x : ℂ | |x.im| < τ} ×ˢ (univ : Set ℂ) := by ext p; simp [hBad]
    rw [measureReal_def, this, Measure.prod_prod, measure_univ, mul_one]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (foldedCircle_strip_le w hr hτ)
  rw [e1, e2, ← integral_sub hAi hBi]
  calc |∫ p, (A p - B p) ∂σ.prod beta| ≤ ∫ p, |A p - B p| ∂σ.prod beta :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p, (D0 + Bad.indicator (fun _ => 2 * Pm) p) ∂σ.prod beta :=
        integral_mono_ae (hAi.sub hBi).abs hrhs hpt
    _ = D0 + (σ.prod beta).real Bad * (2 * Pm) := by
        rw [integral_add (integrable_const D0) ((integrable_const (2 * Pm)).indicator hBadm),
          integral_const, integral_indicator_const _ hBadm, probReal_univ, one_smul,
          smul_eq_mul]
    _ ≤ D0 + 18 * Real.sqrt (τ / r) * (2 * Pm) := by
        have := mul_le_mul_of_nonneg_right hBadv (by positivity : (0 : ℝ) ≤ 2 * Pm)
        linarith
    _ = _ := by ring

/-- **Energy estimate.** The Neumann energy of `f_*(moll dz) − f_* fc(w,r)` is `O(ε^{1/12})`. -/
theorem abs_energy_moll_le (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ∃ Cst : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |kernelCov2 neumannH ((mollMeas w r ε).map (revMap W T), (foldedCircle w r).map (revMap W T))
        ((mollMeas w r ε).map (revMap W T), (foldedCircle w r).map (revMap W T))| ≤
        Cst * ε ^ (1 / 12 : ℝ) := by
  set R := ‖w‖ + r + 2 with hR
  obtain ⟨Bf, hBf0, hBf⟩ := exists_norm_revMap_le hW hT R
  set M := Real.sqrt (R ^ 2 + 4 * T) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set CF := 18 / Real.sqrt r + 12 * M / r with hCFdef
  have hCF : 0 ≤ CF := by positivity
  set Pm := potMax CF Bf
  set KH := holderK CF Bf
  have hPm0 : 0 ≤ Pm := potMax_nonneg hCF hBf0
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hBf0
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  refine ⟨2 * KH * (3 / 2 * M) ^ ((1 / 3 : ℝ) / 2) + 72 * Pm / Real.sqrt r,
    fun ε hε hε1 => ?_⟩
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (mollMeas w r ε).map (revMap W T) := ⟨_, rfl⟩
  obtain ⟨ν', hν'⟩ : ∃ ν', ν' = (foldedCircle w r).map (revMap W T) := ⟨_, rfl⟩
  rw [← hν, ← hν']
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have : IsFiniteMeasure ν' := by rw [hν']; infer_instance
  have hFν : IsFrostman ν (1 / 3) CF := hν ▸ isFrostman_moll hW hT w hr hε hε1
  have hFν' : IsFrostman ν' (1 / 3) CF :=
    hν' ▸ isFrostman_revMap_foldedCircle hW hT hr le_rfl (by rw [hR]; linarith)
  have hBν : ∀ᵐ y ∂ν, ‖y‖ ≤ Bf := hν ▸ (ae_push_moll hW hT w hr hε hε1 hBf).mono fun y h => h.1
  have hBν' : ∀ᵐ y ∂ν', ‖y‖ ≤ Bf := hν' ▸ (ae_push_fc hW hT w hr hBf).mono fun y h => h.1
  have hmν : ν.real univ = 1 := by
    rw [hν, measureReal_def, Measure.map_apply (measurable_revMap hW hT) MeasurableSet.univ,
      preimage_univ, measure_univ, ENNReal.toReal_one]
  have hmν' : ν'.real univ = 1 := hν' ▸ pfc_real_univ hW hT w r
  set τ := Real.sqrt ε with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 hε
  have h1 := abs_D_le hW hT w hr hε hε1 hτ hCF hBf0 hBf ν hFν hBν hmν
  have h2 := abs_D_le hW hT w hr hε hε1 hτ hCF hBf0 hBf ν' hFν' hBν' hmν'
  rw [← hν, ← hν'] at h1 h2
  have hexp : kernelCov2 neumannH (ν, ν') (ν, ν') =
      ((∫ y, neuPot ν y ∂ν) - ∫ y, neuPot ν y ∂ν') -
        ((∫ y, neuPot ν' y ∂ν) - ∫ y, neuPot ν' y ∂ν') := by
    show kernelCov neumannH ν ν - kernelCov neumannH ν ν' - kernelCov neumannH ν' ν +
      kernelCov neumannH ν' ν' = _
    show (∫ x, neuPot ν x ∂ν) - (∫ x, neuPot ν' x ∂ν) - (∫ x, neuPot ν x ∂ν') +
      (∫ x, neuPot ν' x ∂ν') = _
    ring
  have hdiv : 3 / 2 * ε * M / τ = Real.sqrt ε * (3 / 2 * M) := by
    rw [show 3 / 2 * ε * M / τ = ε / τ * (3 / 2 * M) by ring, hτdef, Real.div_sqrt]
  have hpow1 : (3 / 2 * ε * M / τ) ^ ((1 / 3 : ℝ) / 2) =
      (3 / 2 * M) ^ ((1 / 3 : ℝ) / 2) * ε ^ (1 / 12 : ℝ) := by
    rw [hdiv, Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hε.le, show (1 / 2 : ℝ) * ((1 / 3 : ℝ) / 2) = 1 / 12 by norm_num]
    ring
  have hpow2 : Real.sqrt (τ / r) ≤ ε ^ (1 / 12 : ℝ) / Real.sqrt r := by
    rw [Real.sqrt_div (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hε.le]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num)
  rw [hexp]
  rw [hpow1] at h1 h2
  have hsub := (abs_sub _ _).trans (add_le_add h1 h2)
  have h3 := mul_le_mul_of_nonneg_left hpow2 (by positivity : (0 : ℝ) ≤ 2 * Pm * 18)
  have he : 0 ≤ ε ^ (1 / 12 : ℝ) := by positivity
  calc _ ≤ _ := hsub
    _ ≤ 2 * (KH * ((3 / 2 * M) ^ ((1 / 3 : ℝ) / 2) * ε ^ (1 / 12 : ℝ))) +
          2 * (2 * Pm * 18 * (ε ^ (1 / 12 : ℝ) / Real.sqrt r)) := by nlinarith [h3]
    _ = _ := by field_simp; ring

/-! ## 6. Convergence of the deterministic part -/

theorem measurable_hTrev (κ : ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    Measurable (hTrev κ W T) :=
  ((UnzipInvariance.measurable_h0rev κ).comp (measurable_revMap hW hT)).add
    (measurable_const.mul (Real.measurable_log.comp (measurable_deriv _).norm))

theorem abs_hTrev_le (κ : ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {R Bf : ℝ}
    (hBf : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap W T z‖ ≤ Bf) {z : ℂ} {a : ℝ} (ha : 0 < a)
    (haz : a ≤ z.im) (hzR : ‖z‖ ≤ R) :
    |hTrev κ W T z| ≤ |2 / Real.sqrt κ| * (|Real.log a| + |Real.log Bf|) +
      |Qc (Real.sqrt κ)| * (|Real.log (Real.sqrt (R ^ 2 + 4 * T))| + |Real.log a| +
        |Real.log R|) := by
  have hz : z ∈ H := show 0 < z.im by linarith
  have hfz := im_le_im_revMap W hW z hz hT
  have hf1 : a ≤ ‖revMap W T z‖ := haz.trans (hfz.trans (Complex.im_le_norm _))
  have hl1 := abs_log_le_of_mem ha hf1 (hBf z hzR)
  have hzR' : z.im ≤ R := (Complex.im_le_norm _).trans hzR
  have hl2 := abs_log_norm_deriv_revMap_le hW hT hz hzR'
  have hl3 := abs_log_le_of_mem ha haz hzR'
  rw [hTrev, h0rev]
  calc |2 / Real.sqrt κ * Real.log ‖revMap W T z‖ +
        Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W T) z‖|
      ≤ |2 / Real.sqrt κ| * |Real.log ‖revMap W T z‖| +
          |Qc (Real.sqrt κ)| * |Real.log ‖deriv (revMap W T) z‖| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hl1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))

theorem integral_fc_eq_prod {g : ℂ → ℝ} (hg : Measurable g) (w : ℂ) (r : ℝ) :
    ∫ z, g z ∂foldedCircle w r = ∫ p, g p.1 ∂(foldedCircle w r).prod beta := by
  conv_lhs => rw [← (measurePreserving_fst (μ := foldedCircle w r) (ν := beta)).map_eq]
  rw [integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]

theorem integral_moll_eq_prod {g : ℂ → ℝ} (hg : Measurable g) (w : ℂ) (r ε : ℝ) :
    ∫ z, g z ∂mollMeas w r ε = ∫ p, g (cpl ε p) ∂(foldedCircle w r).prod beta := by
  rw [mollMeas, integral_map (measurable_cpl ε).aemeasurable hg.aestronglyMeasurable]

/-- The deterministic part converges: `∫ h_T d(moll dz) → ∫ h_T dσ`. -/
theorem tendsto_integral_hTrev_moll (κ : ℝ) (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ)
    {r : ℝ} (hr : 0 < r) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hεt : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, hTrev κ W T z ∂mollMeas w r (ε n)) atTop
      (𝓝 (∫ z, hTrev κ W T z ∂foldedCircle w r)) := by
  set σ := foldedCircle w r with hσ
  set R := ‖w‖ + r + 2 with hR
  obtain ⟨Bf, hBf0, hBf⟩ := exists_norm_revMap_le hW hT R
  have hhm := measurable_hTrev κ hW hT
  simp_rw [integral_moll_eq_prod hhm]
  rw [integral_fc_eq_prod hhm]
  set K1 := |2 / Real.sqrt κ| * |Real.log Bf| + |Qc (Real.sqrt κ)| *
    (|Real.log (Real.sqrt (R ^ 2 + 4 * T))| + |Real.log R|) with hK1
  set K2 := |2 / Real.sqrt κ| + |Qc (Real.sqrt κ)| with hK2
  have hi : Integrable (fun x : ℂ => Real.log x.im) σ := integrable_log_im_foldedCircle w hr
  have hi2 : Integrable (fun p : ℂ × ℂ => Real.log p.1.im) (σ.prod beta) := by
    have hm : Measurable fun x : ℂ => Real.log x.im := Real.measurable_log.comp Complex.measurable_im
    have := (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).1
      (by rwa [(measurePreserving_fst (μ := σ) (ν := beta)).map_eq])
    exact this
  refine tendsto_integral_of_dominated_convergence (fun p => K1 + K2 * |Real.log p.1.im|)
    (fun n => (hhm.comp (measurable_cpl _)).aestronglyMeasurable)
    ((integrable_const K1).add (hi2.abs.const_mul K2)) ?_ ?_
  · intro n
    filter_upwards [prod_ae w hr] with p hp
    obtain ⟨c1, c2, c3⟩ := cpl_facts (hε0 n) (hε1 n) hp.2.2
    rw [Real.norm_eq_abs]
    have := abs_hTrev_le κ hW hT hBf hp.1 (by linarith [hε0 n] : p.1.im ≤ (cpl (ε n) p).im)
      (by rw [hR]; linarith [hp.2.1])
    refine this.trans (le_of_eq ?_)
    rw [hK1, hK2]; ring
  · filter_upwards [prod_ae w hr] with p hp
    have hc : ContinuousAt (hTrev κ W T) p.1 :=
      (CharFun.continuousOn_hTrev κ hW hT).continuousAt (isOpen_H.mem_nhds hp.1)
    have ht : Tendsto (fun n => cpl (ε n) p) atTop (𝓝 p.1) := by
      have : Tendsto (fun n => p.1 + ((ε n : ℝ) : ℂ) * (I + p.2)) atTop
          (𝓝 (p.1 + ((0 : ℝ) : ℂ) * (I + p.2))) :=
        tendsto_const_nhds.add
          (((Complex.continuous_ofReal.tendsto 0).comp hεt).mul tendsto_const_nhds)
      rw [show p.1 + ((0 : ℝ) : ℂ) * (I + p.2) = p.1 by simp] at this
      exact this
    exact hc.tendsto.comp ht

/-! ## 7. Convergence in probability -/

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Chebyshev with a deterministic shift: if `F n − G = a n + Z n` a.s., `a n → 0` and
`E (Z n)² ≤ b n → 0`, then `F n → G` in probability. -/
theorem tendstoInMeasure_core {F : ℕ → Ω → ℝ} {G : Ω → ℝ} {a b : ℕ → ℝ} {Z : ℕ → Ω → ℝ}
    (hdec : ∀ n, ∀ᵐ ω ∂P, F n ω - G ω = a n + Z n ω) (ha : Tendsto a atTop (𝓝 0))
    (hZm : ∀ n, AEMeasurable (Z n) P)
    (hmom : ∀ n, ∫⁻ ω, ENNReal.ofReal (Z n ω ^ 2) ∂P ≤ ENNReal.ofReal (b n))
    (hb : Tendsto b atTop (𝓝 0)) :
    TendstoInMeasure P F atTop G := by
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  set c : ℝ := (δ / 2) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hup : Tendsto (fun n => ENNReal.ofReal (b n / c)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hb.div_const c)
    rwa [zero_div, ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => zero_le) ?_
  have hsmall : ∀ᶠ n in atTop, |a n| < δ / 2 := by
    have := (tendsto_order.1 (ha.abs)).2 (δ / 2) (by rw [abs_zero]; positivity)
    simpa using this
  filter_upwards [hsmall] with n hn
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (Z n ω ^ 2)) P :=
    ((hZm n).pow_const 2).ennreal_ofReal
  have hcheb := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal c)
  have hsub : {ω | δ ≤ ‖F n ω - G ω‖} ≤ᵐ[P]
      {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (Z n ω ^ 2)} := by
    filter_upwards [hdec n] with ω hω hmem
    have h1 : δ ≤ |a n + Z n ω| := by
      have : δ ≤ ‖F n ω - G ω‖ := hmem
      rwa [Real.norm_eq_abs, hω] at this
    have h2 : δ / 2 ≤ |Z n ω| := by
      have := abs_add_le (a n) (Z n ω)
      linarith
    show ENNReal.ofReal c ≤ ENNReal.ofReal (Z n ω ^ 2)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hc, ← sq_abs (Z n ω)]
    exact pow_le_pow_left₀ (by positivity) h2 2
  calc P {ω | δ ≤ ‖F n ω - G ω‖} ≤ P {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (Z n ω ^ 2)} :=
        measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (b n) / ENNReal.ofReal c := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc0))
          (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hcheb.trans (hmom n)
    _ = ENNReal.ofReal (b n / c) := (ENNReal.ofReal_div_of_pos hc0).symm

/-- Second moment of a balanced GFF difference. -/
theorem lintegral_sq_gff_le {X : Ω → Measure ℂ → ℝ} (hX : IsFreeGFFModConstH X P)
    {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) (hm : μ univ = ν univ) :
    ∫⁻ ω, ENNReal.ofReal ((X ω μ - X ω ν) ^ 2) ∂P ≤
      ENNReal.ofReal |kernelCov2 neumannH (μ, ν) (μ, ν)| := by
  have hL2 := SmoothConv.memLp_pair_sc hX hμ hν hm
  have c1 := hX.covariance_eq (μ, ν) (μ, ν) hμ hν hm hμ hν hm
  dsimp only at c1
  have hmean := hX.centered _ _ hμ hν hm
  have key : ∫ ω, (X ω μ - X ω ν) ^ 2 ∂P =
      cov[fun ω => X ω μ - X ω ν, fun ω => X ω μ - X ω ν; P] := by
    unfold covariance
    rw [hmean]
    simp only [sub_zero, sq]
  rw [← ofReal_integral_eq_lintegral_ofReal hL2.integrable_sq
    (ae_of_all _ fun _ => sq_nonneg _), key, c1]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

end Prob

theorem evalReg_zero (x : FieldSample) : evalReg x 0 = 0 := by
  unfold evalReg
  simp only [integral_zero_measure]
  exact tendsto_const_nhds.limUnder_eq

theorem couplingFieldRev_apply (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (x : FieldSample)
    (μ : Measure ℂ) :
    couplingFieldRev κ W T x μ = (∫ z, hTrev κ W T z ∂μ) + evalReg x (μ.map (revMap W T)) := by
  rw [CouplingMarkov.couplingFieldRev_eq]
  show (∫ z, hTrev κ W T z ∂μ) + (evalReg x (μ.map (revMap W T)) +
    0 * ∫ z, Real.log ‖deriv (revMap W T) z‖ ∂μ) = _
  ring

theorem pairRaw_moll (y : FieldSample) (w : ℂ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    pairRaw y (moll w r ε) = y (mollMeas w r ε) - y 0 := by
  rw [CharFun.pairRaw_eq_tdens, tdens_moll w r hε, tdens_neg_moll]

theorem pairRaw_couplingFieldRev_moll (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (x : FieldSample) (w : ℂ)
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    pairRaw (couplingFieldRev κ W T x) (moll w r ε) =
      (∫ z, hTrev κ W T z ∂mollMeas w r ε) +
        evalReg x ((mollMeas w r ε).map (revMap W T)) := by
  rw [pairRaw_moll _ w r hε, couplingFieldRev_apply, couplingFieldRev_apply, Measure.map_zero,
    evalReg_zero, integral_zero_measure]
  ring

theorem tendsto_rpow_twelfth {ε : ℕ → ℝ} (hεt : Tendsto ε atTop (𝓝 0)) (C : ℝ) :
    Tendsto (fun n => C * ε n ^ (1 / 12 : ℝ)) atTop (𝓝 0) := by
  have h := ((Real.continuousAt_rpow_const 0 (1 / 12 : ℝ) (Or.inr (by norm_num))).tendsto.comp
    hεt).const_mul C
  rwa [Real.zero_rpow (by norm_num), mul_zero] at h

theorem supp_of_ae {ν : Measure ℂ} {Bf : ℝ} (h : ∀ᵐ y ∂ν, ‖y‖ ≤ Bf ∧ 0 < y.im) :
    ν (Metric.closedBall 0 Bf ∩ Hbar)ᶜ = 0 :=
  measure_mono_null (fun y hy (h' : ‖y‖ ≤ Bf ∧ 0 < y.im) => hy
    ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact h'.1, le_of_lt h'.2⟩)
    (ae_iff.1 h : ν {y | ¬(‖y‖ ≤ Bf ∧ 0 < y.im)} = 0)

/-- The pushed-forward mollified and circle measures: Frostman, supported, admissible, with the
energy bound (the common input of the fixed-driver TREG statements). -/
theorem push_facts (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ Bf CF Cst : ℝ,
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ((mollMeas w r ε).map (revMap W T)) (Metric.closedBall 0 Bf ∩ Hbar)ᶜ = 0 ∧
        QuantumZipper.IsFrostman ((mollMeas w r ε).map (revMap W T)) (1 / 3) CF ∧
        IsAdmissibleH ((mollMeas w r ε).map (revMap W T)) ∧
        (mollMeas w r ε).map (revMap W T) univ = (foldedCircle w r).map (revMap W T) univ ∧
        |kernelCov2 neumannH ((mollMeas w r ε).map (revMap W T),
          (foldedCircle w r).map (revMap W T)) ((mollMeas w r ε).map (revMap W T),
          (foldedCircle w r).map (revMap W T))| ≤ Cst * ε ^ (1 / 12 : ℝ)) ∧
      ((foldedCircle w r).map (revMap W T)) (Metric.closedBall 0 Bf ∩ Hbar)ᶜ = 0 ∧
      QuantumZipper.IsFrostman ((foldedCircle w r).map (revMap W T)) (1 / 3) CF ∧
      IsAdmissibleH ((foldedCircle w r).map (revMap W T)) := by
  set R := ‖w‖ + r + 2 with hR
  obtain ⟨Bf, hBf0, hBf⟩ := exists_norm_revMap_le hW hT R
  obtain ⟨Cst, hCst⟩ := abs_energy_moll_le hW hT w hr
  set CF := 18 / Real.sqrt r + 12 * Real.sqrt (R ^ 2 + 4 * T) / r with hCF
  have hFs : QuantumZipper.IsFrostman ((foldedCircle w r).map (revMap W T)) (1 / 3) CF :=
    isFrostman_revMap_foldedCircle hW hT hr le_rfl (show ‖w‖ + r ≤ R by rw [hR]; linarith)
  have hSs := supp_of_ae (ae_push_fc hW hT w hr hBf)
  refine ⟨Bf, CF, Cst, fun ε hε hε1 => ?_, hSs, hFs,
    FrostmanReg.isAdmissibleH_of_frostman hSs hFs (by norm_num)⟩
  have hF : QuantumZipper.IsFrostman ((mollMeas w r ε).map (revMap W T)) (1 / 3) CF :=
    isFrostman_moll hW hT w hr hε hε1
  have hS := supp_of_ae (ae_push_moll hW hT w hr hε hε1 hBf)
  refine ⟨hS, hF, FrostmanReg.isAdmissibleH_of_frostman hS hF (by norm_num), ?_,
    hCst ε hε hε1⟩
  rw [Measure.map_apply (measurable_revMap hW hT) MeasurableSet.univ,
    Measure.map_apply (measurable_revMap hW hT) MeasurableSet.univ, preimage_univ,
    measure_univ, measure_univ]

/-- **TREG, fixed driver.** -/
theorem tendstoInMeasure_pairRaw_moll (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hεt : Tendsto ε atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => pairRaw (couplingFieldRev κ W T (X ω)) (moll w r (ε n)))
      atTop (fun ω => couplingFieldRev κ W T (X ω) (foldedCircle w r)) := by
  obtain ⟨Bf, CF, Cst, hm, hSs, hFs, hAs⟩ := push_facts hW hT w hr
  have hreg : ∀ᵐ ω ∂P, (∀ n, evalReg (X ω) ((mollMeas w r (ε n)).map (revMap W T)) =
        X ω ((mollMeas w r (ε n)).map (revMap W T))) ∧
      evalReg (X ω) ((foldedCircle w r).map (revMap W T)) =
        X ω ((foldedCircle w r).map (revMap W T)) := by
    filter_upwards [ae_all_iff.2 fun n => FrostmanReg.ae_evalReg_eq_frostman hX
      (hm (ε n) (hε0 n) (hε1 n)).1 (hm (ε n) (hε0 n) (hε1 n)).2.1 (by norm_num),
      FrostmanReg.ae_evalReg_eq_frostman hX hSs hFs (by norm_num)] with ω h1 h2
    exact ⟨h1, h2⟩
  refine tendstoInMeasure_core
    (a := fun n => (∫ z, hTrev κ W T z ∂mollMeas w r (ε n)) -
      ∫ z, hTrev κ W T z ∂foldedCircle w r)
    (Z := fun n ω => X ω ((mollMeas w r (ε n)).map (revMap W T)) -
      X ω ((foldedCircle w r).map (revMap W T)))
    (b := fun n => Cst * ε n ^ (1 / 12 : ℝ)) (fun n => ?_) ?_ (fun n => ?_) (fun n => ?_)
    (tendsto_rpow_twelfth hεt Cst)
  · filter_upwards [hreg] with ω hω
    rw [pairRaw_couplingFieldRev_moll κ W T _ w r (hε0 n), couplingFieldRev_apply, hω.1 n, hω.2]
    ring
  · have := (tendsto_integral_hTrev_moll κ hW hT w hr hε0 hε1 hεt).sub_const
      (∫ z, hTrev κ W T z ∂foldedCircle w r)
    rwa [sub_self] at this
  · exact ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  · obtain ⟨-, -, hA, hmass, hE⟩ := hm (ε n) (hε0 n) (hε1 n)
    exact (lintegral_sq_gff_le hX hA hAs hmass).trans (ENNReal.ofReal_le_ofReal hE)

/-! ## 8. TREG for `ofFun h0rev + X` -/

theorem mollMeas_ae_H (w : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ z ∂mollMeas w r ε, z ∈ H := by
  have hS : MeasurableSet {z : ℂ | z ∈ H} := isOpen_H.measurableSet
  rw [mollMeas, ae_map_iff (measurable_cpl ε).aemeasurable hS]
  filter_upwards [prod_ae w hr] with p hp
  obtain ⟨h1, -, -⟩ := cpl_facts hε hε1 hp.2.2
  show 0 < (cpl ε p).im
  linarith [hp.1]

theorem map_revMap_zero_eq {μ : Measure ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ H) :
    μ.map (revMap (fun _ => (0 : ℝ)) 0) = μ := by
  have h : revMap (fun _ => (0 : ℝ)) 0 =ᵐ[μ] id :=
    hμ.mono fun z hz => CharFun.revMap_zero_eq continuous_const rfl hz
  rw [Measure.map_congr h, Measure.map_id]

/-- **TREG for `ofFun h0rev + X`.** -/
theorem tendstoInMeasure_pairRaw_moll_h0rev (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (w : ℂ) {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hεt : Tendsto ε atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => pairRaw (ofFun (h0rev κ) + X ω) (moll w r (ε n))) atTop
      (fun ω => (ofFun (h0rev κ) + X ω) (foldedCircle w r)) := by
  have hW : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  obtain ⟨Bf, CF, Cst, hm, hSs, hFs, hAs⟩ := push_facts hW le_rfl w hr
  have hσ : (foldedCircle w r).map (revMap (fun _ => (0 : ℝ)) 0) = foldedCircle w r :=
    map_revMap_zero_eq (foldedCircle_ae_mem_H w hr)
  have hmo : ∀ n, (mollMeas w r (ε n)).map (revMap (fun _ => (0 : ℝ)) 0) = mollMeas w r (ε n) :=
    fun n => map_revMap_zero_eq (mollMeas_ae_H w hr (hε0 n) (hε1 n))
  rw [hσ] at hAs
  have h0 : ∀ᵐ ω ∂P, X ω 0 = 0 := by
    filter_upwards [hX.linear _ _ hAs hAs 0 0] with ω h
    simpa using h
  have e : ∀ μ : Measure ℂ, (∀ᵐ z ∂μ, z ∈ H) →
      ∫ z, hTrev κ (fun _ => (0 : ℝ)) 0 z ∂μ = ∫ z, h0rev κ z ∂μ := fun μ hμ =>
    integral_congr_ae (hμ.mono fun z hz => CharFun.hTrev_zero_eq κ continuous_const rfl hz)
  refine tendstoInMeasure_core
    (a := fun n => (∫ z, h0rev κ z ∂mollMeas w r (ε n)) - ∫ z, h0rev κ z ∂foldedCircle w r)
    (Z := fun n ω => X ω (mollMeas w r (ε n)) - X ω (foldedCircle w r))
    (b := fun n => Cst * ε n ^ (1 / 12 : ℝ)) (fun n => ?_) ?_ (fun n => ?_) (fun n => ?_)
    (tendsto_rpow_twelfth hεt Cst)
  · filter_upwards [h0] with ω hω
    rw [pairRaw_moll _ w r (hε0 n)]
    simp only [Pi.add_apply, ofFun, hω, integral_zero_measure]
    ring
  · have := (tendsto_integral_hTrev_moll κ hW le_rfl w hr hε0 hε1 hεt).sub_const
      (∫ z, hTrev κ (fun _ => (0 : ℝ)) 0 z ∂foldedCircle w r)
    rw [sub_self] at this
    refine this.congr fun n => ?_
    rw [e _ (mollMeas_ae_H w hr (hε0 n) (hε1 n)), e _ (foldedCircle_ae_mem_H w hr)]
  · exact ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  · obtain ⟨-, -, hA, hmass, hE⟩ := hm (ε n) (hε0 n) (hε1 n)
    rw [hmo n] at hA
    rw [hmo n, hσ] at hmass hE
    exact (lintegral_sq_gff_le hX hA hAs hmass).trans (ENNReal.ofReal_le_ofReal hE)

/-! ## 9. Random driver independent of the field -/

theorem Y2f_eq (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) (x : FieldSample) :
    CharFun.Y2f κ T hT f x = couplingFieldRev κ (CharFun.Wof κ T hT f) T x := by
  rw [CouplingMarkov.couplingFieldRev_eq]; rfl

/-- The value of the reverse coupling field at a folded circle, jointly measurable in the
driver path and the field sample. -/
def valFC (κ T : ℝ) (hT : 0 ≤ T) (w : ℂ) (r : ℝ) (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) : ℝ :=
  (∫ z, CharFun.hTm κ T hT (p.1, z) ∂foldedCircle w r) +
    evalReg p.2 ((foldedCircle w r).map (revMap (CharFun.Wof κ T hT p.1) T))

theorem measurable_valFC (κ T : ℝ) (hT : 0 ≤ T) (w : ℂ) (r : ℝ) :
    Measurable (valFC κ T hT w r) :=
  (((CharFun.measurable_hTm κ T hT).stronglyMeasurable.integral_prod_right'
    (ν := foldedCircle w r)).measurable.comp measurable_fst).add
    (UnzipFull.measurable_evalReg_push_gen κ T hT _)

theorem valFC_eq (κ T : ℝ) (hT : 0 ≤ T) (w : ℂ) {r : ℝ} (hr : 0 < r)
    (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) :
    valFC κ T hT w r p =
      couplingFieldRev κ (CharFun.Wof κ T hT p.1) T p.2 (foldedCircle w r) := by
  rw [couplingFieldRev_apply, valFC]
  congr 1
  exact integral_congr_ae ((foldedCircle_ae_mem_H w hr).mono fun z hz =>
    CharFun.hTm_eq κ T hT p.1 hz)

/-- **TREG, random driver path independent of the field.** -/
theorem tendstoInMeasure_pairRaw_moll_random (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g)
    (hind : IndepFun g X P) (w : ℂ) {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hεt : Tendsto ε atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun n ω => pairRaw (couplingFieldRev κ (CharFun.Wof κ T hT (g ω)) T (X ω))
        (moll w r (ε n)))
      atTop (fun ω => couplingFieldRev κ (CharFun.Wof κ T hT (g ω)) T (X ω)
        (foldedCircle w r)) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  haveI : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (P.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  set Fn : ℕ → C(Icc (0 : ℝ) T, ℝ) × FieldSample → ℝ := fun n p =>
    pairRaw (CharFun.Y2f κ T hT p.1 p.2) (moll w r (ε n)) - valFC κ T hT w r p with hFn
  have hFm : ∀ n, Measurable (Fn n) := fun n =>
    (CharFun.measurable_pair_Y2f κ T hT (mollTF w hr (hε0 n))).sub (measurable_valFC κ T hT w r)
  set S : ℕ → Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) := fun n => {p | δ ≤ ‖Fn n p‖} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n => measurableSet_le measurable_const (hFm n).norm
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hXm.aemeasurable).1 hind
  have hFeq : ∀ n p, Fn n p =
      pairRaw (couplingFieldRev κ (CharFun.Wof κ T hT p.1) T p.2) (moll w r (ε n)) -
        couplingFieldRev κ (CharFun.Wof κ T hT p.1) T p.2 (foldedCircle w r) := fun n p => by
    rw [hFn]; dsimp only; rw [Y2f_eq, valFC_eq κ T hT w hr]
  have heq : ∀ n, P {ω | δ ≤ ‖pairRaw (couplingFieldRev κ (CharFun.Wof κ T hT (g ω)) T (X ω))
        (moll w r (ε n)) - couplingFieldRev κ (CharFun.Wof κ T hT (g ω)) T (X ω)
          (foldedCircle w r)‖} = ∫⁻ f, (P.map X) (Prod.mk f ⁻¹' S n) ∂(P.map g) := by
    intro n
    have hset : {ω | δ ≤ ‖pairRaw (couplingFieldRev κ (CharFun.Wof κ T hT (g ω)) T (X ω))
        (moll w r (ε n)) - couplingFieldRev κ (CharFun.Wof κ T hT (g ω)) T (X ω)
          (foldedCircle w r)‖} = (fun ω => (g ω, X ω)) ⁻¹' S n := by
      ext ω; simp only [mem_setOf_eq, mem_preimage, hS, hFeq]
    rw [hset, ← Measure.map_apply (hg.prodMk hXm) (hSm n), hprod, Measure.prod_apply (hSm n)]
  simp_rw [heq]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _, 0 ∂(P.map g) by simp]
  refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
    (fun n => measurable_measure_prodMk_left (hSm n))
    (fun n => ae_of_all _ fun f => prob_le_one) (by simp) (ae_of_all _ fun f => ?_)
  have hfix := tendstoInMeasure_pairRaw_moll κ hX (CharFun.continuous_Wof κ T hT f) hT w hr
    hε0 hε1 hεt
  rw [tendstoInMeasure_iff_norm] at hfix
  refine (hfix δ hδ).congr fun n => ?_
  rw [Measure.map_apply hXm (measurable_prodMk_left (hSm n))]
  congr 1
  ext ω
  simp only [mem_setOf_eq, mem_preimage, hS, hFeq]

/-! ## 10. Linearity of pairings for general test functions -/

theorem integrable_tf (ρ : TestFun H) : Integrable ρ.1 :=
  (CharFun.tf_continuous ρ).integrable_of_hasCompactSupport ρ.2.2.1

/-- The test function `a ρ₁ + ρ₂`. -/
def tfLin (a : ℝ) (ρ₁ ρ₂ : TestFun H) : TestFun H :=
  ⟨fun z => a * ρ₁.1 z + ρ₂.1 z, (contDiff_const.mul ρ₁.2.1).add ρ₂.2.1,
    (ρ₁.2.2.1.mul_left).add ρ₂.2.2.1, by
      have hs : Function.support (fun z => a * ρ₁.1 z + ρ₂.1 z) ⊆
          Function.support ρ₁.1 ∪ Function.support ρ₂.1 := fun z hz => by
        by_contra hc
        simp only [mem_union, Function.mem_support, not_or, not_not] at hc
        simp [hc.1, hc.2] at hz
      exact (closure_mono hs).trans (by
        rw [closure_union]; exact union_subset ρ₁.2.2.2 ρ₂.2.2.2)⟩

/-- `a ρ₁ + ρ₂` as a mass-zero test function, when `a ∫ρ₁ + ∫ρ₂ = 0`. -/
def tfLin0 (a : ℝ) (ρ₁ ρ₂ : TestFun H) (h : a * (∫ z, ρ₁.1 z) + ∫ z, ρ₂.1 z = 0) :
    TestFun0 H :=
  ⟨tfLin a ρ₁ ρ₂, by
    show ∫ z, (a * ρ₁.1 z + ρ₂.1 z) = 0
    rw [integral_add ((integrable_tf ρ₁).const_mul a) (integrable_tf ρ₂), integral_const_mul]
    exact h⟩

/-- Linearity of the pairings of `ofFun h0rev + X` (general test functions). -/
theorem ae_pairRaw_lin_h0rev (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} (hX : IsFreeGFFModConstH X P) (a : ℝ) (ρ₁ ρ₂ : TestFun H) :
    ∀ᵐ ω ∂P, pairRaw (ofFun (h0rev κ) + X ω) (tfLin a ρ₁ ρ₂).1 =
      a * pairRaw (ofFun (h0rev κ) + X ω) ρ₁.1 + pairRaw (ofFun (h0rev κ) + X ω) ρ₂.1 := by
  have h : ∀ z, (tfLin a ρ₁ ρ₂).1 z = a * ρ₁.1 z + ρ₂.1 z := fun z => rfl
  filter_upwards [CharFun.ae_lin_push hX CharFun.goodMap_id ρ₁ ρ₂ (tfLin a ρ₁ ρ₂) a h]
    with ω hω
  simp only [Measure.map_id] at hω
  simp only [CharFun.pairRaw_add, CharFun.pairRaw_ofFun (CharFun.continuousOn_h0rev κ),
    CharFun.pairRaw_eq_tdens (X ω)]
  rw [CharFun.integral_lin (CharFun.continuousOn_h0rev κ) ρ₁ ρ₂ (tfLin a ρ₁ ρ₂) a h, hω]
  ring

/-- Linearity of the pairings of the reverse coupling field with a random driver path
independent of the field (general test functions). -/
theorem ae_pairRaw_lin_Y2f (κ T : ℝ) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → FieldSample} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g)
    (hind : IndepFun g X P) (a : ℝ) (ρ₁ ρ₂ : TestFun H) :
    ∀ᵐ ω ∂P, pairRaw (CharFun.Y2f κ T hT (g ω) (X ω)) (tfLin a ρ₁ ρ₂).1 =
      a * pairRaw (CharFun.Y2f κ T hT (g ω) (X ω)) ρ₁.1 +
        pairRaw (CharFun.Y2f κ T hT (g ω) (X ω)) ρ₂.1 := by
  have h : ∀ z, (tfLin a ρ₁ ρ₂).1 z = a * ρ₁.1 z + ρ₂.1 z := fun z => rfl
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hE : MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      pairRaw (CharFun.Y2f κ T hT p.1 p.2) (tfLin a ρ₁ ρ₂).1 =
        a * pairRaw (CharFun.Y2f κ T hT p.1 p.2) ρ₁.1 +
          pairRaw (CharFun.Y2f κ T hT p.1 p.2) ρ₂.1} :=
    measurableSet_eq_fun (CharFun.measurable_pair_Y2f κ T hT (tfLin a ρ₁ ρ₂))
      ((measurable_const.mul (CharFun.measurable_pair_Y2f κ T hT ρ₁)).add
        (CharFun.measurable_pair_Y2f κ T hT ρ₂))
  refine CharFun.ae_indep hg hXm hind hE fun f => ?_
  filter_upwards [CharFun.cond_Y2f κ T hT hX ρ₁ f, CharFun.cond_Y2f κ T hT hX ρ₂ f,
    CharFun.cond_Y2f κ T hT hX (tfLin a ρ₁ ρ₂) f,
    CharFun.ae_lin_push hX (CharFun.goodMap_Wof κ T hT f) ρ₁ ρ₂ (tfLin a ρ₁ ρ₂) a h]
    with ω h1 h2 h3 hω
  show pairRaw (CharFun.Y2f κ T hT f (X ω)) (tfLin a ρ₁ ρ₂).1 =
    a * pairRaw (CharFun.Y2f κ T hT f (X ω)) ρ₁.1 + pairRaw (CharFun.Y2f κ T hT f (X ω)) ρ₂.1
  rw [h1, h2, h3, hω]
  simp only [CharFun.Xfun]
  rw [CharFun.integral_lin (CharFun.continuousOn_hTrev κ (CharFun.continuous_Wof κ T hT f) hT)
    ρ₁ ρ₂ (tfLin a ρ₁ ρ₂) a h]
  ring

end TReg
end QuantumZipper

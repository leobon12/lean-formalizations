import QuantumZipper.Proofs.GFF.K3.MixedAnnulus
import QuantumZipper.Proofs.GFF.K3.MixedPoincare
import QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Local admissibility for the mixed space (GFF-K3 node M4)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M4).

Route (a direct energy bound, no Riesz vectors of `bind` measures):

1. *Pointwise bound* (from M1, `s → 0`): for `z ∈ Hbar` and `0 < s' ≤ ρ`,
   `|f z − ∫ f d fold_{z,s'}| ≤ (2π)⁻¹ ∫_H ‖∇f‖ · 2 k_ρ(· − z)`, with `k_ρ(u) = ‖u‖⁻¹ 1{‖u‖<ρ}`.
2. *Averaging* over `s' ∈ (R, 2R)` with weight `s'` (polar coordinates) turns the circle
   term into `(2π)⁻¹ · 2 ∫_D |f|`, provided `H ∩ B(z, 2R) ⊆ D`.
3. Integrate against `μ`; the gradient term is handled by Tonelli, Cauchy–Schwarz and the
   kernel bound `∫ k(y−a) k(y−b) dy ≤ C (1 + log⁻ ‖a − b‖)` (admissibility of `μ`); the `L¹`
   term by Cauchy–Schwarz and the Poincaré inequality M3.

Sources. Step 1 is the localized first-order representation formula
`f(x) = ω₁⁻¹ ∫ ∇f(y)·(x−y)/|x−y|² dy` (D. R. Adams, L. I. Hedberg, *Function Spaces and Potential
Theory*, Springer 1996, eq. (1.2.4), p. 8), in the form of the annulus identity M1; Steps 1–2
follow the classical potential estimate `|u(x) − u_B| ≤ C ∫_B |∇u(y)| |x−y|^{1−n} dy`
(D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, 2001 ed.,
Lemma 7.16, eq. (7.41), p. 162; `literature/GilbargTrudinger_EllipticPDE_2001.pdf`, PDF p. 175):
the same radial fundamental theorem of calculus followed by averaging, but with the average over a
folded annulus (weight `s'` on `s' ∈ (R, 2R)`) in place of the average over a convex set, and the
radial integration packaged as the annulus identity M1. Step 3 is Fubini for the
mutual energy (Adams–Hedberg, §2.3, eq. (2.3.3), p. 24) together with the planar composition
bound `∫ |y−a|⁻¹ |y−b|⁻¹ dy ≲ 1 + log⁻|a−b|` for truncated Riesz kernels (the critical case of the
composition law of Riesz kernels, N. S. Landkof, *Foundations of Modern Potential Theory*, Ch. I;
proved here directly by splitting at `|y − a| = |a − b|/2`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal

namespace QuantumZipper.K3

/-! ## Local discs -/

/-- A local disc of `(D, S)` around `z` (blueprint §0). -/
def LocalBall (D S : Set ℂ) (z : ℂ) (R : ℝ) : Prop :=
  z ∈ Hbar ∧ 0 < R ∧ D ⊆ H ∧ closedBall z R ∩ Hbar ⊆ closure D ∧ closedBall z R ∩ frontier D ⊆ S

theorem LocalBall.mem_of_mem_H {D S : Set ℂ} {z : ℂ} {R : ℝ} (h : LocalBall D S z R)
    (hD : IsOpen D) (hS : S ⊆ {z : ℂ | z.im = 0}) {y : ℂ} (hy : y ∈ H) (hyz : ‖y - z‖ ≤ R) :
    y ∈ D := by
  by_contra hyD
  have hyb : y ∈ closedBall z R := by rwa [mem_closedBall, dist_eq_norm]
  have hcl : y ∈ closure D := h.2.2.2.1 ⟨hyb, show (0 : ℝ) ≤ y.im from le_of_lt hy⟩
  have hfr : y ∈ frontier D := by rw [hD.frontier_eq]; exact ⟨hcl, hyD⟩
  have h0 : y.im = 0 := hS (h.2.2.2.2 ⟨hyb, hfr⟩)
  have h1 : 0 < y.im := hy
  linarith

theorem LocalBall.mem_closure {D S : Set ℂ} {z : ℂ} {R : ℝ} (h : LocalBall D S z R) :
    z ∈ closure D :=
  h.2.2.2.1 ⟨mem_closedBall_self h.2.1.le, h.1⟩

/-! ## Elementary geometry -/

theorem norm_sub_le_norm_sub_conj {y z : ℂ} (hy : 0 ≤ y.im) (hz : 0 ≤ z.im) :
    ‖y - z‖ ≤ ‖y - conj z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith [mul_nonneg hy hz]

/-- The truncated inverse-distance kernel `k_R(u) = ‖u‖⁻¹ 1{‖u‖ < R}`. -/
def kInv (R : ℝ) (u : ℂ) : ℝ≥0∞ := if ‖u‖ < R then ENNReal.ofReal ‖u‖⁻¹ else 0

theorem measurable_kInv (R : ℝ) : Measurable (kInv R) := by
  unfold kInv
  exact Measurable.ite (measurableSet_lt measurable_norm measurable_const)
    (ENNReal.measurable_ofReal.comp measurable_norm.inv) measurable_const

theorem enorm_annulusTerm_le {c : ℂ} {s s' R : ℝ} (hs' : s' ≤ R) (y : ℂ) :
    ‖annulusTerm c s s' y‖ₑ ≤ kInv R (y - c) := by
  unfold annulusTerm kInv
  split_ifs with h1 h2
  · exact le_of_eq (by rw [neg_div, enorm_neg, ← ofReal_norm, norm_radial_vec])
  · exact absurd (h1.2.trans_le hs') h2
  · simp
  · simp

theorem kInv_conj_le {y z : ℂ} (hy : 0 ≤ y.im) (hz : 0 ≤ z.im) (hyz : y ≠ z) (R : ℝ) :
    kInv R (y - conj z) ≤ kInv R (y - z) := by
  have hle := norm_sub_le_norm_sub_conj hy hz
  have hpos : 0 < ‖y - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
  unfold kInv
  split_ifs with h1 h2
  · exact ENNReal.ofReal_le_ofReal (inv_anti₀ hpos hle)
  · exact absurd (hle.trans_lt h1) h2
  · exact zero_le
  · exact le_rfl

theorem enorm_annulusField_le {z y : ℂ} {s s' R : ℝ} (hs' : s' ≤ R) (hy : 0 ≤ y.im)
    (hz : 0 ≤ z.im) (hyz : y ≠ z) :
    ‖annulusField z s s' y‖ₑ ≤ 2 * kInv R (y - z) := by
  rw [annulusField_eq, two_mul]
  exact (enorm_add_le _ _).trans (add_le_add (enorm_annulusTerm_le hs' y)
    ((enorm_annulusTerm_le hs' y).trans (kInv_conj_le hy hz hyz R)))

/-! ## Step 1: the pointwise bound -/

theorem tendsto_integral_circleUnif_zero {g : ℂ → ℝ} (hg : Continuous g) (w : ℂ) :
    Tendsto (fun r => ∫ x, g x ∂(circleUnif w r)) (𝓝[>] 0) (𝓝 (g w)) := by
  simp_rw [integral_circleUnif_eq hg]
  have hvol : ∫ θ in Ioo (-π) π, g (circleMap w 0 θ) = 2 * π * g w := by
    simp only [circleMap_zero_radius, Function.const_apply, setIntegral_const, smul_eq_mul]
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    ring
  have hgw : g w = (2 * π)⁻¹ * ∫ θ in Ioo (-π) π, g (circleMap w 0 θ) := by
    rw [hvol]; field_simp
  rw [hgw]
  refine Tendsto.const_mul _ ?_
  obtain ⟨C, hC⟩ := (isCompact_closedBall w 1).exists_bound_of_continuousOn hg.continuousOn
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun r => (hg.comp (continuous_circleMap w r)).aestronglyMeasurable)
    ?_ (integrable_const C) (Eventually.of_forall fun θ => ?_)
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
    refine Eventually.of_forall fun θ => hC _ ?_
    rw [mem_closedBall, dist_eq_norm, norm_circleMap_sub_center, abs_of_pos hr.1]
    exact hr.2.le
  · have hcont : Continuous fun r : ℝ => g (circleMap w r θ) :=
      hg.comp ((continuous_circleMap_uncurry w).comp (continuous_id.prodMk continuous_const))
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

theorem integral_foldedCircle_eq {f : ℂ → ℝ} (hf : Continuous f) (z : ℂ) (r : ℝ) :
    ∫ x, f x ∂(foldedCircle z r) = ∫ x, (f ∘ foldH) x ∂(circleUnif z r) := by
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable hf.aestronglyMeasurable]
  rfl

/-- **Step 1.** The pointwise bound. -/
theorem ofReal_abs_sub_foldedCircle_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {z : ℂ}
    (hz : z ∈ Hbar) {s' R : ℝ} (hs' : 0 < s') (hs'R : s' ≤ R) :
    ENNReal.ofReal |f z - ∫ x, f x ∂(foldedCircle z s')| ≤
      ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv R (y - z)) := by
  have hz' : 0 ≤ z.im := hz
  have hcont : Continuous (f ∘ foldH) := hf.continuous.comp continuous_foldH_K3
  have hlim : Tendsto (fun s => ∫ x, f x ∂(foldedCircle z s)) (𝓝[>] 0) (𝓝 (f z)) := by
    have h := tendsto_integral_circleUnif_zero hcont z
    have hfz : (f ∘ foldH) z = f z := by simp [Function.comp, foldH, hz']
    rw [hfz] at h
    exact h.congr' (Eventually.of_forall fun s => (integral_foldedCircle_eq hf.continuous z s).symm)
  have hbound : ∀ s, 0 < s → s < s' →
      ENNReal.ofReal |∫ x, f x ∂(foldedCircle z s) - ∫ x, f x ∂(foldedCircle z s')| ≤
        ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv R (y - z)) := by
    intro s hs hss'
    rw [← annulus_identity hf hz hs hss', ← Real.norm_eq_abs, ofReal_norm, enorm_mul]
    refine mul_le_mul' ?_ ?_
    · rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by positivity)]
    · refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
      have hne : ∀ᵐ y ∂(volume : Measure ℂ), y ∉ ({z} : Set ℂ) :=
        measure_eq_zero_iff_ae_notMem.mp (measure_singleton z)
      filter_upwards [ae_restrict_mem measurableSet_H_mx, ae_restrict_of_ae hne] with y hy hyz
      have hy' : 0 ≤ y.im := le_of_lt hy
      exact ((fderiv ℝ f y).le_opENorm _).trans
        (mul_le_mul_right (enorm_annulusField_le hs'R hy' hz' hyz) _)
  have ht : Tendsto (fun s => ENNReal.ofReal |∫ x, f x ∂(foldedCircle z s) -
      ∫ x, f x ∂(foldedCircle z s')|) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal |f z - ∫ x, f x ∂(foldedCircle z s')|)) :=
    ((ENNReal.continuous_ofReal.comp continuous_abs).tendsto _).comp (hlim.sub_const _)
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hs'] with s hs
  exact hbound s hs.1 hs.2

/-! ## Step 2: averaging in polar coordinates -/

/-- Polar coordinates for lintegrals (radius outside). -/
theorem lintegral_eq_polar {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G y = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal ρ * G (circleMap 0 ρ θ) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hpt : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  simp_rw [polarCoord_symm_eq_circleMap, smul_eq_mul]
  rw [hpt, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  exact ((ENNReal.measurable_ofReal.comp measurable_fst).mul
    (hG.comp (continuous_circleMap_uncurry 0).measurable)).aemeasurable

theorem lintegral_radius_circle_le {g : ℂ → ℝ≥0∞} (hg : Measurable g) (z : ℂ) {a b : ℝ}
    (ha : 0 ≤ a) :
    ∫⁻ ρ in Ioo a b, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap z ρ θ) ≤
      ∫⁻ y in ball z b, g y := by
  set G : ℂ → ℝ≥0∞ := fun y => (ball z b).indicator g (z + y) with hGdef
  have hGm : Measurable G :=
    (hg.indicator measurableSet_ball).comp (measurable_const.add measurable_id)
  have h1 : ∫⁻ y in ball z b, g y = ∫⁻ y, G y := by
    rw [← lintegral_indicator measurableSet_ball]
    exact (lintegral_add_left_eq_self _ z).symm
  rw [h1, lintegral_eq_polar hGm]
  calc ∫⁻ ρ in Ioo a b, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap z ρ θ)
      = ∫⁻ ρ in Ioo a b, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * G (circleMap 0 ρ θ) := by
        refine setLIntegral_congr_fun measurableSet_Ioo (fun ρ hρ => ?_)
        refine lintegral_congr fun θ => ?_
        have hmem : z + circleMap 0 ρ θ ∈ ball z b := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_circleMap_zero,
            abs_of_pos (ha.trans_lt hρ.1)]
          exact hρ.2
        have hcm : circleMap z ρ θ = z + circleMap 0 ρ θ := by simp [circleMap]
        simp only [hGdef, indicator_of_mem hmem, hcm]
    _ ≤ _ := lintegral_mono_set fun x hx => ha.trans_lt hx.1

theorem lintegral_ball_foldH_le {D : Set ℂ} (hDm : MeasurableSet D) {z : ℂ} {r : ℝ}
    (hz : z ∈ Hbar) (hsub : ∀ y ∈ H, ‖y - z‖ < r → y ∈ D) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y in ball z r, g (foldH y) ≤ 2 * ∫⁻ y in D, g y := by
  have hz' : 0 ≤ z.im := hz
  have hmp : MeasurePreserving (Complex.conjLIE : ℂ → ℂ) volume volume :=
    Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (Complex.conjLIE : ℂ → ℂ) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hconj : ∫⁻ y, D.indicator g (conj y) = ∫⁻ y, D.indicator g y := by
    have h := hmp.lintegral_comp_emb hemb (D.indicator g)
    simpa only [Complex.conjLIE_apply] using h
  calc ∫⁻ y in ball z r, g (foldH y)
      ≤ ∫⁻ y, (D.indicator g y + D.indicator g (conj y)) := by
        rw [← lintegral_indicator measurableSet_ball]
        refine lintegral_mono_ae ?_
        filter_upwards [ae_im_ne_zero] with y hy
        by_cases hyb : y ∈ ball z r
        · rw [indicator_of_mem hyb]
          have hyr : ‖y - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hyb
          rcases lt_or_gt_of_ne hy with hlt | hgt
          · have hf : foldH y = conj y := by simp [foldH, not_le.mpr hlt]
            have hcH : conj y ∈ H := by
              change 0 < (conj y).im; rw [Complex.conj_im]; linarith
            have hle : ‖conj y - z‖ ≤ ‖y - z‖ := by
              have h := norm_sub_le_norm_sub_conj (le_of_lt hcH) hz'
              rwa [← map_sub, Complex.norm_conj] at h
            rw [hf, indicator_of_mem (hsub _ hcH (hle.trans_lt hyr))]
            exact le_add_self
          · have hf : foldH y = y := by simp [foldH, hgt.le]
            rw [hf, indicator_of_mem (hsub y hgt hyr)]
            exact le_self_add
        · rw [indicator_of_notMem hyb]; exact zero_le
    _ = 2 * ∫⁻ y in D, g y := by
        rw [lintegral_add_left (hg.indicator hDm), hconj, lintegral_indicator hDm, two_mul]

theorem setLIntegral_ofReal_id_Ioo {R : ℝ} (hR : 0 < R) :
    ∫⁻ ρ in Ioo R (2 * R), ENNReal.ofReal ρ = ENNReal.ofReal (3 * R ^ 2 / 2) := by
  have hint : IntegrableOn (fun ρ : ℝ => ρ) (Ioo R (2 * R)) :=
    (continuous_id.integrableOn_Icc (a := R) (b := 2 * R)).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioo).mono fun ρ hρ => (hR.trans hρ.1).le),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith), integral_id]
  congr 1
  ring

/-- **Step 2.** The averaged pointwise bound. -/
theorem local_pointwise_bound {D : Set ℂ} (hDm : MeasurableSet D) {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) {z : ℂ} (hz : z ∈ Hbar) {R : ℝ} (hR : 0 < R)
    (hsub : ∀ y ∈ H, ‖y - z‖ < 2 * R → y ∈ D) :
    ENNReal.ofReal (3 * R ^ 2 / 2) * ENNReal.ofReal |f z| ≤
      ENNReal.ofReal (2 * π)⁻¹ * (2 * ∫⁻ y in D, ‖f y‖ₑ) +
      ENNReal.ofReal (3 * R ^ 2 / 2) *
        (ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) := by
  set Q := ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))
    with hQ
  set c := ENNReal.ofReal (2 * π)⁻¹ with hc
  set g : ℂ → ℝ≥0∞ := fun y => ‖f (foldH y)‖ₑ with hgdef
  have hgc : Continuous (f ∘ foldH) := hf.continuous.comp continuous_foldH_K3
  have hgm : Measurable g := (continuous_enorm.comp hgc).measurable
  set A : ℝ → ℝ≥0∞ := fun ρ => c * ∫⁻ θ in Ioo (-π) π, g (circleMap z ρ θ) with hAdef
  have hA : ∀ ρ ∈ Ioo R (2 * R), ENNReal.ofReal |f z| ≤ A ρ + Q := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hR.trans hρ.1
    have h1 : ENNReal.ofReal |f z| ≤ ENNReal.ofReal |∫ x, f x ∂(foldedCircle z ρ)| +
        ENNReal.ofReal |f z - ∫ x, f x ∂(foldedCircle z ρ)| := by
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := abs_sub_abs_le_abs_sub (f z) (∫ x, f x ∂(foldedCircle z ρ))
      linarith
    have h2 : ENNReal.ofReal |∫ x, f x ∂(foldedCircle z ρ)| ≤ A ρ := by
      rw [integral_foldedCircle_eq hf.continuous, integral_circleUnif_eq hgc, ← Real.norm_eq_abs,
        ofReal_norm, enorm_mul, hAdef]
      refine mul_le_mul' ?_ ?_
      · rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by positivity)]
      · exact enorm_integral_le_lintegral_enorm _
    exact h1.trans (add_le_add h2 (ofReal_abs_sub_foldedCircle_le hf hz hρ0 hρ.2.le))
  have hAm : Measurable A := by
    refine Measurable.const_mul ?_ c
    exact Measurable.lintegral_prod_right'
      (f := fun p : ℝ × ℝ => g (circleMap z p.1 p.2))
      (hgm.comp (continuous_circleMap_uncurry z).measurable)
  calc ENNReal.ofReal (3 * R ^ 2 / 2) * ENNReal.ofReal |f z|
      = ∫⁻ ρ in Ioo R (2 * R), ENNReal.ofReal ρ * ENNReal.ofReal |f z| := by
        rw [lintegral_mul_const _ ENNReal.measurable_ofReal, setLIntegral_ofReal_id_Ioo hR]
    _ ≤ ∫⁻ ρ in Ioo R (2 * R), ENNReal.ofReal ρ * (A ρ + Q) := by
        refine lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioo).mono fun ρ hρ => ?_)
        exact mul_le_mul_right (hA ρ hρ) _
    _ = (∫⁻ ρ in Ioo R (2 * R), ENNReal.ofReal ρ * A ρ) +
          ∫⁻ ρ in Ioo R (2 * R), ENNReal.ofReal ρ * Q := by
        simp_rw [mul_add]
        exact lintegral_add_right _ (ENNReal.measurable_ofReal.mul_const Q)
    _ ≤ c * (2 * ∫⁻ y in D, ‖f y‖ₑ) + ENNReal.ofReal (3 * R ^ 2 / 2) * Q := by
        apply add_le_add
        · have e : ∀ ρ, ENNReal.ofReal ρ * A ρ =
              c * ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap z ρ θ) := by
            intro ρ
            rw [hAdef, mul_left_comm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp_rw [e]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine mul_le_mul_right ?_ c
          exact (lintegral_radius_circle_le hgm z hR.le).trans
            (lintegral_ball_foldH_le hDm hz hsub (continuous_enorm.comp hf.continuous).measurable)
        · rw [lintegral_mul_const _ ENNReal.measurable_ofReal, setLIntegral_ofReal_id_Ioo hR,
            mul_comm]

/-! ## Step 3: the kernel bound -/

/-- `h_δ(u) = ‖u‖⁻¹ min(‖u‖⁻¹, 2/δ) 1{‖u‖ < ρ}`. -/
def kMin (ρ δ : ℝ) (u : ℂ) : ℝ≥0∞ :=
  if ‖u‖ < ρ then ENNReal.ofReal (‖u‖⁻¹ * min ‖u‖⁻¹ (2 / δ)) else 0

theorem measurable_kMin (ρ δ : ℝ) : Measurable (kMin ρ δ) := by
  unfold kMin
  exact Measurable.ite (measurableSet_lt measurable_norm measurable_const)
    (ENNReal.measurable_ofReal.comp (measurable_norm.inv.mul
      (measurable_norm.inv.min measurable_const))) measurable_const

theorem inv_le_min_of_le {x y δ : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hδ : 0 < δ) (hy : δ / 2 ≤ y) :
    y⁻¹ ≤ min x⁻¹ (2 / δ) := by
  refine le_min (inv_anti₀ hx hxy) ?_
  have := inv_anti₀ (by positivity : 0 < δ / 2) hy
  rwa [inv_div] at this

theorem kInv_mul_kInv_le {a b : ℂ} (hab : a ≠ b) (ρ : ℝ) (y : ℂ) :
    kInv ρ (y - a) * kInv ρ (y - b) ≤ kMin ρ ‖a - b‖ (y - a) + kMin ρ ‖a - b‖ (y - b) := by
  have hδ : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have htri : ‖a - b‖ ≤ ‖y - a‖ + ‖y - b‖ := by
    calc ‖a - b‖ = ‖(y - b) - (y - a)‖ := by congr 1; ring
      _ ≤ ‖y - b‖ + ‖y - a‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  unfold kInv kMin
  by_cases ha : ‖y - a‖ < ρ
  · by_cases hb : ‖y - b‖ < ρ
    · simp only [ha, hb, ↓reduceIte]
      rcases eq_or_lt_of_le (norm_nonneg (y - a)) with h0 | hapos
      · rw [← h0, inv_zero, ENNReal.ofReal_zero, zero_mul]; exact zero_le
      rcases eq_or_lt_of_le (norm_nonneg (y - b)) with h0 | hbpos
      · rw [← h0, inv_zero, ENNReal.ofReal_zero, mul_zero]; exact zero_le
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
      rcases le_total ‖y - a‖ ‖y - b‖ with h | h
      · refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_self_add
        exact mul_le_mul_of_nonneg_left (inv_le_min_of_le hapos h hδ (by linarith))
          (inv_nonneg.mpr (norm_nonneg _))
      · refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_add_self
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (inv_le_min_of_le hbpos h hδ (by linarith))
          (inv_nonneg.mpr (norm_nonneg _))
    · simp only [hb, ↓reduceIte, mul_zero]; exact zero_le
  · simp only [ha, ↓reduceIte, zero_mul]; exact zero_le

theorem lintegral_kMin_le {ρ δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ u, kMin ρ δ u ≤
      ENNReal.ofReal (2 * π) * (1 + ENNReal.ofReal (Real.log (max (2 * ρ / δ) 1))) := by
  rw [lintegral_eq_polar (measurable_kMin ρ δ)]
  set J : ℝ → ℝ≥0∞ := fun t => if t < ρ then ENNReal.ofReal (min t⁻¹ (2 / δ)) else 0 with hJ
  have e : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal t * kMin ρ δ (circleMap 0 t θ) =
      ENNReal.ofReal (2 * π) * J t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hk : ∀ θ, ENNReal.ofReal t * kMin ρ δ (circleMap 0 t θ) = J t := by
      intro θ
      simp only [kMin, hJ, norm_circleMap_zero, abs_of_pos ht0]
      split_ifs
      · rw [← ENNReal.ofReal_mul ht0.le, ← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul]
      · rw [mul_zero]
    simp_rw [hk]
    rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
    congr 2
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul_right ?_ _
  set ρ' := max ρ (δ / 2) with hρ'
  have hδ2 : 0 < δ / 2 := by positivity
  have hρ'2 : δ / 2 ≤ ρ' := le_max_right _ _
  have hJle : ∀ t ∈ Ioi (0 : ℝ), J t ≤
      (Ioc 0 (δ / 2)).indicator (fun _ => ENNReal.ofReal (2 / δ)) t +
      (Ioo (δ / 2) ρ').indicator (fun t => ENNReal.ofReal t⁻¹) t := by
    intro t ht
    have ht0 : 0 < t := ht
    simp only [hJ]
    split_ifs with htρ
    · rcases le_or_gt t (δ / 2) with h | h
      · rw [indicator_of_mem (show t ∈ Ioc 0 (δ / 2) from ⟨ht0, h⟩)]
        exact le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) le_self_add
      · rw [indicator_of_mem (show t ∈ Ioo (δ / 2) ρ' from ⟨h, lt_max_of_lt_left htρ⟩)]
        exact le_trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)) le_add_self
    · exact zero_le
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Ioo (δ / 2) ρ') :=
    (ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono fun t ht =>
      (hδ2.trans_le ht.1).ne')).mono_set Ioo_subset_Icc_self
  have hlog : ∫⁻ t in Ioo (δ / 2) ρ', ENNReal.ofReal t⁻¹ =
      ENNReal.ofReal (Real.log (max (2 * ρ / δ) 1)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => (inv_pos.mpr (hδ2.trans ht.1)).le),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ'2,
      integral_inv_of_pos hδ2 (hδ2.trans_le hρ'2)]
    congr 2
    rw [hρ', ← max_div_div_right hδ2.le, div_self hδ2.ne']
    congr 1
    field_simp
  calc ∫⁻ t in Ioi 0, J t
      ≤ ∫⁻ t in Ioi 0, ((Ioc 0 (δ / 2)).indicator (fun _ => ENNReal.ofReal (2 / δ)) t +
        (Ioo (δ / 2) ρ').indicator (fun t => ENNReal.ofReal t⁻¹) t) :=
        setLIntegral_mono' measurableSet_Ioi hJle
    _ ≤ ∫⁻ t, ((Ioc 0 (δ / 2)).indicator (fun _ => ENNReal.ofReal (2 / δ)) t +
        (Ioo (δ / 2) ρ').indicator (fun t => ENNReal.ofReal t⁻¹) t) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (2 / δ) * volume (Ioc (0 : ℝ) (δ / 2)) +
        (∫⁻ t in Ioo (δ / 2) ρ', ENNReal.ofReal t⁻¹) := by
        rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioc),
          lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioo,
          setLIntegral_const]
    _ = 1 + ENNReal.ofReal (Real.log (max (2 * ρ / δ) 1)) := by
        rw [hlog, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
          show 2 / δ * (δ / 2) = 1 by field_simp, ENNReal.ofReal_one]

theorem log_max_div_le {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    Real.log (max (2 * ρ / δ) 1) ≤ max (Real.log (2 * ρ)) 0 + max 0 (-Real.log δ) := by
  rcases le_total (2 * ρ / δ) 1 with h | h
  · rw [max_eq_right h, Real.log_one]
    exact add_nonneg (le_max_right _ _) (le_max_left _ _)
  · rw [max_eq_left h, Real.log_div (by positivity) hδ.ne']
    linarith [le_max_left (Real.log (2 * ρ)) 0, le_max_right 0 (-Real.log δ)]

/-- **Step 3.** `∫ k_ρ(y−a) k_ρ(y−b) dy ≤ A₀ + A₁ log⁻ ‖a − b‖`. -/
theorem lintegral_kInv_mul_kInv_le {a b : ℂ} (hab : a ≠ b) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ y, kInv ρ (y - a) * kInv ρ (y - b) ≤
      2 * ENNReal.ofReal (2 * π) * (1 + ENNReal.ofReal (max (Real.log (2 * ρ)) 0)) +
        2 * ENNReal.ofReal (2 * π) * ENNReal.ofReal (-Real.log ‖a - b‖) := by
  have hδ : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hlog : ENNReal.ofReal (Real.log (max (2 * ρ / ‖a - b‖) 1)) ≤
      ENNReal.ofReal (max (Real.log (2 * ρ)) 0) + ENNReal.ofReal (-Real.log ‖a - b‖) := by
    rw [← admissible_ofReal_max_zero (-Real.log ‖a - b‖)]
    exact (ENNReal.ofReal_le_ofReal (log_max_div_le hρ hδ)).trans ENNReal.ofReal_add_le
  calc ∫⁻ y, kInv ρ (y - a) * kInv ρ (y - b)
      ≤ ∫⁻ y, (kMin ρ ‖a - b‖ (y - a) + kMin ρ ‖a - b‖ (y - b)) :=
        lintegral_mono (kInv_mul_kInv_le hab ρ)
    _ = 2 * ∫⁻ u, kMin ρ ‖a - b‖ u := by
        have hma : Measurable fun y : ℂ => kMin ρ ‖a - b‖ (y - a) :=
          (measurable_kMin _ _).comp (measurable_id.sub_const a)
        rw [lintegral_add_left hma,
          lintegral_sub_right_eq_self (kMin ρ ‖a - b‖) a,
          lintegral_sub_right_eq_self (kMin ρ ‖a - b‖) b, two_mul]
    _ ≤ 2 * (ENNReal.ofReal (2 * π) * (1 + ENNReal.ofReal (Real.log (max (2 * ρ / ‖a - b‖) 1)))) :=
        mul_le_mul_right (lintegral_kMin_le hδ) 2
    _ ≤ 2 * (ENNReal.ofReal (2 * π) * (1 + (ENNReal.ofReal (max (Real.log (2 * ρ)) 0) +
          ENNReal.ofReal (-Real.log ‖a - b‖)))) :=
        mul_le_mul_right (mul_le_mul_right (add_le_add_right hlog 1) _) 2
    _ = _ := by ring

/-- **Step 3′.** The potential `P(y) = ∫ k_ρ(y − z) dμ(z)` of an admissible measure is in `L²`. -/
theorem lintegral_kInvPot_sq_lt_top {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {ρ : ℝ}
    (hρ : 0 < ρ) : ∫⁻ y, (∫⁻ z, kInv ρ (y - z) ∂μ) ^ (2 : ℝ) < ⊤ := by
  obtain ⟨hμf, -, C, hC, hbd⟩ := id hμ
  have := hμf
  have hatom := noAtoms_of_isAdmissibleH hμ
  set A0 := 2 * ENNReal.ofReal (2 * π) * (1 + ENNReal.ofReal (max (Real.log (2 * ρ)) 0)) with hA0
  set A1 := 2 * ENNReal.ofReal (2 * π) with hA1
  have hk2 : Measurable fun p : ℂ × ℂ => kInv ρ (p.1 - p.2) :=
    (measurable_kInv ρ).comp (measurable_fst.sub measurable_snd)
  have hF : Measurable fun p : (ℂ × ℂ) × ℂ => kInv ρ (p.1.1 - p.1.2) * kInv ρ (p.1.1 - p.2) :=
    (hk2.comp measurable_fst).mul (hk2.comp (measurable_fst.fst.prodMk measurable_snd))
  have step1 : ∀ y, (∫⁻ z, kInv ρ (y - z) ∂μ) ^ (2 : ℝ) =
      ∫⁻ z, (∫⁻ z', kInv ρ (y - z) * kInv ρ (y - z') ∂μ) ∂μ := by
    intro y
    have hm : Measurable fun z => kInv ρ (y - z) :=
      (measurable_kInv ρ).comp (measurable_const.sub measurable_id)
    rw [ENNReal.rpow_two, sq, lintegral_lintegral_mul hm.aemeasurable hm.aemeasurable]
  simp_rw [step1]
  have hm1 : Measurable fun q : ℂ × ℂ => ∫⁻ z', kInv ρ (q.1 - q.2) * kInv ρ (q.1 - z') ∂μ :=
    Measurable.lintegral_prod_right' (ν := μ) hF
  rw [lintegral_lintegral_swap (μ := volume) (ν := μ) hm1.aemeasurable]
  have step2 : ∀ z, ∫⁻ y, (∫⁻ z', kInv ρ (y - z) * kInv ρ (y - z') ∂μ) =
      ∫⁻ z', (∫⁻ y, kInv ρ (y - z) * kInv ρ (y - z')) ∂μ := by
    intro z
    refine lintegral_lintegral_swap ?_
    exact ((hk2.comp (measurable_fst.prodMk measurable_const)).mul hk2).aemeasurable
  simp_rw [step2]
  have hK : ∀ z, ∫⁻ z', (∫⁻ y, kInv ρ (y - z) * kInv ρ (y - z')) ∂μ ≤
      A0 * μ univ + A1 * C := by
    intro z
    calc ∫⁻ z', (∫⁻ y, kInv ρ (y - z) * kInv ρ (y - z')) ∂μ
        ≤ ∫⁻ z', (A0 + A1 * ENNReal.ofReal (-Real.log ‖z' - z‖)) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hatom z)] with z' hz'
          have hne : z ≠ z' := fun h => hz' (by rw [h]; rfl)
          have h := lintegral_kInv_mul_kInv_le hne hρ
          rwa [norm_sub_rev z z'] at h
      _ = A0 * μ univ + A1 * ∫⁻ z', ENNReal.ofReal (-Real.log ‖z' - z‖) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_const_mul _ (admissible_measurable_logNeg_sub z)]
      _ ≤ A0 * μ univ + A1 * C := add_le_add_right (mul_le_mul_right (hbd z) _) _
  calc ∫⁻ z, (∫⁻ z', (∫⁻ y, kInv ρ (y - z) * kInv ρ (y - z')) ∂μ) ∂μ
      ≤ ∫⁻ _z, (A0 * μ univ + A1 * C) ∂μ := lintegral_mono hK
    _ = (A0 * μ univ + A1 * C) * μ univ := lintegral_const _
    _ < ⊤ := by
        have h1 : A0 ≠ ⊤ := by rw [hA0]; finiteness
        have h2 : A1 ≠ ⊤ := by rw [hA1]; finiteness
        have h3 : μ univ ≠ ⊤ := measure_ne_top μ _
        have h4 : C ≠ ⊤ := hC.ne
        finiteness

/-! ## Step 4: assembly -/

/-- **M4, quantitative form.** `(∫ f dμ)² ≤ M ∫_D ‖∇f‖²` on the mixed space. -/
theorem mixed_local_energy_bound {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {K : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hKloc : ∀ z ∈ K, LocalBall D S z (2 * R)) {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hμK : μ Kᶜ = 0) :
    ∃ M : ℝ, ∀ f ∈ mixedSpace D S, (∫ x, f x ∂μ) ^ 2 ≤ M * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 := by
  obtain ⟨CP, hCP⟩ := mixed_poincare hD hDH hb hS
  have hμf := hμ.1
  have hKae : ∀ᵐ z ∂μ, z ∈ K := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμK] with z hz
    exact Set.notMem_compl_iff.mp hz
  set a : ℝ≥0∞ := ENNReal.ofReal (3 * R ^ 2 / 2) with ha
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * π)⁻¹ with hc
  set P : ℂ → ℝ≥0∞ := fun y => ∫⁻ z, kInv (2 * R) (y - z) ∂μ with hPdef
  have hPm : Measurable P :=
    Measurable.lintegral_prod_right' (ν := μ)
      ((measurable_kInv (2 * R)).comp (measurable_fst.sub measurable_snd))
  set PP : ℝ≥0∞ := ∫⁻ y, P y ^ (2 : ℝ) with hPP
  have hPP_lt : PP < ⊤ := lintegral_kInvPot_sq_lt_top hμ (by linarith)
  set VD : ℝ≥0∞ := volume D with hVD
  have hVD_lt : VD < ⊤ := hb.measure_lt_top
  set B : ℝ≥0∞ := c * 2 * μ univ * (VD ^ (1 / 2 : ℝ) * ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ)) +
    a * (c * 2 * PP ^ (1 / 2 : ℝ)) with hB
  have hB_ne : B ≠ ⊤ := by
    have h1 : VD ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVD_lt.ne
    have h2 : ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have h3 : PP ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPP_lt.ne
    have h4 : μ univ ≠ ⊤ := measure_ne_top μ _
    have h5 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h5) h4) (ENNReal.mul_ne_top h1 h2),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h5) h3)⟩
  have ha0 : 0 < 3 * R ^ 2 / 2 := by positivity
  refine ⟨(B.toReal / (3 * R ^ 2 / 2)) ^ 2, fun f hf => ?_⟩
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le one_le_smooth
  have hfc : Continuous f := hf1.continuous
  have hdc : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  set G : ℝ := ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg hD.measurableSet fun _ _ => sq_nonneg _
  have hGint : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D := hf.2.1
  set Y : ℝ≥0∞ := ENNReal.ofReal G ^ (1 / 2 : ℝ) with hY
  -- (a) the energy as a lintegral
  have hEn : ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal G := by
    rw [hG, ofReal_integral_eq_lintegral_ofReal hGint
      (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  -- (b) Poincaré
  have hfsq : IntegrableOn (fun z => f z ^ 2) D :=
    ((hfc.pow 2).continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have hL2 : ∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (max CP 0) * ENNReal.ofReal G := by
    have e : ∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∫ z in D, f z ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hfsq (Eventually.of_forall fun _ => sq_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
        Real.rpow_two, sq_abs]
    rw [e, ← ENNReal.ofReal_mul (le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal
      ((hCP f hf).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hG0))
  -- (c) the `L¹` term
  set L1 := ∫⁻ y in D, ‖f y‖ₑ with hL1def
  have hL1 : L1 ≤ VD ^ (1 / 2 : ℝ) * (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) * Y) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict D) Real.HolderConjugate.two_two
      (f := fun _ => (1 : ℝ≥0∞)) (g := fun y => ‖f y‖ₑ) aemeasurable_const
      hfc.enorm.measurable.aemeasurable
    simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const,
      Measure.restrict_apply_univ] at h
    refine h.trans (mul_le_mul_right ?_ _)
    calc (∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (max CP 0) * ENNReal.ofReal G) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hL2 (by norm_num)
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  -- (d) the pointwise bound, integrated
  have hint1 : a * ∫⁻ z, ENNReal.ofReal |f z| ∂μ ≤ c * (2 * L1) * μ univ +
      a * (c * ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ) := by
    rw [← lintegral_const_mul' a (fun z => ENNReal.ofReal |f z|) ENNReal.ofReal_ne_top]
    calc ∫⁻ z, a * ENNReal.ofReal |f z| ∂μ
        ≤ ∫⁻ z, (c * (2 * L1) +
          a * (c * ∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)))) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hKae] with z hz
          exact local_pointwise_bound hD.measurableSet hf1 (hKloc z hz).1 hR
            (fun y hy hyz => (hKloc z hz).mem_of_mem_H hD hS hy hyz.le)
      _ = _ := by
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_const_mul' a _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  -- (e) Tonelli, and restriction to `D`
  have hswap : ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ ≤
      2 * ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ * P y := by
    have hm : Measurable fun p : ℂ × ℂ => ‖fderiv ℝ f p.2‖ₑ * (2 * kInv (2 * R) (p.2 - p.1)) :=
      (hdc.enorm.measurable.comp measurable_snd).mul
        (measurable_const.mul ((measurable_kInv _).comp (measurable_snd.sub measurable_fst)))
    have e : ∀ y, ∫⁻ z, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)) ∂μ =
        2 * (‖fderiv ℝ f y‖ₑ * P y) := by
      intro y
      calc ∫⁻ z, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)) ∂μ
          = ∫⁻ z, (‖fderiv ℝ f y‖ₑ * 2) * kInv (2 * R) (y - z) ∂μ := by simp_rw [mul_assoc]
        _ = (‖fderiv ℝ f y‖ₑ * 2) * P y :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top (by norm_num))
        _ = 2 * (‖fderiv ℝ f y‖ₑ * P y) := by ring
    rw [lintegral_lintegral_swap hm.aemeasurable, setLIntegral_congr_fun measurableSet_H_mx (fun y _ => e y),
      lintegral_const_mul' _ _ (by norm_num)]
    refine mul_le_mul_right ?_ 2
    rw [← lintegral_indicator measurableSet_H_mx, ← lintegral_indicator hD.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hyD : y ∈ D
    · rw [indicator_of_mem (hDH hyD), indicator_of_mem hyD]
    · rw [indicator_of_notMem hyD]
      by_cases hyH : y ∈ H
      · rw [indicator_of_mem hyH]
        have hP0 : P y = 0 := by
          rw [hPdef]
          refine (lintegral_congr_ae ?_).trans lintegral_zero
          filter_upwards [hKae] with z hz
          have hk : ¬ ‖y - z‖ < 2 * R := fun h =>
            hyD ((hKloc z hz).mem_of_mem_H hD hS hyH h.le)
          simp [kInv, hk]
        rw [hP0, mul_zero]
      · rw [indicator_of_notMem hyH]
  -- (f) Cauchy–Schwarz for the gradient term
  have hW : ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ * P y ≤ Y * PP ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict D) Real.HolderConjugate.two_two
      (f := fun y => ‖fderiv ℝ f y‖ₑ) (g := P) hdc.enorm.measurable.aemeasurable hPm.aemeasurable
    simp only [Pi.mul_apply] at h
    refine h.trans (mul_le_mul' (le_of_eq ?_)
      (ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by norm_num)))
    rw [hEn]
  -- (g) combination
  have hmain : a * ENNReal.ofReal |∫ x, f x ∂μ| ≤ Y * B := by
    have h0 : ENNReal.ofReal |∫ x, f x ∂μ| ≤ ∫⁻ z, ENNReal.ofReal |f z| ∂μ := by
      rw [← Real.enorm_eq_ofReal_abs]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp only [Real.enorm_eq_ofReal_abs]
    calc a * ENNReal.ofReal |∫ x, f x ∂μ| ≤ a * ∫⁻ z, ENNReal.ofReal |f z| ∂μ :=
          mul_le_mul_right h0 _
      _ ≤ c * (2 * L1) * μ univ +
          a * (c * ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ) := hint1
      _ ≤ c * (2 * (VD ^ (1 / 2 : ℝ) * (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) * Y))) * μ univ +
          a * (c * (2 * (Y * PP ^ (1 / 2 : ℝ)))) := by
          refine add_le_add (mul_le_mul_left (mul_le_mul_right (mul_le_mul_right hL1 2) c) _)
            (mul_le_mul_right (mul_le_mul_right (hswap.trans (mul_le_mul_right hW 2)) c) a)
      _ = Y * B := by rw [hB]; ring
  -- (h) back to real numbers
  have hYeq : Y = ENNReal.ofReal (Real.sqrt G) := by
    rw [hY, Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hG0 (by norm_num)]
  rw [hYeq, ha, ← ENNReal.ofReal_toReal hB_ne,
    ← ENNReal.ofReal_mul (p := 3 * R ^ 2 / 2) (q := |∫ x, f x ∂μ|) ha0.le,
    ← ENNReal.ofReal_mul (p := Real.sqrt G) (q := B.toReal) (Real.sqrt_nonneg _)] at hmain
  have hr := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)).mp hmain
  have hI : |∫ x, f x ∂μ| ≤ Real.sqrt G * (B.toReal / (3 * R ^ 2 / 2)) := by
    rw [← mul_div_assoc, le_div_iff₀ ha0]
    linarith
  calc (∫ x, f x ∂μ) ^ 2 = |∫ x, f x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt G * (B.toReal / (3 * R ^ 2 / 2))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hI 2
    _ = (B.toReal / (3 * R ^ 2 / 2)) ^ 2 * G := by rw [mul_pow, Real.sq_sqrt hG0]; ring

/-- **M4.** Local admissibility: an admissible measure carried by a set of points with uniform
local discs has finite dual norm on the mixed space. -/
theorem isAdmissibleDual_mixed_of_local {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {K : Set ℂ} (hK : IsCompact K)
    {R : ℝ} (hR : 0 < R) (hKloc : ∀ z ∈ K, LocalBall D S z (2 * R)) {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0) : IsAdmissibleDual D (mixedSpace D S) μ := by
  obtain ⟨M, hM⟩ := mixed_local_energy_bound hD hDH hb hS hR hKloc hμ hμK
  refine ⟨hμ.1, ⟨K, hK, fun z hz => (hKloc z hz).mem_closure, hμK⟩, ?_⟩
  unfold dualNormSq
  refine lt_of_le_of_lt (iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_)
    (ENNReal.ofReal_lt_top (r := M * (2 * π)))
  rw [div_le_iff₀ hf.2]
  have hE : dirichletEnergyOn D f = (2 * π)⁻¹ * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 := rfl
  have hπ : (2 * π) ≠ 0 := by positivity
  calc (∫ x, f x ∂μ) ^ 2 ≤ M * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 := hM f hf.1
    _ = M * (2 * π) * dirichletEnergyOn D f := by
        rw [hE, ← mul_assoc, mul_assoc M (2 * π) (2 * π)⁻¹, mul_inv_cancel₀ hπ, mul_one]

end QuantumZipper.K3

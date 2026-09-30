import QuantumZipper.Proofs.GFF.K3.Polar

/-!
# The annulus identity (GFF-K3 node M1)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M.

`annulus_identity`: for `f ∈ C¹(ℂ)`, `z ∈ ℂ` and `0 < s < s'`,
`(2π)⁻¹ ∫_H ⟪∇f, annulusField z s s'⟫ = ∫ f d(foldedCircle z s) − ∫ f d(foldedCircle z s')`.

Route: the `H`-integral of the two terms of `annulusField` is the `ℂ`-integral of the first
term against `∇(f ∘ foldH)` (reflection `x ↦ x̄` on the lower half-plane); then F1′ at the radii
`s` and `s'`. A smooth cutoff (equal to `1` on a large ball around `0`, which is invariant under
`foldH`) removes the compact-support hypothesis of F1′.

Source: the first-order representation formula of Adams–Hedberg, *Function Spaces and Potential
Theory*, eq. (1.2.4), p. 8, applied on annuli and reflected across `ℝ`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate

namespace QuantumZipper.K3

/-! ## Definitions -/

/-- One term of the annulus field: `−(x−c)/|x−c|²` on the open annulus `s < |x−c| < s'`. -/
def annulusTerm (c : ℂ) (s s' : ℝ) (x : ℂ) : ℂ :=
  if s < ‖x - c‖ ∧ ‖x - c‖ < s' then -(x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ) else 0

/-- The gradient of the annulus potential of `foldedCircle z s − foldedCircle z s'`. -/
def annulusField (z : ℂ) (s s' : ℝ) (x : ℂ) : ℂ :=
  (if s < ‖x - z‖ ∧ ‖x - z‖ < s' then -(x - z) / ((‖x - z‖ ^ 2 : ℝ) : ℂ) else 0) +
  (if s < ‖x - conj z‖ ∧ ‖x - conj z‖ < s' then
    -(x - conj z) / ((‖x - conj z‖ ^ 2 : ℝ) : ℂ) else 0)

theorem annulusField_eq (z : ℂ) (s s' : ℝ) (x : ℂ) :
    annulusField z s s' x = annulusTerm z s s' x + annulusTerm (conj z) s s' x := rfl

/-- The integrand of F1 for a general `ℂ →L[ℝ] ℝ`-valued field `G`. -/
def radialInt (G : ℂ → ℂ →L[ℝ] ℝ) (c : ℂ) (r : ℝ) (x : ℂ) : ℝ :=
  if r < ‖x - c‖ then G x ((x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ)) else 0

/-! ## Measurability and integrability -/

theorem measurableSet_H_mx : MeasurableSet H :=
  measurableSet_lt measurable_const Complex.measurable_im

theorem Hbar_ae_eq_H_mx : (Hbar : Set ℂ) =ᵐ[volume] H := by
  filter_upwards [ae_im_ne_zero] with z hz
  change (0 ≤ z.im) = (0 < z.im)
  exact propext ⟨fun h => lt_of_le_of_ne h (Ne.symm hz), le_of_lt⟩

theorem radial_vec_eq (x c : ℂ) :
    (x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ) = ((‖x - c‖ ^ 2)⁻¹ : ℝ) • (x - c) := by
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]

theorem measurable_radial_vec (c : ℂ) :
    Measurable fun x : ℂ => (x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [radial_vec_eq]
  exact (((measurable_id.sub_const c).norm.pow_const 2).inv).smul (measurable_id.sub_const c)

theorem norm_radial_vec (x c : ℂ) : ‖(x - c) / ((‖x - c‖ ^ 2 : ℝ) : ℂ)‖ = ‖x - c‖⁻¹ := by
  rw [radial_vec_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases eq_or_ne ‖x - c‖ 0 with h | h
  · simp [h]
  · rw [sq, mul_inv, mul_assoc, inv_mul_cancel₀ h, mul_one]

theorem measurable_radialInt {G : ℂ → ℂ →L[ℝ] ℝ} (hG : Measurable G) (c : ℂ) (r : ℝ) :
    Measurable (radialInt G c r) := by
  unfold radialInt
  refine Measurable.ite (measurableSet_lt measurable_const (measurable_id.sub_const c).norm) ?_
    measurable_const
  exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := ℂ) (F := ℝ)).continuous.measurable.comp
    (hG.prodMk (measurable_radial_vec c))

theorem integrable_radialInt {G : ℂ → ℂ →L[ℝ] ℝ} (hG : Measurable G) {C : ℝ}
    (hC : ∀ x, ‖G x‖ ≤ C) {c : ℂ} {M : ℝ} (hM : ∀ x, M < ‖x - c‖ → G x = 0) {r : ℝ}
    (hr : 0 < r) : Integrable (radialInt G c r) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hon : IntegrableOn (radialInt G c r) (closedBall c M) := by
    refine Measure.integrableOn_of_bounded (M := C * r⁻¹) measure_closedBall_lt_top.ne
      (measurable_radialInt hG c r).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    unfold radialInt
    split_ifs with h
    · refine ((G x).le_opNorm _).trans ?_
      rw [norm_radial_vec]
      exact mul_le_mul (hC x) (inv_anti₀ hr h.le) (inv_nonneg.mpr (norm_nonneg _)) hC0
    · rw [norm_zero]; exact mul_nonneg hC0 (inv_nonneg.mpr hr.le)
  refine hon.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  have : M < ‖x - c‖ := by simpa [mem_closedBall, dist_eq_norm] using hx
  simp [radialInt, hM x this]

/-! ## The folded derivative -/

theorem measurable_foldDeriv {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) : Measurable (foldDeriv f) := by
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  unfold foldDeriv
  refine Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im)
    hdc.measurable ?_
  exact ((hdc.comp Complex.continuous_conj).clm_comp continuous_const).measurable

theorem norm_foldDeriv_le {f : ℂ → ℝ} {C : ℝ} (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (x : ℂ) :
    ‖foldDeriv f x‖ ≤ C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold foldDeriv
  split_ifs
  · exact hC x
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by simp
    calc ‖fderiv ℝ f ((starRingEnd ℂ) x)‖ * ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖
        ≤ C * 1 := mul_le_mul (hC _) h1 (norm_nonneg _) hC0
      _ = C := mul_one C

theorem foldDeriv_of_pos {f : ℂ → ℝ} {x : ℂ} (hx : 0 < x.im) : foldDeriv f x = fderiv ℝ f x := by
  simp [foldDeriv, hx]

theorem foldDeriv_conj_of_pos {f : ℂ → ℝ} {y : ℂ} (hy : 0 < y.im) (v : ℂ) :
    foldDeriv f (conj y) v = fderiv ℝ f y (conj v) := by
  have h : ¬ 0 < (conj y).im := by rw [Complex.conj_im]; linarith
  simp only [foldDeriv, h, ↓reduceIte, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, Complex.conj_conj]

theorem conj_annulusTerm (z : ℂ) (s s' : ℝ) (y : ℂ) :
    conj (annulusTerm z s s' (conj y)) = annulusTerm (conj z) s s' y := by
  have hn : ‖conj y - z‖ = ‖y - conj z‖ := by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
  unfold annulusTerm
  rw [hn]
  split_ifs
  · rw [map_div₀, map_neg, map_sub, Complex.conj_conj, Complex.conj_ofReal]
  · simp

/-! ## M1 for compactly supported `f` -/

theorem annulus_identity_of_hasCompactSupport {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (z : ℂ) {s s' : ℝ} (hs : 0 < s) (hss' : s < s') :
    (2 * Real.pi)⁻¹ * ∫ x in H, fderiv ℝ f x (annulusField z s s' x) =
      ∫ x, f x ∂(foldedCircle z s) - ∫ x, f x ∂(foldedCircle z s') := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hdc
  obtain ⟨M0, hM0⟩ := exists_radius_of_hasCompactSupport hc 0
  have hfz : ∀ y : ℂ, M0 < ‖y‖ → fderiv ℝ f y = 0 := fun y hy =>
    Function.notMem_support.mp fun h => hM0 y (by simpa using hy) (support_fderiv_subset ℝ h)
  set G := foldDeriv f with hGdef
  have hGm : Measurable G := measurable_foldDeriv hf
  have hGb : ∀ x, ‖G x‖ ≤ C := norm_foldDeriv_le hC
  have hGz : ∀ x, M0 + ‖z‖ < ‖x - z‖ → G x = 0 := by
    intro x hx
    have h1 : M0 < ‖x‖ := by linarith [norm_sub_le x z]
    simp only [hGdef, foldDeriv]
    split_ifs
    · exact hfz x h1
    · rw [hfz _ (by rwa [Complex.norm_conj])]; rfl
  -- F1′ in terms of `G`.
  have hF1 : ∀ r : ℝ, 0 ≤ r →
      ∫ x, radialInt G z r x = -(2 * π) * ∫ w, f w ∂(foldedCircle z r) := by
    intro r hr
    have h := integral_fderiv_radial_eq_circle_foldH hf hc z hr
    rw [foldedCircle, integral_map measurable_foldH.aemeasurable
      (hf.continuous.aestronglyMeasurable),
      show (∫ x, f (foldH x) ∂circleUnif z r) = ∫ w, (f ∘ foldH) w ∂circleUnif z r from rfl, ← h]
    refine integral_congr_ae ?_
    filter_upwards [ae_im_ne_zero] with x hx
    simp only [radialInt, hGdef, (hasFDerivAt_comp_foldH hfd hx).fderiv]
  -- The first annulus term against `G`.
  set φ : ℂ → ℝ := fun x => G x (annulusTerm z s s' x) with hφdef
  have hsph : volume (sphere z s') = 0 := Measure.addHaar_sphere volume z s'
  have hφae : φ =ᵐ[volume] fun x => -(radialInt G z s x - radialInt G z s' x) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hsph] with x hx
    have hne : ‖x - z‖ ≠ s' := by simpa [mem_sphere, dist_eq_norm] using hx
    simp only [hφdef]
    rcases le_or_gt ‖x - z‖ s with h1 | h1
    · have h1' : ¬ s < ‖x - z‖ := not_lt.mpr h1
      have h2' : ¬ s' < ‖x - z‖ := not_lt.mpr (h1.trans hss'.le)
      simp only [annulusTerm, radialInt, h1', h2', false_and, ↓reduceIte, map_zero, sub_self,
        neg_zero]
    · rcases lt_or_gt_of_ne hne with h2 | h2
      · have h2' : ¬ s' < ‖x - z‖ := not_lt.mpr h2.le
        simp only [annulusTerm, radialInt, h1, h2, h2', and_self, ↓reduceIte]
        rw [neg_div, map_neg, sub_zero]
      · have h2' : ¬ ‖x - z‖ < s' := not_lt.mpr h2.le
        simp only [annulusTerm, radialInt, h1, h2, h2', and_false, ↓reduceIte, map_zero,
          sub_self, neg_zero]
  have ii : ∀ r, 0 < r → Integrable (radialInt G z r) := fun r hr =>
    integrable_radialInt hGm hGb hGz hr
  have hφi : Integrable φ :=
    (((ii s hs).sub (ii s' (hs.trans hss'))).neg).congr hφae.symm
  have hφint : ∫ x, φ x = 2 * π * (∫ w, f w ∂(foldedCircle z s) -
      ∫ w, f w ∂(foldedCircle z s')) := by
    rw [integral_congr_ae hφae, integral_neg, integral_sub (ii s hs) (ii s' (hs.trans hss')),
      hF1 s hs.le, hF1 s' (hs.trans hss').le]
    ring
  -- Reflection: `∫_ℂ φ = ∫_H ⟪∇f, annulusField⟫`.
  have hmp : MeasurePreserving (Complex.conjLIE : ℂ → ℂ) volume volume :=
    Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (Complex.conjLIE : ℂ → ℂ) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hpre : (Complex.conjLIE : ℂ → ℂ) ⁻¹' Hᶜ = Hbar := by
    ext y
    simp only [Set.mem_preimage, Set.mem_compl_iff, Complex.conjLIE_apply]
    change ¬ (0 < (conj y).im) ↔ 0 ≤ y.im
    rw [Complex.conj_im, not_lt, neg_nonpos]
  have hlow : ∫ x in Hᶜ, φ x = ∫ y in H, φ (conj y) := by
    rw [← hmp.setIntegral_preimage_emb hemb φ Hᶜ, hpre, setIntegral_congr_set Hbar_ae_eq_H_mx]
    rfl
  have hφci : Integrable (fun y => φ (conj y)) :=
    (hmp.integrable_comp_emb hemb).mpr hφi
  have hsum : ∫ x, φ x = ∫ x in H, fderiv ℝ f x (annulusField z s s' x) := by
    rw [← integral_add_compl measurableSet_H_mx hφi, hlow,
      ← integral_add hφi.integrableOn hφci.integrableOn]
    refine setIntegral_congr_fun measurableSet_H_mx fun y hy => ?_
    have hy' : 0 < y.im := hy
    simp only [hφdef, hGdef, foldDeriv_of_pos hy', foldDeriv_conj_of_pos hy', conj_annulusTerm,
      annulusField_eq, map_add]
  rw [← hsum, hφint]
  field_simp

/-! ## M1 -/

/-- **M1.** The annulus identity. -/
theorem annulus_identity {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {z : ℂ} (_hz : z ∈ Hbar)
    {s s' : ℝ} (hs : 0 < s) (hss' : s < s') :
    (2 * Real.pi)⁻¹ * ∫ x in H, fderiv ℝ f x (annulusField z s s' x) =
      ∫ x, f x ∂(foldedCircle z s) - ∫ x, f x ∂(foldedCircle z s') := by
  set R : ℝ := ‖z‖ + s' + 1 with hRdef
  have hR0 : 0 < R := by rw [hRdef]; linarith [norm_nonneg z]
  let χ : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR0, by linarith⟩
  set F : ℂ → ℝ := fun x => χ x * f x with hFdef
  have hFd : ContDiff ℝ 1 F := (χ.contDiff (n := 1)).mul hf
  have hFc : HasCompactSupport F := χ.hasCompactSupport.mul_right
  have hball : ∀ x : ℂ, ‖x‖ < R → F =ᶠ[𝓝 x] f := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball (0 : ℂ) R by simpa using hx)] with y hy
    have : χ y = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hy)
    simp [hFdef, this]
  have key := annulus_identity_of_hasCompactSupport hFd hFc z hs hss'
  -- the left sides agree
  have hL : ∫ x in H, fderiv ℝ F x (annulusField z s s' x) =
      ∫ x in H, fderiv ℝ f x (annulusField z s s' x) := by
    refine setIntegral_congr_fun measurableSet_H_mx fun x _ => ?_
    by_cases hx : ‖x‖ < R
    · rw [(hball x hx).fderiv_eq]
    · have h1 : ¬ ‖x - z‖ < s' := fun h => hx (by linarith [norm_le_insert' x z])
      have h2 : ¬ ‖x - conj z‖ < s' := fun h => hx (by
        linarith [norm_le_insert' x (conj z), Complex.norm_conj z])
      simp [annulusField, h1, h2]
  -- the right sides agree
  have hcirc : ∀ r : ℝ, 0 ≤ r → r ≤ s' →
      ∫ x, F x ∂(foldedCircle z r) = ∫ x, f x ∂(foldedCircle z r) := by
    intro r hr hrs
    rw [foldedCircle, integral_map measurable_foldH.aemeasurable hFd.continuous.aestronglyMeasurable,
      integral_map measurable_foldH.aemeasurable hf.continuous.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [CircleMV.ae_circleUnif z r] with w hw
    have : ‖foldH w‖ < R := by
      rw [norm_foldH_K3]
      rw [abs_of_nonneg hr] at hw
      linarith [norm_le_insert' w z]
    exact (hball _ this).eq_of_nhds
  rw [← hL, key, hcirc s hs.le hss'.le, hcirc s' (hs.trans hss').le le_rfl]

end QuantumZipper.K3

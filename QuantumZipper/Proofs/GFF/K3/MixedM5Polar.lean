import QuantumZipper.Proofs.GFF.K3.MixedM5Rep

/-!
# Radially smoothed folded circles (GFF-K3 node M5(c), preparation)

For a continuous radial weight `φ` supported in `[a, b]` (`0 < a`) and `ψ(y) := φ(|y|)/|y|`:

* `integral_radial_circle_eq`: `∫_{t>0} φ(t) ∫_{-π}^{π} F(z + t e^{iθ}) dθ dt = ∫ F(y) ψ(y − z) dy`
  (polar coordinates, `Complex.integral_comp_polarCoord_symm`, and Fubini);
* `integral_radial_foldedCircle_eq`: the same for folded circles,
  `∫_{t>0} φ(t) ∫ f d(fold_{z,t}) dt = (2π)⁻¹ ∫ f(foldH y) ψ(y − z) dy`;
* `ofReal_abs_integral_foldH_sub_le`: if `ψ` is `L`-Lipschitz and vanishes off `B(0,b)`, the
  difference of the smoothed averages at `z, z'` is at most `L|z − z'| · 4 ∫_D |f|`;
* `lintegral_enorm_le_of_poincare`: `∫_D |f| ≤ |D|^{1/2} (C_P ∫_D |∇f|²)^{1/2}`.

Own elementary arguments (cost rule); the polar-coordinate computation follows
`polar_green_core` (`Polar.lean`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- Polar coordinates with a radial weight. -/
theorem integral_radial_circle_eq {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a)
    (hφa : ∀ t, t ≤ a → φ t = 0) (hφb : ∀ t, b ≤ t → φ t = 0) {F : ℂ → ℝ} (hF : Continuous F)
    (z : ℂ) :
    IntegrableOn (fun t => φ t * ∫ θ in Ioo (-π) π, F (circleMap z t θ)) (Ioi 0) ∧
      ∫ t in Ioi 0, φ t * ∫ θ in Ioo (-π) π, F (circleMap z t θ) =
        ∫ y, F y * (φ ‖y - z‖ / ‖y - z‖) := by
  set Fp : ℝ × ℝ → ℝ := fun p => φ p.1 * F (circleMap z p.1 p.2) with hFp
  have hcm := continuous_circleMap_uncurry z
  have hFpc : Continuous Fp := (hφ.comp continuous_fst).mul (hF.comp hcm)
  obtain ⟨CF, hCF⟩ := (isCompact_closedBall z b).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨Cφ, hCφ⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hφbd : ∀ t, ‖φ t‖ ≤ max Cφ 0 := by
    intro t
    by_cases h1 : t ≤ a
    · rw [hφa t h1, norm_zero]; exact le_max_right _ _
    by_cases h2 : b ≤ t
    · rw [hφb t h2, norm_zero]; exact le_max_right _ _
    exact (hCφ t ⟨(not_le.mp h1).le, (not_le.mp h2).le⟩).trans (le_max_left _ _)
  have hFpb : ∀ p, ‖Fp p‖ ≤ max Cφ 0 * max CF 0 := by
    intro p
    simp only [hFp, norm_mul]
    by_cases h1 : p.1 ≤ a
    · rw [hφa _ h1, norm_zero, zero_mul]; positivity
    by_cases h2 : b ≤ p.1
    · rw [hφb _ h2, norm_zero, zero_mul]; positivity
    refine mul_le_mul (hφbd _) ((hCF _ ?_).trans (le_max_left _ _)) (norm_nonneg _)
      (le_max_right _ _)
    rw [mem_closedBall, dist_eq_norm, norm_circleMap_sub_center, abs_of_pos (ha.trans
      (not_le.mp h1))]
    exact (not_le.mp h2).le
  have hFz : ∀ p : ℝ × ℝ, b < p.1 → Fp p = 0 := fun p hp => by
    simp only [hFp]; rw [hφb _ hp.le, zero_mul]
  have hint : IntegrableOn Fp (Ioi 0 ×ˢ Ioo (-π) π) (volume.prod volume) := by
    have hS : IntegrableOn Fp (Ioc 0 b ×ˢ Ioo (-π) π) (volume.prod volume) := by
      refine Measure.integrableOn_of_bounded ?_ hFpc.aestronglyMeasurable
        (Eventually.of_forall hFpb)
      rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    refine hS.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro p ⟨⟨hp1, hp2⟩, hpS⟩
    apply hFz
    by_contra h
    exact hpS ⟨⟨hp1, not_lt.mp h⟩, hp2⟩
  have hpt : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have hRHS : ∫ y, F y * (φ ‖y - z‖ / ‖y - z‖) = ∫ p in Ioi 0 ×ˢ Ioo (-π) π, Fp p := by
    rw [← integral_add_right_eq_self _ z]
    simp only [add_sub_cancel_right]
    rw [← Complex.integral_comp_polarCoord_symm, ← hpt]
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    rw [hpt] at hp
    have hp1 : 0 < p.1 := hp.1
    rw [polarCoord_symm_eq_circleMap, norm_circleMap_zero, abs_of_pos hp1]
    have e1 : circleMap 0 p.1 p.2 + z = circleMap z p.1 p.2 := by simp [circleMap, add_comm]
    rw [e1, smul_eq_mul, hFp]
    field_simp
  have hint' : Integrable Fp ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))) := by
    rw [Measure.prod_restrict]; exact hint
  have hinner : ∀ t, ∫ θ in Ioo (-π) π, Fp (t, θ) = φ t * ∫ θ in Ioo (-π) π, F (circleMap z t θ) :=
    fun t => by simp only [hFp]; exact integral_const_mul _ _
  refine ⟨?_, ?_⟩
  · have := hint'.integral_prod_left
    simp only [hinner] at this
    exact this
  · rw [hRHS, Measure.volume_eq_prod, setIntegral_prod _ hint]
    simp only [hinner]

/-- Folded version. -/
theorem integral_radial_foldedCircle_eq {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a)
    (hφa : ∀ t, t ≤ a → φ t = 0) (hφb : ∀ t, b ≤ t → φ t = 0) {f : ℂ → ℝ} (hf : Continuous f)
    (z : ℂ) :
    IntegrableOn (fun t => φ t * ∫ x, f x ∂(foldedCircle z t)) (Ioi 0) ∧
      ∫ t in Ioi 0, φ t * ∫ x, f x ∂(foldedCircle z t) =
        (2 * π)⁻¹ * ∫ y, f (foldH y) * (φ ‖y - z‖ / ‖y - z‖) := by
  have hF : Continuous (f ∘ foldH) := hf.comp CircleFubini.continuous_foldH'
  obtain ⟨h1, h2⟩ := integral_radial_circle_eq hφ ha hφa hφb hF z
  have e : ∀ t, φ t * ∫ x, f x ∂(foldedCircle z t) =
      (2 * π)⁻¹ * (φ t * ∫ θ in Ioo (-π) π, (f ∘ foldH) (circleMap z t θ)) := fun t => by
    rw [integral_foldedCircle_eq hf, integral_circleUnif_eq hF]; ring
  simp only [e]
  refine ⟨h1.const_mul _, ?_⟩
  rw [integral_const_mul, h2]
  rfl

/-- The Lipschitz difference bound. -/
theorem ofReal_abs_integral_foldH_sub_le {f : ℂ → ℝ} (hf : Continuous f) {ψ : ℂ → ℝ} {L : ℝ≥0}
    {b : ℝ} (hψ : LipschitzWith L ψ) (hψb : ∀ y, b ≤ ‖y‖ → ψ y = 0) {D : Set ℂ}
    (hDm : MeasurableSet D) {z z' : ℂ} (hz : z ∈ Hbar) (hz' : z' ∈ Hbar)
    (hsub : ∀ y ∈ H, ‖y - z‖ < b → y ∈ D) (hsub' : ∀ y ∈ H, ‖y - z'‖ < b → y ∈ D) :
    ENNReal.ofReal |(∫ y, f (foldH y) * ψ (y - z)) - ∫ y, f (foldH y) * ψ (y - z')| ≤
      ENNReal.ofReal (L * ‖z - z'‖) * (4 * ∫⁻ y in D, ‖f y‖ₑ) := by
  have hψc : Continuous ψ := hψ.continuous
  have hF : Continuous (f ∘ foldH) := hf.comp CircleFubini.continuous_foldH'
  have hcs : ∀ w : ℂ, HasCompactSupport fun y => f (foldH y) * ψ (y - w) := by
    intro w
    refine HasCompactSupport.intro (isCompact_closedBall w b) (fun y hy => ?_)
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    simp [hψb _ hy.le]
  have hI : ∀ w : ℂ, Integrable fun y => f (foldH y) * ψ (y - w) := fun w =>
    (hF.mul (hψc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (hcs w)
  rw [← integral_sub (hI z) (hI z'), ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hm : Measurable fun y : ℂ => ‖f y‖ₑ := hf.enorm.measurable
  have hpt : ∀ y, ‖f (foldH y) * ψ (y - z) - f (foldH y) * ψ (y - z')‖ₑ ≤
      ENNReal.ofReal (L * ‖z - z'‖) *
        ((ball z b).indicator (fun y => ‖f (foldH y)‖ₑ) y +
          (ball z' b).indicator (fun y => ‖f (foldH y)‖ₑ) y) := by
    intro y
    rw [← mul_sub, enorm_mul]
    have hL : ‖ψ (y - z) - ψ (y - z')‖ₑ ≤ ENNReal.ofReal (L * ‖z - z'‖) := by
      rw [← ofReal_norm, ← dist_eq_norm]
      refine ENNReal.ofReal_le_ofReal ((hψ.dist_le_mul _ _).trans (le_of_eq ?_))
      rw [dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev]
    by_cases hy : y ∈ ball z b
    · rw [indicator_of_mem hy, mul_comm (‖f (foldH y)‖ₑ)]
      exact mul_le_mul' hL le_self_add
    by_cases hy' : y ∈ ball z' b
    · rw [indicator_of_mem hy', mul_comm (‖f (foldH y)‖ₑ)]
      exact mul_le_mul' hL le_add_self
    · have h1 : ψ (y - z) = 0 := hψb _ (by rw [mem_ball, dist_eq_norm, not_lt] at hy; exact hy)
      have h2 : ψ (y - z') = 0 :=
        hψb _ (by rw [mem_ball, dist_eq_norm, not_lt] at hy'; exact hy')
      rw [h1, h2, sub_zero, enorm_zero, mul_zero]; exact zero_le
  calc ∫⁻ y, ‖f (foldH y) * ψ (y - z) - f (foldH y) * ψ (y - z')‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (L * ‖z - z'‖) *
          ((ball z b).indicator (fun y => ‖f (foldH y)‖ₑ) y +
            (ball z' b).indicator (fun y => ‖f (foldH y)‖ₑ) y) := lintegral_mono hpt
    _ = ENNReal.ofReal (L * ‖z - z'‖) * ((∫⁻ y in ball z b, ‖f (foldH y)‖ₑ) +
          ∫⁻ y in ball z' b, ‖f (foldH y)‖ₑ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left
          (Measurable.indicator (f := fun y => ‖f (foldH y)‖ₑ) (hm.comp measurable_foldH)
            measurableSet_ball),
          lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball]
    _ ≤ ENNReal.ofReal (L * ‖z - z'‖) * (2 * (∫⁻ y in D, ‖f y‖ₑ) + 2 * ∫⁻ y in D, ‖f y‖ₑ) := by
        gcongr
        · exact lintegral_ball_foldH_le hDm hz hsub hm
        · exact lintegral_ball_foldH_le hDm hz' hsub' hm
    _ = _ := by ring

/-- `L¹` bound from the Poincaré inequality. -/
theorem lintegral_enorm_le_of_poincare {D S : Set ℂ} (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {CP : ℝ} (hCP : ∀ f ∈ mixedSpace D S, ∫ z in D, f z ^ 2 ≤ CP * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2)
    {f : ℂ → ℝ} (hf : f ∈ mixedSpace D S) :
    ∫⁻ y in D, ‖f y‖ₑ ≤ volume D ^ (1 / 2 : ℝ) * (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal (∫ z in D, ‖fderiv ℝ f z‖ ^ 2) ^ (1 / 2 : ℝ)) := by
  have hfc : Continuous f := hf.1.continuous
  set G : ℝ := ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg hD.measurableSet fun _ _ => sq_nonneg _
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

end QuantumZipper.K3

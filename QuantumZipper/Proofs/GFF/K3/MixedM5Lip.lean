import QuantumZipper.Proofs.GFF.K3.MixedM5Polar
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The remainder kernel is Lipschitz (GFF-K3 node M5(c))

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M5, "Lipschitz"). With
`r(z) := remVec D S (foldedCircle z R)`:

* by the mean value property, `⟪r(z) − r(z'), u⟫ = ⟪v_{fold_{z,t}} − v_{fold_{z',t}}, u⟫` for every
  `u ⊥ M` and every radius `t ∈ (0, 2R)`; averaging over `t` with a smooth radial weight `φ`
  turns the pairing into `∫ f (ψ(· − z) − ψ(· − z'))`, `ψ(y) = φ(|y|)/|y|` (for `u = ∇f`), which
  is `O(|z − z'| ‖∇f‖)` by the Lipschitz bound on `ψ` and the Poincaré inequality (M3);
* `exists_abs_inner_remVec_sub_le`: `|⟪r(z) − r(z'), u⟫| ≤ K |z − z'| ‖u‖` for `u ⊥ M` in the
  gradient closure (density argument);
* **M5(c)** `remKernelLipschitz`: `remKernel D S R` is Lipschitz on `K × K`.

The blueprint sketch ("`remVec` differences are bounded by dual norms of
`fold_{z,s} − fold_{z',s}`, bounded via M4(i) by `C|z − z'|/s`") is implemented with the smooth
radial average in place of the annulus average (own elementary argument, cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

variable {D S K : Set ℂ} {R : ℝ}

/-- A smooth probability weight on `(a, b)`. -/
theorem exists_radial_weight {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ (∀ t, 0 ≤ φ t) ∧ (∀ t, t ≤ a → φ t = 0) ∧
      (∀ t, b ≤ t → φ t = 0) ∧ ∫ t in Ioi 0, φ t = 1 := by
  let β : ContDiffBump ((a + b) / 2) := ⟨(b - a) / 4, (b - a) / 2, by linarith, by linarith⟩
  have hout : ∀ t, (t ≤ a ∨ b ≤ t) → β.normed volume t = 0 := by
    intro t ht
    apply Function.notMem_support.mp
    rw [β.support_normed_eq, Real.ball_eq_Ioo]
    rintro ⟨h1, h2⟩
    have hr : β.rOut = (b - a) / 2 := rfl
    rw [hr] at h1 h2
    rcases ht with ht | ht <;> linarith
  refine ⟨β.normed volume, β.contDiff_normed, β.nonneg_normed, fun t ht => hout t (Or.inl ht),
    fun t ht => hout t (Or.inr ht), ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))
    (fun t ht => hout t (Or.inl ((not_lt.mp ht).trans ha.le)))]
  exact β.integral_normed

/-- `ψ(y) = φ(|y|)/|y|` is Lipschitz. -/
theorem exists_lipschitz_radial {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {a b : ℝ} (ha : 0 < a)
    (hφa : ∀ t, t ≤ a → φ t = 0) (hφb : ∀ t, b ≤ t → φ t = 0) :
    ∃ L : ℝ≥0, LipschitzWith L (fun y : ℂ => φ ‖y‖ / ‖y‖) := by
  have hcd : ContDiff ℝ 1 (fun y : ℂ => φ ‖y‖ / ‖y‖) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y = 0
    · subst hy
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [ball_mem_nhds (0 : ℂ) ha] with w hw
      rw [mem_ball, dist_zero_right] at hw
      simp [hφa _ hw.le]
    · have hn : ContDiffAt ℝ 1 (fun y : ℂ => ‖y‖) y := contDiffAt_norm ℝ hy
      exact (hφ.contDiffAt.comp y hn).div hn (norm_ne_zero_iff.mpr hy)
  have hcs : HasCompactSupport (fun y : ℂ => φ ‖y‖ / ‖y‖) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) b) (fun y hy => ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    simp [hφb _ hy.le]
  exact hcd.lipschitzWith_of_hasCompactSupport hcs one_ne_zero

theorem exists_norm_annulusFeat_le (hb : Bornology.IsBounded D) {s : ℝ} (hs : 0 < s) :
    ∃ CA : ℝ, ∀ z s', ‖annulusFeat D z s s'‖ ≤ CA := by
  have : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  refine ⟨(measureUnivNNReal (gradMeasure D) ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) *
    ((Real.sqrt (2 * π))⁻¹ * (2 * s⁻¹)), fun z s' => ?_⟩
  have hA := memLp_annulusVal hb z hs (s' := s') (D := D)
  have hf : annulusFeat D z s s' = hA.toLp _ := by simp [annulusFeat, hA]
  rw [hf]
  refine Lp.norm_le_of_ae_bound (by positivity) ?_
  filter_upwards [hA.coeFn_toLp] with p hp
  rw [hp]
  have hA' : ‖annulusField z s s' p.1‖ ≤ 2 * s⁻¹ := by
    rw [annulusField_eq, two_mul]
    exact (norm_add_le _ _).trans (add_le_add (norm_annulusTerm_le z hs _)
      (norm_annulusTerm_le _ hs _))
  unfold annulusVal
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  split_ifs
  · exact (Complex.abs_re_le_norm _).trans hA'
  · exact (Complex.abs_im_le_norm _).trans hA'

/-- Mean value property for any two radii in `(0, 2R)`. -/
theorem remVec_foldedCircle_eq_of_lt (h : MixedLocalHyp D S K R) {z : ℂ} (hz : z ∈ K) {s t : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * R) (ht : 0 < t) (ht2 : t < 2 * R) :
    remVec D S (foldedCircle z s) = remVec D S (foldedCircle z t) := by
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact remVec_foldedCircle_eq h.isOpen h.subset_H h.bounded h.free_real (h.local_ z hz) hs hst
      ht2
  · rfl
  · exact (remVec_foldedCircle_eq h.isOpen h.subset_H h.bounded h.free_real (h.local_ z hz) ht
      hts hs2).symm

theorem remVec_mem_gradClosure (hb : Bornology.IsBounded D) (ρ : Measure ℂ) :
    remVec D S ρ ∈ gradClosure D (mixedSpace D S) := by
  set M := annulusSpan D S
  have e : remVec D S ρ = rieszVec D (mixedSpace D S) ρ -
      M.starProjection (rieszVec D (mixedSpace D S) ρ) :=
    eq_sub_of_add_eq' (M.starProjection_add_starProjection_orthogonal _)
  rw [e]
  exact sub_mem rieszVec_mem (annulusSpan_le_gradClosure hb (M.starProjection_apply_mem _))

theorem inner_remVec_of_mem_orthogonal (ρ : Measure ℂ) {w : GradSpace D}
    (hw : w ∈ (annulusSpan D S)ᗮ) :
    ⟪remVec D S ρ, w⟫ = ⟪rieszVec D (mixedSpace D S) ρ, w⟫ := by
  set M := annulusSpan D S
  have hx := M.starProjection_add_starProjection_orthogonal (rieszVec D (mixedSpace D S) ρ)
  conv_rhs => rw [← hx]
  rw [inner_add_left, Submodule.inner_right_of_mem_orthogonal (M.starProjection_apply_mem _) hw,
    zero_add]
  rfl

/-- **Key estimate.** `|⟪r(z) − r(z'), u⟫| ≤ K |z − z'| ‖u‖` for `u ⊥ M` in the gradient
closure. -/
theorem exists_abs_inner_remVec_sub_le (h : MixedLocalHyp D S K R)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) :
    ∃ Kl : ℝ, ∀ z ∈ K, ∀ z' ∈ K, ∀ u ∈ gradClosure D (mixedSpace D S),
      u ∈ (annulusSpan D S)ᗮ →
      |⟪remVec D S (foldedCircle z R) - remVec D S (foldedCircle z' R), u⟫| ≤
        Kl * ‖z - z'‖ * ‖u‖ := by
  have hR := h.pos
  have hV := isDNSpace_mixedSpace D S
  set a : ℝ := R / 2 with ha_def
  have ha : 0 < a := by positivity
  have hab : a < R := by linarith
  obtain ⟨φ, hφ, hφ0, hφa, hφb, hφ1⟩ := exists_radial_weight ha hab
  obtain ⟨L, hL⟩ := exists_lipschitz_radial hφ ha hφa hφb
  have hψb : ∀ y : ℂ, R ≤ ‖y‖ → φ ‖y‖ / ‖y‖ = 0 := fun y hy => by rw [hφb _ hy, zero_div]
  have hφcs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := R)) (fun t ht => ?_)
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · exact hφa t ht.le
    · exact hφb t ht.le
  have hφint : IntegrableOn φ (Ioi 0) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφcs).integrableOn
  obtain ⟨CP, hCP⟩ := mixed_poincare h.isOpen h.subset_H h.bounded h.free_real
  obtain ⟨Ba, hBa⟩ := exists_norm_rieszVec_foldedCircle_le h.isOpen h.subset_H h.bounded
    h.free_real hR h.local_ ha hab
  obtain ⟨CA, hCA⟩ := exists_norm_annulusFeat_le (D := D) h.bounded ha
  set W : ℝ := 2 * (Ba + CA) with hWdef
  set vd : ℝ := (volume D ^ (1 / 2 : ℝ)).toReal with hvd
  set cp : ℝ := (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ)).toReal with hcp
  set K2 : ℝ := (2 * π)⁻¹ * (4 * (vd * cp)) * L * Real.sqrt (2 * π) with hK2
  refine ⟨K2, fun z hz z' hz' u hu hu' => ?_⟩
  have hzH := (h.local_ z hz).1
  have hz'H := (h.local_ z' hz').1
  set c := ⟪remVec D S (foldedCircle z R) - remVec D S (foldedCircle z' R), u⟫ with hc_def
  have hc : ∀ t, 0 < t → t < 2 * R →
      ⟪rieszVec D (mixedSpace D S) (foldedCircle z t) -
        rieszVec D (mixedSpace D S) (foldedCircle z' t), u⟫ = c := by
    intro t ht ht2
    rw [hc_def, inner_sub_left, inner_sub_left, ← inner_remVec_of_mem_orthogonal _ hu',
      ← inner_remVec_of_mem_orthogonal _ hu', remVec_foldedCircle_eq_of_lt h hz ht ht2 hR
        (by linarith), remVec_foldedCircle_eq_of_lt h hz' ht ht2 hR (by linarith)]
  have hW : ∀ t, a < t → t < 2 * R →
      ‖rieszVec D (mixedSpace D S) (foldedCircle z t) -
        rieszVec D (mixedSpace D S) (foldedCircle z' t)‖ ≤ W := by
    intro t hat ht2
    have hb1 : ∀ w ∈ K, ‖rieszVec D (mixedSpace D S) (foldedCircle w t)‖ ≤ Ba + CA := by
      intro w hw
      have e : rieszVec D (mixedSpace D S) (foldedCircle w t) =
          rieszVec D (mixedSpace D S) (foldedCircle w a) - annulusFeat D w a t := by
        rw [← rieszVec_annulus' h.isOpen h.subset_H h.bounded h.free_real (h.local_ w hw) ha hat
          ht2]
        abel
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add (hBa w hw) (hCA w t))
    refine (norm_sub_le _ _).trans ?_
    rw [hWdef]; linarith [hb1 z hz, hb1 z' hz']
  have hu2 : u ∈ closure (Submodule.span ℝ (gradFeat D '' mixedSpace D S) : Set (GradSpace D)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hu
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.mp hu2
  choose f hf hfg using fun n => mem_image_of_mem_span hV (hg n)
  have hsub : ∀ w ∈ K, ∀ y ∈ H, ‖y - w‖ < R → y ∈ D := fun w hw y hy hyw =>
    (h.local_ w hw).mem_of_mem_H h.isOpen h.free_real hy (by linarith)
  have hn : ∀ n, |c| ≤ K2 * ‖z - z'‖ * ‖g n‖ + W * ‖g n - u‖ := by
    intro n
    have hfn := hf n
    have hfc : Continuous (f n) := hfn.1.continuous
    have hf1 : ContDiff ℝ 1 (f n) := hfn.1.of_le one_le_smooth
    obtain ⟨hIz, hAz⟩ := integral_radial_foldedCircle_eq hφ.continuous ha hφa hφb hfc z
    obtain ⟨hIz', hAz'⟩ := integral_radial_foldedCircle_eq hφ.continuous ha hφa hφb hfc z'
    set Az := ∫ t in Ioi 0, φ t * ∫ x, f n x ∂(foldedCircle z t) with hAz_def
    set Az' := ∫ t in Ioi 0, φ t * ∫ x, f n x ∂(foldedCircle z' t) with hAz'_def
    -- (i) the Lipschitz/Poincaré bound
    set G : ℝ := ∫ w in D, ‖fderiv ℝ (f n) w‖ ^ 2 with hG
    have hG0 : 0 ≤ G := setIntegral_nonneg h.isOpen.measurableSet fun _ _ => sq_nonneg _
    have hgn : ‖g n‖ ^ 2 = (2 * π)⁻¹ * G := by
      rw [← hfg n, norm_gradFeat_sq hf1 hfn.2.1]; rfl
    have hsqrtG : Real.sqrt G = Real.sqrt (2 * π) * ‖g n‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (g n)), ← Real.sqrt_mul (by positivity), hgn,
        ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    have hE := ofReal_abs_integral_foldH_sub_le hfc hL hψb h.isOpen.measurableSet hzH hz'H
      (hsub z hz) (hsub z' hz')
    have hP := lintegral_enorm_le_of_poincare h.isOpen h.bounded hCP hfn
    rw [← hG] at hP
    have hVD : volume D ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) h.bounded.measure_lt_top.ne
    have hCPt : ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have hYt : ENNReal.ofReal G ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have hY : (ENNReal.ofReal G ^ (1 / 2 : ℝ)).toReal = Real.sqrt G := by
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hG0, Real.sqrt_eq_rpow]
    have hX := ENNReal.toReal_mono (by finiteness)
      (hE.trans (mul_le_mul_right (mul_le_mul_right hP 4) _))
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hX
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg L.coe_nonneg (norm_nonneg _))]
      at hX
    rw [hY] at hX
    rw [← hvd, ← hcp] at hX
    have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
    rw [h4] at hX
    have hdiff : |Az - Az'| ≤ K2 * ‖z - z'‖ * ‖g n‖ := by
      rw [hAz, hAz', ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
      calc (2 * π)⁻¹ * |(∫ y, f n (foldH y) * (φ ‖y - z‖ / ‖y - z‖)) -
              ∫ y, f n (foldH y) * (φ ‖y - z'‖ / ‖y - z'‖)|
          ≤ (2 * π)⁻¹ * (L * ‖z - z'‖ * (4 * (vd * (cp * Real.sqrt G)))) :=
            mul_le_mul_of_nonneg_left hX (by positivity)
        _ = K2 * ‖z - z'‖ * ‖g n‖ := by rw [hsqrtG, hK2]; ring
    -- (ii) comparison with `c`
    have hDn : ∀ t ∈ Ioi (0 : ℝ), ‖φ t * (∫ x, f n x ∂(foldedCircle z t) -
        ∫ x, f n x ∂(foldedCircle z' t)) - φ t * c‖ ≤ φ t * (W * ‖g n - u‖) := by
      intro t ht
      by_cases hta : t ≤ a
      · rw [hφa t hta]; simp
      by_cases htR : R ≤ t
      · rw [hφb t htR]; simp
      push Not at hta htR
      have ht2 : t < 2 * R := by linarith
      have e1 := pair_rieszVec hV (isAdmissibleDual_foldedCircle_of_local h.isOpen h.subset_H
        h.bounded h.free_real (h.local_ z hz) (ha.trans hta) ht2) hpos (f n) hfn
      have e2 := pair_rieszVec hV (isAdmissibleDual_foldedCircle_of_local h.isOpen h.subset_H
        h.bounded h.free_real (h.local_ z' hz') (ha.trans hta) ht2) hpos (f n) hfn
      rw [← e1, ← e2, hfg n, ← inner_sub_left, ← hc t (ha.trans hta) ht2, ← mul_sub,
        ← inner_sub_right, norm_mul, Real.norm_of_nonneg (hφ0 t)]
      refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (hφ0 t)
      exact mul_le_mul_of_nonneg_right (hW t hta ht2) (norm_nonneg _)
    have hrel : |(Az - Az') - c| ≤ W * ‖g n - u‖ := by
      have hI3 : IntegrableOn (fun t => φ t * (∫ x, f n x ∂(foldedCircle z t) -
          ∫ x, f n x ∂(foldedCircle z' t))) (Ioi 0) :=
        (hIz.sub hIz').congr_fun (fun t _ => by simp only [Pi.sub_apply, mul_sub])
          measurableSet_Ioi
      have e1 : Az - Az' = ∫ t in Ioi 0, φ t * (∫ x, f n x ∂(foldedCircle z t) -
          ∫ x, f n x ∂(foldedCircle z' t)) := by
        rw [hAz_def, hAz'_def, ← integral_sub hIz hIz']
        congr 1; funext t; ring
      have e2 : ∫ t in Ioi 0, φ t * c = c := by rw [integral_mul_const, hφ1, one_mul]
      have e : (Az - Az') - c = ∫ t in Ioi 0, (φ t * (∫ x, f n x ∂(foldedCircle z t) -
          ∫ x, f n x ∂(foldedCircle z' t)) - φ t * c) := by
        rw [e1, integral_sub hI3 (hφint.mul_const c), e2]
      rw [e, ← Real.norm_eq_abs]
      calc ‖∫ t in Ioi 0, (φ t * (∫ x, f n x ∂(foldedCircle z t) -
            ∫ x, f n x ∂(foldedCircle z' t)) - φ t * c)‖
          ≤ ∫ t in Ioi 0, φ t * (W * ‖g n - u‖) :=
            norm_integral_le_of_norm_le (hφint.mul_const _)
              (ae_restrict_of_forall_mem measurableSet_Ioi hDn)
        _ = W * ‖g n - u‖ := by rw [integral_mul_const, hφ1, one_mul]
    calc |c| = |(Az - Az') - ((Az - Az') - c)| := by ring_nf
      _ ≤ |Az - Az'| + |(Az - Az') - c| := abs_sub _ _
      _ ≤ K2 * ‖z - z'‖ * ‖g n‖ + W * ‖g n - u‖ := add_le_add hdiff hrel
  have hT : Tendsto (fun n => K2 * ‖z - z'‖ * ‖g n‖ + W * ‖g n - u‖) atTop
      (𝓝 (K2 * ‖z - z'‖ * ‖u‖ + W * ‖u - u‖)) :=
    (hlim.norm.const_mul _).add ((hlim.sub_const u).norm.const_mul W)
  have := ge_of_tendsto' hT hn
  simpa using this

end QuantumZipper.K3

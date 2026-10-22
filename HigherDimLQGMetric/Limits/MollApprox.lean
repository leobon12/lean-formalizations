import HigherDimLQGMetric.Limits.TightScales
import HigherDimLQGMetric.ConvField.ContBound

/-! Approximation of bounded continuous functions by the pinned convolution kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Change variables from the physical convolution to the unscaled kernel. -/
theorem l6c_conv_ofCont_change_variables {d : ℕ}
    (κ : Rd d → ℝ) (f : C(Rd d, ℝ)) {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    (∫ w : Rd d, convKernelEps κ ε (z - w) * f w) =
      ∫ u : Rd d, convKernel κ u * f (z - ε • u) := by
  let F : Rd d → ℝ := fun w => convKernelEps κ ε (z - w) * f w
  have h := integral_comp_affinePt_abs F (-ε) z
  have hp : |(-ε : ℝ)| ^ d = ε ^ d := by rw [abs_neg, abs_of_pos hε]
  rw [hp] at h
  have heval (u : Rd d) : F ((-ε) • u + z) =
      ε ^ (-(d : ℝ)) * (convKernel κ u * f (z - ε • u)) := by
    dsimp [F, convKernelEps]
    have he : z - ((-ε) • u + z) = ε • u := by
      rw [neg_smul]
      abel_nf
    rw [he]
    have he2 : ε⁻¹ • (ε • u) = u := by
      rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    rw [he2]
    rw [← mul_assoc]
    congr 1
    rw [neg_smul]
    abel_nf
  simp_rw [heval] at h
  rw [integral_const_mul] at h
  have hpow : ε ^ (-(d : ℝ)) * ε ^ d = 1 := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ hε.ne')
  have hpow' : ε ^ (-(d : ℝ)) = (ε ^ d)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast]
  rw [hpow'] at h
  have hn : ε ^ d ≠ 0 := pow_ne_zero _ hε.ne'
  exact (mul_left_cancel₀ (inv_ne_zero hn)) (by
    simpa only [inv_mul_cancel₀ hn, one_mul] using h.symm)

/-- Convolution of a bounded continuous function with the pinned L¹ kernel is continuous. -/
theorem l6c_continuous_convMollify_ofCont {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (f : C(Rd d, ℝ)) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) :
    Continuous (convMollify κ ε (ofCont f)) := by
  have hK : Integrable (convKernel κ) := integrable_convKernel hd hκ
  have hmeas (z : Rd d) : AEStronglyMeasurable
      (fun u : Rd d => convKernel κ u * f (z - ε • u)) :=
    (hK.aestronglyMeasurable.mul
      (f.continuous.comp (by fun_prop : Continuous
        (fun u : Rd d => z - ε • u))).aestronglyMeasurable)
  have hbound (z : Rd d) : ∀ᵐ u : Rd d ∂volume,
      ‖convKernel κ u * f (z - ε • u)‖ ≤
        M * |convKernel κ u| := by
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hM _) (abs_nonneg (convKernel κ u))
  have hcont (u : Rd d) : Continuous
      (fun z : Rd d => convKernel κ u * f (z - ε • u)) :=
    continuous_const.mul (f.continuous.comp (by fun_prop))
  have h := continuous_of_dominated hmeas hbound
    (hK.abs.const_mul M) (Filter.Eventually.of_forall hcont)
  have heq (z : Rd d) : convMollify κ ε (ofCont f) z =
      ∫ u : Rd d, convKernel κ u * f (z - ε • u) := by
    rw [l2b_convMollify_ofCont hd hκ hε f M hM z]
    exact l6c_conv_ofCont_change_variables κ f hε z
  convert h using 1
  funext z
  exact heq z

/-- The absolute mass of an integrable kernel escapes every fixed tail. -/
theorem l6c_convKernel_tail_zero {d : ℕ} (κ : Rd d → ℝ)
    (hK : Integrable (convKernel κ)) :
    Tendsto (fun n : ℕ => ∫ u in {u : Rd d | (n : ℝ) ≤ ‖u‖},
      |convKernel κ u|) atTop (𝓝 0) := by
  let S : ℕ → Set (Rd d) := fun n => {u | (n : ℝ) ≤ ‖u‖}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hanti : Antitone S := by
    intro m n hmn u hu
    change (n : ℝ) ≤ ‖u‖ at hu
    change (m : ℝ) ≤ ‖u‖
    have hmnr : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact hmnr.trans hu
  have hempty : (⋂ n, S n) = ∅ := by
    ext u
    obtain ⟨n, hn⟩ := exists_nat_gt ‖u‖
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hall
    exact (not_le_of_gt hn) (hall n)
  have ht := hanti.tendsto_setIntegral hS hK.abs.integrableOn
  rw [hempty, setIntegral_empty] at ht
  exact ht

/-- A near/far split of the convolution error.  It is valid for signed kernels. -/
theorem l6c_conv_error_bound {d : ℕ} (κ : Rd d → ℝ)
    (hK : Integrable (convKernel κ))
    (f g : C(Rd d, ℝ)) (ε : ℝ) (z : Rd d)
    (M a N : ℝ) (_hM : 0 ≤ M) (ha : 0 ≤ a)
    (hfg : ∀ w, |f w| ≤ M ∧ |g w| ≤ M)
    (hnear : ∀ u : Rd d, ‖u‖ < N → |g (z - ε • u) - f z| ≤ a) :
    |∫ u : Rd d, convKernel κ u * (g (z - ε • u) - f z)| ≤
      a * (∫ u : Rd d, |convKernel κ u|) +
      2 * M * (∫ u in {u : Rd d | N ≤ ‖u‖}, |convKernel κ u|) := by
  let S : Set (Rd d) := {u | N ≤ ‖u‖}
  have hS : MeasurableSet S :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  let B : Rd d → ℝ := fun u =>
    a * |convKernel κ u| + S.indicator (fun u => 2 * M * |convKernel κ u|) u
  have hBi : Integrable B :=
    (hK.abs.const_mul a).add ((hK.abs.const_mul (2 * M)).indicator hS)
  have hpoint (u : Rd d) :
      ‖convKernel κ u * (g (z - ε • u) - f z)‖ ≤ B u := by
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hu : u ∈ S
    · have hg := (hfg (z - ε • u)).2
      have hf := (hfg z).1
      have hb : |g (z - ε • u) - f z| ≤ 2 * M := by
        calc
          _ ≤ |g (z - ε • u)| + |f z| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      dsimp [B]
      rw [Set.indicator_of_mem hu]
      have hmul := mul_le_mul_of_nonneg_left hb (abs_nonneg (convKernel κ u))
      nlinarith [mul_nonneg ha (abs_nonneg (convKernel κ u))]
    · have hsmall : ‖u‖ < N := lt_of_not_ge hu
      have hb := hnear u hsmall
      dsimp [B]
      simp only [Set.indicator, hu, ↓reduceIte]
      simpa only [add_zero, mul_comm] using
        mul_le_mul_of_nonneg_left hb (abs_nonneg (convKernel κ u))
  have hmain := norm_integral_le_of_norm_le hBi (Filter.Eventually.of_forall hpoint)
  rw [Real.norm_eq_abs] at hmain
  have hBint : (∫ u : Rd d, B u) =
      a * (∫ u : Rd d, |convKernel κ u|) +
      2 * M * (∫ u in S, |convKernel κ u|) := by
    dsimp [B]
    rw [integral_add (hK.abs.const_mul a) ((hK.abs.const_mul (2 * M)).indicator hS)]
    rw [integral_const_mul, integral_indicator hS, integral_const_mul]
  exact hmain.trans_eq hBint

/-- The pinned signed L¹ kernel is an approximate identity, uniformly on
compact sets even when the bounded continuous function varies with `n`. -/
theorem l6c_tendstoUniformlyOn_convMollify_seq {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {fn : ℕ → C(Rd d, ℝ)} {f : C(Rd d, ℝ)} {M : ℝ}
    (hfnM : ∀ n z, |fn n z| ≤ M) (hfM : ∀ z, |f z| ≤ M)
    (hconv : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop (closedBall 0 R))
    {R : ℝ} (hR : 0 < R) :
    TendstoUniformlyOn
      (fun n z => convMollify κ (εs n) (ofCont (fn n)) z) ⇑f atTop
      (closedBall (0 : Rd d) R) := by
  have hK : Integrable (convKernel κ) := integrable_convKernel hd hκ
  let A : ℝ := ∫ u : Rd d, |convKernel κ u|
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  let a : ℝ := η / (8 * (A + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hKc : IsCompact (closedBall (0 : Rd d) (R + 1)) := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous f.continuous.continuousOn) a ha
  let δ₁ := min δ 1
  have hδ₁ : 0 < δ₁ := lt_min hδ one_pos
  let t : ℝ := η / (8 * (M + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have htailEv : ∀ᶠ n : ℕ in atTop,
      (∫ u in {u : Rd d | (n : ℝ) ≤ ‖u‖}, |convKernel κ u|) < t :=
    (l6c_convKernel_tail_zero κ hK).eventually (gt_mem_nhds ht)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htailEv
  have htail : (∫ u in {u : Rd d | (N : ℝ) ≤ ‖u‖}, |convKernel κ u|) < t :=
    hN N le_rfl
  have hfnEv := (Metric.tendstoUniformlyOn_iff.mp
    (hconv (R + 1) (by linarith))) a ha
  have hεEv : ∀ᶠ n in atTop, εs n * (N : ℝ) < δ₁ := by
    have hεN : Tendsto (fun n => εs n * (N : ℝ)) atTop (𝓝 0) := by
      simpa only [zero_mul] using hεt.mul_const (N : ℝ)
    exact hεN.eventually (gt_mem_nhds hδ₁)
  filter_upwards [hfnEv, hεEv] with n hn he z hz
  have hnear (u : Rd d) (hu : ‖u‖ < (N : ℝ)) :
      |fn n (z - εs n • u) - f z| ≤ 2 * a := by
    have hzu : z - εs n • u ∈ closedBall (0 : Rd d) (R + 1) := by
      rw [mem_closedBall, dist_zero_right] at hz ⊢
      calc
        ‖z - εs n • u‖ ≤ ‖z‖ + ‖εs n • u‖ := norm_sub_le _ _
        _ ≤ R + 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hεs n)]
          have hmul : εs n * ‖u‖ < δ₁ :=
            (mul_lt_mul_of_pos_left hu (hεs n)).trans he
          linarith [min_le_right δ 1]
    have hz1 : z ∈ closedBall (0 : Rd d) (R + 1) :=
      closedBall_subset_closedBall (by linarith) hz
    have hdist : dist (z - εs n • u) z < δ := by
      rw [dist_eq_norm]
      have heq : z - εs n • u - z = -(εs n • u) := by abel_nf
      rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (hεs n)]
      exact (mul_lt_mul_of_pos_left hu (hεs n)).trans he |>.trans_le (min_le_left δ 1)
    have hmod := hδf (z - εs n • u) hzu z hz1 hdist
    have hfn := hn (z - εs n • u) hzu
    rw [Real.dist_eq] at hmod hfn
    rw [abs_sub_comm] at hfn
    calc
      |fn n (z - εs n • u) - f z| ≤
          |fn n (z - εs n • u) - f (z - εs n • u)| +
            |f (z - εs n • u) - f z| := abs_sub_le _ _ _
      _ ≤ 2 * a := by linarith
  have herr := l6c_conv_error_bound κ hK f (fn n) (εs n) z
    M (2 * a) N hM (by positivity) (fun w => ⟨hfM w, hfnM n w⟩) hnear
  have hmass : ∫ u : Rd d, convKernel κ u = 1 :=
    convKernel_integral_eq_one (by omega) hκ hK
  have hint1 : Integrable (fun u : Rd d =>
      convKernel κ u * fn n (z - εs n • u)) := by
    apply Integrable.mono' (hK.abs.const_mul M)
    · exact (hK.aestronglyMeasurable.mul
        ((fn n).continuous.comp (by fun_prop : Continuous
          (fun u : Rd d => z - εs n • u))).aestronglyMeasurable)
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hfnM n _) (abs_nonneg (convKernel κ u))
  have hint0 : Integrable (fun u : Rd d => convKernel κ u * f z) :=
    hK.mul_const _
  have heq : convMollify κ (εs n) (ofCont (fn n)) z - f z =
      ∫ u : Rd d, convKernel κ u * (fn n (z - εs n • u) - f z) := by
    rw [l2b_convMollify_ofCont hd hκ (hεs n) (fn n) M (hfnM n) z,
      l6c_conv_ofCont_change_variables κ (fn n) (hεs n) z]
    have hfz : f z = ∫ u : Rd d, convKernel κ u * f z := by
      rw [integral_mul_const, hmass, one_mul]
    nth_rewrite 1 [hfz]
    rw [← integral_sub hint1 hint0]
    congr 1
    funext u
    ring
  rw [Real.dist_eq, abs_sub_comm, heq]
  have haeq : a * (A + 1) = η / 8 := by
    dsimp [a]
    field_simp
  have hteq : t * (M + 1) = η / 8 := by
    dsimp [t]
    field_simp
  have htail0 : 0 ≤ (∫ u in {u : Rd d | (N : ℝ) ≤ ‖u‖},
      |convKernel κ u|) :=
    setIntegral_nonneg (isClosed_le continuous_const continuous_norm).measurableSet
      (fun _ _ => abs_nonneg _)
  have hbound : 2 * a * A + 2 * M *
      (∫ u in {u : Rd d | (N : ℝ) ≤ ‖u‖}, |convKernel κ u|) < η := by
    have hprod := mul_lt_mul_of_pos_left htail (by nlinarith : 0 < 2 * (M + 1))
    nlinarith [mul_nonneg ha.le hA]
  exact herr.trans_lt hbound

end HigherDimLQGMetric

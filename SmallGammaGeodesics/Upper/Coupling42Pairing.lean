import SmallGammaGeodesics.Upper.Coupling42Path
import SmallGammaGeodesics.NIC.Transport

/-!
# Lemma 4.2′, Step 6 (part 2): the pairing identity (b5) (blueprint `lem:coupling`)

Let `D` be a near-identity pair (`NIC.NearIdPair`) whose inverse `Ψ` is `2`-Lipschitz and
`1/2`-co-Lipschitz, `λ = pathMeas segPath` the uniform measure on `[0,1]`, `λ_n = bumpPath n segPath`
its mollifications, `τ` the transport of `D` and `μ_n = bumpPath n (Ψ ∘ ·)` the mollifications of
`Ψ_*λ`. Then:

* `τλ_n dx = (λ * ψ_n) ∘ Ψ⁻¹` (`withDensity_transport`), and the potential of `τλ_n` is within
  `C 2^{-n/2}` of `U_{Ψ_*λ}` (`abs_logPot_transport_sub_le`): `log|x − Ψ(t + z)|` and
  `log|x − Ψ(t)|` differ by `O(|z|^{1/2})` in `L¹(dt)` (GaussianLQG's `abs_log_sub_log_le` and the
  negative moments of the bi-Lipschitz path measures);
* hence `logCov(τλ_n − μ_n) ≤ C 2^{-n/2}` and, for every whole-plane GFF `h`,
  `⟨h, τλ_n⟩ − ⟨h, μ_n⟩ → 0` almost surely (`ae_tendsto_transport_sub`; blueprint
  `lem:pairing-limits` (b), with the explicit `H_*`-free bound replacing the dual-space argument);
* `∫ K λ_n → ∫ K dλ` for `K` continuous near `[0,1]` (`tendsto_integral_mul_segBump`);
* **(b5)** (`ae_measPairing_eq`): if `⟨h, τλ_n⟩ = ⟨h̄, λ_n⟩ + ∫ K λ_n` for all large `n` almost
  surely, then `measPairing(h̄, λ) = measPairing(h, Ψ_*λ) − ∫ K dλ` almost surely.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal Distributions BoundedContinuousFunction

namespace SmallGammaGeodesics

namespace Coupling42

open LQGMetric GaussianLQG.Realization

/-! ## The two paths -/

/-- the segment `t ↦ t` -/
def segPath : C(ℝ, ℂ) := ⟨fun t : ℝ => (t : ℂ), Complex.continuous_ofReal⟩

theorem lip_segPath : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1,
    1 * |t - t'| ≤ ‖segPath t - segPath t'‖ := fun t _ t' _ => by
  show 1 * |t - t'| ≤ ‖(t : ℂ) - t'‖
  rw [one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem segMeasure_eq : GaussianLQG.segMeasure 0 1 = pathMeas segPath :=
  segMeasure_eq_pathMeas

theorem ballBound_segPath : BallBound (pathMeas segPath) (2 / 1) 1 :=
  ballBound_pathMeas segPath.continuous.measurable one_pos lip_segPath

section pair

variable (D : NIC.NearIdPair)

/-- the image path `t ↦ Ψ(t)` -/
def invPath : C(ℝ, ℂ) := ⟨fun t : ℝ => D.Ψ t, D.continuous_inv.comp Complex.continuous_ofReal⟩

/-- the Lipschitz bounds of `Ψ` used here -/
structure PsiLip : Prop where
  lip : ∀ w w', ‖D.Ψ w - D.Ψ w'‖ ≤ 2 * ‖w - w'‖
  anti : ∀ w w', ‖w - w'‖ ≤ 2 * ‖D.Ψ w - D.Ψ w'‖

variable {D}

theorem lip_shiftPath (hD : PsiLip D) (z : ℂ) : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1,
    1 / 2 * |t - t'| ≤ ‖D.Ψ (t + z) - D.Ψ (t' + z)‖ := fun t _ t' _ => by
  have h := hD.anti (t + z) (t' + z)
  rw [show (t : ℂ) + z - (t' + z) = ((t - t' : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs] at h
  linarith

theorem measurable_shiftPath (z : ℂ) : Measurable fun t : ℝ => D.Ψ (t + z) :=
  (D.continuous_inv.comp (Complex.continuous_ofReal.add continuous_const)).measurable

theorem ballBound_shiftPath (hD : PsiLip D) (z : ℂ) :
    BallBound (pathMeas fun t : ℝ => D.Ψ (t + z)) (2 / (1 / 2)) 1 :=
  ballBound_pathMeas (measurable_shiftPath z) (by norm_num) (lip_shiftPath hD z)

theorem invPath_eq_shift : (pathMeas (invPath D)) = pathMeas fun t : ℝ => D.Ψ (t + 0) := by
  congr 1
  funext t
  simp [invPath]

theorem ballBound_invPath (hD : PsiLip D) : BallBound (pathMeas (invPath D)) (2 / (1 / 2)) 1 := by
  rw [invPath_eq_shift]; exact ballBound_shiftPath hD 0

/-- `‖Ψ(t + z)‖ ≤ ‖Ψ 0‖ + 2(1 + ‖z‖)` on `[0,1]` -/
theorem shiftPath_compl_closedBall (hD : PsiLip D) (z : ℂ) :
    (pathMeas fun t : ℝ => D.Ψ (t + z)) (closedBall (0 : ℂ) (‖D.Ψ 0‖ + 2 * (1 + ‖z‖)))ᶜ = 0 := by
  refine pathMeas_compl_eq_zero (measurable_shiftPath z) measurableSet_closedBall fun t ht => ?_
  rw [mem_closedBall, dist_zero_right]
  have h1 := hD.lip (t + z) 0
  have h2 : ‖(t : ℂ) + z‖ ≤ 1 + ‖z‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    linarith [ht.2]
  rw [sub_zero] at h1
  have h3 := norm_sub_norm_le (D.Ψ (t + z)) (D.Ψ 0)
  linarith

/-! ## The negative moments and the shift comparison -/

theorem real_univ_shiftPath (z : ℂ) : (pathMeas fun t : ℝ => D.Ψ (t + z)).real univ = 1 :=
  pathMeas_real_univ (measurable_shiftPath z)

theorem negMoment_shiftPath (z : ℂ) :
    negMoment (pathMeas fun t : ℝ => D.Ψ (t + z)) (2 / (1 / 2)) 1 sH = 5 := by
  rw [negMoment, real_univ_shiftPath]; norm_num [sH]

/-- **Shift comparison**: `|U_{ν_z}(x) − U_{ν_0}(x)| ≤ 20 (2|z|)^{1/2}` for the path measures
`ν_z = (t ↦ Ψ(t + z))_* Leb|[0,1]`. -/
theorem abs_logPotM_shift_sub_le (hD : PsiLip D) (z x : ℂ) :
    |logPotM (pathMeas fun t : ℝ => D.Ψ (t + z)) x -
        logPotM (pathMeas fun t : ℝ => D.Ψ (t + 0)) x| ≤ 20 * (2 * ‖z‖) ^ sH := by
  have hs : (0 : ℝ) < sH := by norm_num [sH]
  have hs1 : sH ≤ 1 := by norm_num [sH]
  have hsα : sH < 1 := by norm_num [sH]
  set νz := pathMeas fun t : ℝ => D.Ψ (t + z) with hνz
  set ν0 := pathMeas fun t : ℝ => D.Ψ (t + 0) with hν0
  have hbz := ballBound_shiftPath hD z
  have hb0 := ballBound_shiftPath hD 0
  set μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1) with hμ
  -- integrals over the path measures as integrals over `[0,1]`
  have hmap : ∀ (w : ℂ) (F : ℂ → ℝ), Measurable F →
      ∫ v, F v ∂(pathMeas fun t : ℝ => D.Ψ (t + w)) = ∫ t : ℝ, F (D.Ψ ((t : ℂ) + w)) ∂μ := by
    intro w F hF
    rw [pathMeas, integral_map (measurable_shiftPath w).aemeasurable hF.aestronglyMeasurable]
  have hint : ∀ w : ℂ, Integrable (fun t : ℝ => -Real.log ‖x - D.Ψ (t + w)‖) μ := by
    intro w
    have hi := (integrable_log_norm_sub (ballBound_shiftPath hD w) one_pos
      (shiftPath_compl_closedBall hD w) x).neg
    exact (integrable_map_measure (measurable_neg_log_norm_sub x).aestronglyMeasurable
      (measurable_shiftPath w).aemeasurable).mp hi
  have hintr : ∀ w : ℂ, Integrable (fun t : ℝ => ‖x - D.Ψ (t + w)‖ ^ (-sH)) μ := by
    intro w
    exact (integrable_map_measure (measurable_rpow_neg_norm sH x).aestronglyMeasurable
      (measurable_shiftPath w).aemeasurable).mp
      (integrable_rpow_neg (ballBound_shiftPath hD w) hs hsα x)
  have hrz : ∫ t : ℝ, ‖x - D.Ψ ((t : ℂ) + z)‖ ^ (-sH) ∂μ ≤ 5 := by
    rw [← hmap z _ (measurable_rpow_neg_norm sH x), ← negMoment_shiftPath (D := D) z]
    exact integral_rpow_neg_le hbz hs hsα x
  have hr0 : ∫ t : ℝ, ‖x - D.Ψ ((t : ℂ) + 0)‖ ^ (-sH) ∂μ ≤ 5 := by
    rw [← hmap 0 _ (measurable_rpow_neg_norm sH x), ← negMoment_shiftPath (D := D) 0]
    exact integral_rpow_neg_le hb0 hs hsα x
  -- a.e. the two distances are positive
  have hne : ∀ w : ℂ, ∀ᵐ t : ℝ ∂μ, 0 < ‖x - D.Ψ ((t : ℂ) + w)‖ := by
    intro w
    have h0 := (ballBound_shiftPath hD w).measure_singleton one_pos x
    rw [pathMeas, Measure.map_apply (measurable_shiftPath w) (measurableSet_singleton x)] at h0
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) h0
    simp only [not_lt, mem_ofPred_eq, norm_le_zero_iff, sub_eq_zero] at ht
    exact ht.symm
  have hlog : ∀ᵐ t : ℝ ∂μ, |(-Real.log ‖x - D.Ψ ((t : ℂ) + z)‖) -
      (-Real.log ‖x - D.Ψ ((t : ℂ) + 0)‖)| ≤ (2 * ‖z‖) ^ sH *
        (‖x - D.Ψ ((t : ℂ) + z)‖ ^ (-sH) + ‖x - D.Ψ ((t : ℂ) + 0)‖ ^ (-sH)) / sH := by
    filter_upwards [hne z, hne 0] with t h1 h2
    rw [neg_sub_neg, abs_sub_comm]
    refine (abs_log_sub_log_le h1 h2 hs hs1).trans ?_
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) ?_ hs.le) (by positivity)) hs.le
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [show x - D.Ψ (t + z) - (x - D.Ψ (t + 0)) = D.Ψ (t + 0) - D.Ψ (t + z) by ring]
    refine (hD.lip _ _).trans (le_of_eq ?_)
    rw [show (t : ℂ) + 0 - (t + z) = -z by ring, norm_neg]
  rw [logPotM, logPotM, hmap z _ (measurable_neg_log_norm_sub x),
    hmap 0 _ (measurable_neg_log_norm_sub x), ← integral_sub (hint z) (hint 0)]
  refine (abs_integral_le_integral_abs).trans ?_
  have hmaj : Integrable (fun t : ℝ => (2 * ‖z‖) ^ sH *
      (‖x - D.Ψ (t + z)‖ ^ (-sH) + ‖x - D.Ψ (t + 0)‖ ^ (-sH)) / sH) μ :=
    (((hintr z).add (hintr 0)).const_mul _).div_const _
  refine (integral_mono_ae ((hint z).sub (hint 0)).abs hmaj hlog).trans ?_
  rw [integral_div, integral_const_mul, integral_add (hintr z) (hintr 0)]
  have hz0 : 0 ≤ (2 * ‖z‖) ^ sH := by positivity
  calc (2 * ‖z‖) ^ sH * ((∫ t : ℝ, ‖x - D.Ψ ((t : ℂ) + z)‖ ^ (-sH) ∂μ) +
        ∫ t : ℝ, ‖x - D.Ψ ((t : ℂ) + 0)‖ ^ (-sH) ∂μ) / sH
      ≤ (2 * ‖z‖) ^ sH * (5 + 5) / sH :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hrz hr0) hz0) hs.le
    _ = 20 * (2 * ‖z‖) ^ sH := by rw [sH]; ring

theorem lip_invPath (hD : PsiLip D) : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1,
    1 / 2 * |t - t'| ≤ ‖invPath D t - invPath D t'‖ := fun t ht t' ht' => by
  have h := lip_shiftPath hD 0 t ht t' ht'
  simpa [invPath] using h

/-! ## The transported mollifications `τλ_n` -/

/-- `λ_n = bumpPath n segPath` -/
abbrev segBump (n : ℕ) : TestC := bumpPath n segPath

theorem transport_nonneg (g : TestC) (hg : ∀ y, 0 ≤ g y) (y : ℂ) : 0 ≤ D.transport g y := by
  rw [NIC.NearIdPair.transport_apply]
  exact mul_nonneg (D.jac_pos y).le (hg _)

theorem integrable_transport (g : TestC) : Integrable (D.transport g) :=
  (D.transport g).continuous.integrable_of_hasCompactSupport (D.transport g).hasCompactSupport

theorem integral_transport_segBump (n : ℕ) : ∫ y, D.transport (segBump n) y = 1 := by
  rw [D.integral_transport, integral_bumpPath]

/-- **`τλ_n dx = (λ * ψ_n) ∘ Ψ⁻¹`** -/
theorem withDensity_transport (n : ℕ) :
    volume.withDensity (fun y => ENNReal.ofReal (D.transport (segBump n) y)) =
      (moll n (pathMeas segPath)).map D.Ψ := by
  have : IsFiniteMeasure (volume.withDensity fun y =>
      ENNReal.ofReal (D.transport (segBump n) y)) :=
    isFiniteMeasure_withDensity_ofReal (integrable_transport _).hasFiniteIntegral
  have : IsFiniteMeasure ((moll n (pathMeas segPath)).map D.Ψ) := Measure.isFiniteMeasure_map _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_withDensity_eq_integral_toReal_smul
    (D.transport (segBump n)).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_map D.continuous_inv.aemeasurable f.continuous.aestronglyMeasurable]
  have e : ∀ y, (ENNReal.ofReal (D.transport (segBump n) y)).toReal • f y =
      D.transport (segBump n) y * f y := fun y => by
    rw [ENNReal.toReal_ofReal (transport_nonneg _ (bumpPath_nonneg n segPath) y), smul_eq_mul]
  simp_rw [e]
  rw [D.integral_transport_mul (segBump n) f, integral_mul_bumpPath n segPath fun y => f (D.Ψ y)]

/-- the potential of `τλ_n` -/
theorem logPot_transport (n : ℕ) (x : ℂ) :
    CircleAvg.logPot (D.transport (segBump n)) x =
      ∫ u, -Real.log ‖x - D.Ψ u‖ ∂moll n (pathMeas segPath) := by
  unfold CircleAvg.logPot
  calc ∫ y, -Real.log ‖x - y‖ * D.transport (segBump n) y
      = ∫ y, D.transport (segBump n) y * (fun y => -Real.log ‖x - y‖) y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        ring
    _ = ∫ u, segBump n u * -Real.log ‖x - D.Ψ u‖ := D.integral_transport_mul _ _
    _ = ∫ u, -Real.log ‖x - D.Ψ u‖ ∂moll n (pathMeas segPath) :=
        integral_mul_bumpPath n segPath fun u => -Real.log ‖x - D.Ψ u‖

theorem moll_segPath_univ (n : ℕ) : moll n (pathMeas segPath) univ = 1 := by
  rw [moll_univ, pathMeas_univ segPath.continuous.measurable]

theorem segPath_compl_closedBall : pathMeas segPath (closedBall (0 : ℂ) 1)ᶜ = 0 :=
  pathMeas_compl_eq_zero segPath.continuous.measurable measurableSet_closedBall fun t ht => by
    show (t : ℂ) ∈ closedBall (0 : ℂ) 1
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact ht.2

/-- the ball-mass bound of `(λ * ψ_n) ∘ Ψ⁻¹` -/
theorem ballBound_moll_map (hD : PsiLip D) (n : ℕ) :
    BallBound ((moll n (pathMeas segPath)).map D.Ψ) 4 1 := by
  intro u r hr _
  rw [Real.rpow_one]
  have hb : BallBound (moll n (pathMeas segPath)) (2 / 1) 1 := ballBound_moll ballBound_segPath
  have hsub : D.Ψ ⁻¹' ball u r ⊆ ball (D.Φ u) (2 * r) := by
    intro v hv
    rw [mem_preimage, mem_ball, dist_eq_norm] at hv
    rw [mem_ball, dist_eq_norm]
    have h1 := hD.anti v (D.Φ u)
    rw [D.left_inv] at h1
    linarith
  rw [Measure.map_apply D.continuous_inv.measurable measurableSet_ball]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (measure_mono hsub).trans ?_
  rcases le_or_gt (2 * r) 1 with h2 | h2
  · refine (hb.measure_ball_le _ (by positivity) h2).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_one]; linarith
  · calc moll n (pathMeas segPath) (ball (D.Φ u) (2 * r))
        ≤ moll n (pathMeas segPath) univ := measure_mono (subset_univ _)
      _ = 1 := moll_segPath_univ n
      _ ≤ ENNReal.ofReal (4 * r) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)

theorem moll_map_compl_closedBall (hD : PsiLip D) (n : ℕ) :
    ((moll n (pathMeas segPath)).map D.Ψ) (closedBall (0 : ℂ) (‖D.Ψ 0‖ + 4))ᶜ = 0 := by
  rw [Measure.map_apply D.continuous_inv.measurable measurableSet_closedBall.compl]
  refine measure_mono_null (fun v hv => ?_)
    (moll_compl_closedBall (m := n) segPath_compl_closedBall)
  simp only [mem_preimage, mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hv ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hD.lip v 0
  rw [sub_zero] at h1
  have h3 := norm_sub_norm_le (D.Ψ v) (D.Ψ 0)
  norm_num at hcon
  linarith

theorem integrable_neg_log_moll_map (hD : PsiLip D) (n : ℕ) (x : ℂ) :
    Integrable (fun y => -Real.log ‖x - y‖) ((moll n (pathMeas segPath)).map D.Ψ) :=
  (integrable_log_norm_sub (ballBound_moll_map hD n) one_pos (moll_map_compl_closedBall hD n) x).neg

theorem integrable_neg_log_comp (hD : PsiLip D) (n : ℕ) (x : ℂ) :
    Integrable (fun u => -Real.log ‖x - D.Ψ u‖) (moll n (pathMeas segPath)) :=
  (integrable_map_measure (measurable_neg_log_norm_sub x).aestronglyMeasurable
    D.continuous_inv.aemeasurable).mp (integrable_neg_log_moll_map hD n x)

theorem integrable_neg_log_mul_transport (hD : PsiLip D) (n : ℕ) (x : ℂ) :
    Integrable (fun y => -Real.log ‖x - y‖ * D.transport (segBump n) y) := by
  have hi := integrable_neg_log_moll_map hD n x
  rw [← withDensity_transport, integrable_withDensity_iff_integrable_smul'
    (D.transport (segBump n)).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi
  refine hi.congr (Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (transport_nonneg _ (bumpPath_nonneg n segPath) y), smul_eq_mul]
  ring

/-- `∫ −log|x − Ψ(w)| dλ(w)` over a shifted segment is the potential of the shifted path -/
theorem integral_segPath_shift (z x : ℂ) :
    ∫ w, -Real.log ‖x - D.Ψ (w + z)‖ ∂pathMeas segPath =
      logPotM (pathMeas fun t : ℝ => D.Ψ (t + z)) x := by
  have hm : Measurable fun w : ℂ => -Real.log ‖x - D.Ψ (w + z)‖ :=
    (measurable_neg_log_norm_sub x).comp
      (D.continuous_inv.comp (continuous_id.add continuous_const)).measurable
  rw [pathMeas, integral_map segPath.continuous.measurable.aemeasurable hm.aestronglyMeasurable,
    logPotM, pathMeas, integral_map (measurable_shiftPath z).aemeasurable
      (measurable_neg_log_norm_sub x).aestronglyMeasurable]
  rfl

/-- **The potential of `τλ_n` is within `20 (2·2^{-n})^{1/2}` of `U_{Ψ_*λ}`.** -/
theorem abs_logPot_transport_sub_le (hD : PsiLip D) (n : ℕ) (x : ℂ) :
    |CircleAvg.logPot (D.transport (segBump n)) x - logPotM (pathMeas (invPath D)) x| ≤
      20 * (2 * (2 : ℝ)⁻¹ ^ n) ^ sH := by
  rw [logPot_transport]
  have hm : Measurable fun u => -Real.log ‖x - D.Ψ u‖ :=
    (measurable_neg_log_norm_sub x).comp D.continuous_inv.measurable
  have hp : Integrable (fun p : ℂ × ℂ => -Real.log ‖x - D.Ψ (p.1 + p.2)‖)
      ((pathMeas segPath).prod (bumpLaw n)) :=
    (integrable_map_measure hm.aestronglyMeasurable measurable_add_pair.aemeasurable).mp
      (integrable_neg_log_comp hD n x)
  set A : ℂ → ℝ := fun z => logPotM (pathMeas fun t : ℝ => D.Ψ (t + z)) x with hA
  have e1 : ∫ u, -Real.log ‖x - D.Ψ u‖ ∂moll n (pathMeas segPath) = ∫ z, A z ∂bumpLaw n := by
    rw [moll, integral_map measurable_add_pair.aemeasurable hm.aestronglyMeasurable,
      integral_prod_symm _ hp]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact integral_segPath_shift z x
  have hAint : Integrable A (bumpLaw n) :=
    hp.integral_prod_right.congr (Eventually.of_forall fun z => integral_segPath_shift z x)
  have e2 : logPotM (pathMeas (invPath D)) x = A 0 := by rw [invPath_eq_shift]
  rw [e1, e2]
  have e3 : ∫ z, A z ∂bumpLaw n - A 0 = ∫ z, (A z - A 0) ∂bumpLaw n := by
    rw [integral_sub hAint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [e3, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 20 * (2 * (2 : ℝ)⁻¹ ^ n) ^ sH) ?_).trans
    (by rw [probReal_univ, mul_one])
  filter_upwards [ae_bumpLaw_norm_le n] with z hz
  rw [Real.norm_eq_abs]
  refine (abs_logPotM_shift_sub_le hD z x).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ (by norm_num [sH]))
    (by norm_num)
  linarith

/-! ## `⟨h, τλ_n⟩ − ⟨h, μ_n⟩ → 0` almost surely -/

/-- `τλ_n − μ_n` as a mean-zero test function -/
def transportDiff (D : NIC.NearIdPair) (n : ℕ) : TestC0 :=
  ⟨D.transport (segBump n) - bumpPath n (invPath D), by
    show ∫ y, (D.transport (segBump n) y - bumpPath n (invPath D) y) = 0
    rw [integral_sub (integrable_transport _) (integrable_bumpPath _ _),
      integral_transport_segBump, integral_bumpPath, sub_self]⟩

theorem logCov_transportDiff_le (hD : PsiLip D) (n : ℕ) :
    logCov (transportDiff D n).1 (transportDiff D n).1 ≤
      2 * (20 * 2 ^ sH + holdPath (invPath D) (1 / 2)) * ((2 : ℝ)⁻¹ ^ sH) ^ n := by
  have hcoe : ((transportDiff D n).1 : ℂ → ℝ) =
      fun y => D.transport (segBump n) y - bumpPath n (invPath D) y := rfl
  rw [hcoe]
  have hb := ballBound_invPath hD
  refine (logCov_sub_le (integrable_transport _) (integrable_bumpPath _ _)
    (integrable_neg_log_mul_transport hD n) (integrable_neg_log_mul_bumpPath (invPath D) hb n)
    (abs_logPot_transport_sub_le hD n) (abs_logPot_bumpPath_sub_le (invPath D) hb n)).trans ?_
  have hI : ∫ y, |D.transport (segBump n) y - bumpPath n (invPath D) y| ≤ 2 := by
    calc ∫ y, |D.transport (segBump n) y - bumpPath n (invPath D) y|
        ≤ ∫ y, (D.transport (segBump n) y + bumpPath n (invPath D) y) := by
          refine integral_mono ((integrable_transport _).sub (integrable_bumpPath _ _)).abs
            ((integrable_transport _).add (integrable_bumpPath _ _)) fun y => ?_
          have := transport_nonneg (D := D) (segBump n) (bumpPath_nonneg n segPath) y
          have := bumpPath_nonneg n (invPath D) y
          rw [abs_le]; constructor <;> linarith
      _ = 2 := by
          rw [integral_add (integrable_transport _) (integrable_bumpPath _ _),
            integral_transport_segBump, integral_bumpPath]; norm_num
  have hH : 0 ≤ holdPath (invPath D) (1 / 2) := by
    unfold holdPath
    exact div_nonneg (mul_nonneg zero_le_two (negMoment_nonneg hb (by norm_num [sH])
      (by norm_num [sH]))) (by norm_num [sH])
  have e : (2 * (2 : ℝ)⁻¹ ^ n) ^ sH = 2 ^ sH * ((2 : ℝ)⁻¹ ^ sH) ^ n := by
    rw [Real.mul_rpow (by norm_num) (by positivity), rpow_sH_pow]
  rw [e, rpow_sH_pow]
  have hq : 0 ≤ ((2 : ℝ)⁻¹ ^ sH) ^ n := by positivity
  have h2s : 0 ≤ (2 : ℝ) ^ sH := by positivity
  have hE : 0 ≤ 20 * (2 ^ sH * ((2 : ℝ)⁻¹ ^ sH) ^ n) + ((2 : ℝ)⁻¹ ^ sH) ^ n *
      holdPath (invPath D) (1 / 2) := by positivity
  calc (20 * (2 ^ sH * ((2 : ℝ)⁻¹ ^ sH) ^ n) + ((2 : ℝ)⁻¹ ^ sH) ^ n *
        holdPath (invPath D) (1 / 2)) *
        ∫ y, |D.transport (segBump n) y - bumpPath n (invPath D) y|
      ≤ (20 * (2 ^ sH * ((2 : ℝ)⁻¹ ^ sH) ^ n) + ((2 : ℝ)⁻¹ ^ sH) ^ n *
        holdPath (invPath D) (1 / 2)) * 2 := mul_le_mul_of_nonneg_left hI hE
    _ = 2 * (20 * 2 ^ sH + holdPath (invPath D) (1 / 2)) * ((2 : ℝ)⁻¹ ^ sH) ^ n := by ring

/-- **`lem:pairing-limits` (b) for the transported mollifications**: almost surely
`⟨h, τλ_n⟩ − ⟨h, μ_n⟩ → 0`. -/
theorem ae_tendsto_transport_sub (hD : PsiLip D) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => h ω (D.transport (segBump n)) - h ω (bumpPath n (invPath D)))
      atTop (𝓝 0) := by
  have := hh.gaussian.isProbabilityMeasure
  have hq0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ sH := by positivity
  have hq1 : (2 : ℝ)⁻¹ ^ sH < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num [sH])
  have hconv := CircleAvg.ae_tendsto_zero_of_sq_le (P := P)
    (Y := fun n ω => h ω (transportDiff D n).1)
    (C := 2 * (20 * 2 ^ sH + holdPath (invPath D) (1 / 2)))
    (fun n => (CircleAvg.integral_sq_pair hh (transportDiff D n)).1) hq0 hq1
    (fun n => by
      rw [(CircleAvg.integral_sq_pair hh (transportDiff D n)).2]
      exact logCov_transportDiff_le hD n)
  filter_upwards [hconv] with ω hω
  refine hω.congr fun n => ?_
  show h ω (D.transport (segBump n) - bumpPath n (invPath D)) = _
  rw [map_sub]

end pair

/-! ## Supports and the deterministic term `∫ K λ_n → ∫ K dλ` -/

/-- the closed rectangle `[-r, 1 + r] × [-r, r]` around `[0,1]` -/
def rectN (r : ℝ) : Set ℂ := Icc (-r) (1 + r) ×ℂ Icc (-r) r

theorem isCompact_rectN (r : ℝ) : IsCompact (rectN r) := isCompact_Icc.reProdIm isCompact_Icc

theorem mem_rectN {r : ℝ} {y : ℂ} : y ∈ rectN r ↔ y.re ∈ Icc (-r) (1 + r) ∧ y.im ∈ Icc (-r) r :=
  Complex.mem_reProdIm

theorem segPath_mem_rectN {r : ℝ} (hr : 0 ≤ r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    segPath t ∈ rectN r := by
  rw [mem_rectN]
  show (t : ℂ).re ∈ Icc (-r) (1 + r) ∧ (t : ℂ).im ∈ Icc (-r) r
  rw [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith, hr⟩⟩

theorem segBump_eq_zero {n : ℕ} {y : ℂ} (hy : y ∉ rectN ((2 : ℝ)⁻¹ ^ n)) : segBump n y = 0 := by
  rw [bumpPath_apply]
  have hr0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have hz : ∀ t ∈ uIcc (0 : ℝ) 1, bumpTest n (segPath t) y = 0 := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    apply CircleAvg.bumpTest_eq_zero_of_le
    show (2 : ℝ)⁻¹ ^ n ≤ dist y (t : ℂ)
    rw [dist_eq_norm]
    have hre := Complex.abs_re_le_norm (y - t)
    have him := Complex.abs_im_le_norm (y - t)
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    have a1 := neg_abs_le (y.re - t)
    have a2 := le_abs_self (y.re - t)
    have a3 := neg_abs_le y.im
    have a4 := le_abs_self y.im
    rw [mem_rectN, not_and_or] at hy
    rcases hy with h | h
    · rw [mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h <;> linarith [ht.1, ht.2]
    · rw [mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h <;> linarith
  rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]

theorem tsupport_segBump (n : ℕ) : tsupport (segBump n : ℂ → ℝ) ⊆ rectN ((2 : ℝ)⁻¹ ^ n) :=
  closure_minimal (fun y hy => by
    by_contra hn
    exact hy (segBump_eq_zero hn)) (isCompact_rectN _).isClosed

theorem neg_le_one_add {r : ℝ} (hr : 0 ≤ r) : -r ≤ 1 + r := by linarith

theorem neg_le_self' {r : ℝ} (hr : 0 ≤ r) : -r ≤ r := by linarith

/-- the projection of `ℂ` onto `rectN r` -/
def clampN (r : ℝ) (hr : 0 ≤ r) (y : ℂ) : ℂ :=
  ((projIcc (-r) (1 + r) (neg_le_one_add hr) y.re : ℝ) : ℂ) +
    ((projIcc (-r) r (neg_le_self' hr) y.im : ℝ) : ℂ) * Complex.I

theorem clampN_re {r : ℝ} (hr : 0 ≤ r) (y : ℂ) :
    (clampN r hr y).re = projIcc (-r) (1 + r) (neg_le_one_add hr) y.re := by
  simp [clampN]

theorem clampN_im {r : ℝ} (hr : 0 ≤ r) (y : ℂ) :
    (clampN r hr y).im = projIcc (-r) r (neg_le_self' hr) y.im := by
  simp [clampN]

theorem clampN_mem {r : ℝ} (hr : 0 ≤ r) (y : ℂ) : clampN r hr y ∈ rectN r := by
  rw [mem_rectN, clampN_re, clampN_im]
  exact ⟨(projIcc (-r) (1 + r) (neg_le_one_add hr) y.re).2,
    (projIcc (-r) r (neg_le_self' hr) y.im).2⟩

theorem clampN_of_mem {r : ℝ} (hr : 0 ≤ r) {y : ℂ} (hy : y ∈ rectN r) : clampN r hr y = y := by
  rw [mem_rectN] at hy
  apply Complex.ext
  · rw [clampN_re, projIcc_of_mem _ hy.1]
  · rw [clampN_im, projIcc_of_mem _ hy.2]

theorem continuous_clampN {r : ℝ} (hr : 0 ≤ r) : Continuous (clampN r hr) := by
  unfold clampN
  refine (Complex.continuous_ofReal.comp (continuous_subtype_val.comp
    (continuous_projIcc.comp Complex.continuous_re))).add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp
      (continuous_projIcc.comp Complex.continuous_im))).mul continuous_const)

theorem abs_projIcc_sub_le {a b : ℝ} (h : a ≤ b) (x y : ℝ) :
    |(projIcc a b h x : ℝ) - projIcc a b h y| ≤ |x - y| := by
  have := (LipschitzWith.projIcc h).dist_le_mul x y
  rw [Subtype.dist_eq, Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this
  exact this

theorem dist_clampN_le {r : ℝ} (hr : 0 ≤ r) (y y' : ℂ) :
    dist (clampN r hr y) (clampN r hr y') ≤ dist y y' := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im, clampN_re, clampN_re, clampN_im, clampN_im]
  refine Real.sqrt_le_sqrt ?_
  have h1 := abs_projIcc_sub_le (neg_le_one_add hr) y.re y'.re
  have h2 := abs_projIcc_sub_le (neg_le_self' hr) y.im y'.im
  have s1 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have s2 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
  rw [sq_abs] at s1 s2
  linarith

/-- mollification converges for bounded uniformly continuous functions -/
theorem tendsto_integral_moll {ρ : Measure ℂ} [IsFiniteMeasure ρ] {F : ℂ → ℝ} (hF : Continuous F)
    (hFu : UniformContinuous F) {M : ℝ} (hM : ∀ y, |F y| ≤ M) :
    Tendsto (fun n => ∫ y, F y ∂moll n ρ) atTop (𝓝 (∫ y, F y ∂ρ)) := by
  have hbint : ∀ μ : Measure ℂ, IsFiniteMeasure μ → Integrable F μ := fun μ _ =>
    (integrable_const M).mono' hF.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y)
  have hinner : ∀ n, Integrable (fun x => ∫ y, F (x + y) ∂bumpLaw n) ρ := by
    intro n
    refine (integrable_const M).mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((hF.comp continuous_add).stronglyMeasurable.integral_prod_right'
        (ν := bumpLaw n)).aestronglyMeasurable
    · refine (norm_integral_le_of_norm_le_const (C := M) (ae_of_all _ fun y => ?_)).trans
        (by rw [probReal_univ, mul_one])
      rw [Real.norm_eq_abs]; exact hM _
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (ρ.real univ + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformContinuous_iff.mp hFu ε' hε'0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun n hn => ?_⟩
  rw [integral_moll hF.measurable (hbint _ inferInstance), Real.dist_eq,
    ← integral_sub (hinner n) (hbint ρ inferInstance)]
  have hpt : ∀ x, |∫ y, F (x + y) ∂bumpLaw n - F x| ≤ ε' := by
    intro x
    rw [← Real.norm_eq_abs]
    have e : ∫ y, F (x + y) ∂bumpLaw n - F x = ∫ y, (F (x + y) - F x) ∂bumpLaw n := by
      have hix : Integrable (fun y => F (x + y)) (bumpLaw n) :=
        (integrable_const M).mono' (hF.comp (continuous_const.add continuous_id)).aestronglyMeasurable
          (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM _)
      rw [integral_sub hix (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [e]
    refine (norm_integral_le_of_norm_le_const (C := ε') ?_).trans (by rw [probReal_univ, mul_one])
    filter_upwards [ae_bumpLaw_norm_le n] with y hy
    rw [← dist_eq_norm]
    refine (hFδ ?_).le
    rw [dist_eq_norm, add_sub_cancel_left]
    calc ‖y‖ ≤ (2 : ℝ)⁻¹ ^ n := hy
      _ ≤ (2 : ℝ)⁻¹ ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ < δ := hN
  calc |∫ x, (∫ y, F (x + y) ∂bumpLaw n - F x) ∂ρ|
      ≤ ε' * ρ.real univ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs]; exact hpt x)
    _ < ε := by
        rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        have := measureReal_nonneg (μ := ρ) (s := univ)
        nlinarith

/-- **`∫ K λ_n → ∫ K dλ`** for `K` continuous on a closed rectangle around `[0,1]` -/
theorem tendsto_integral_mul_segBump {K : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hK : ContinuousOn K (rectN r)) :
    Tendsto (fun n => ∫ y, K y * segBump n y) atTop (𝓝 (∫ w, K w ∂pathMeas segPath)) := by
  set Kt : ℂ → ℝ := fun y => K (clampN r hr.le y) with hKt
  have hKtc : Continuous Kt := hK.comp_continuous (continuous_clampN hr.le) (clampN_mem hr.le)
  obtain ⟨M, hM⟩ := (isCompact_rectN r).exists_bound_of_continuousOn hK
  have hKtM : ∀ y, |Kt y| ≤ M := fun y => by
    rw [← Real.norm_eq_abs]; exact hM _ (clampN_mem hr.le y)
  have hKtu : UniformContinuous Kt := by
    have hu := (isCompact_rectN r).uniformContinuousOn_of_continuous hK
    rw [Metric.uniformContinuousOn_iff] at hu
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hu ε hε
    exact ⟨δ, hδ, fun {a b} hab => h _ (clampN_mem hr.le a) _ (clampN_mem hr.le b)
      ((dist_clampN_le hr.le a b).trans_lt hab)⟩
  have hlim := tendsto_integral_moll (ρ := pathMeas segPath) hKtc hKtu hKtM
  have hend : ∫ w, Kt w ∂pathMeas segPath = ∫ w, K w ∂pathMeas segPath := by
    refine integral_congr_ae ?_
    filter_upwards [ae_pathMeas_mem segPath.continuous.measurable (isCompact_rectN r).isClosed.measurableSet
      (fun t ht => segPath_mem_rectN hr.le ht)] with w hw
    show K (clampN r hr.le w) = K w
    rw [clampN_of_mem hr.le hw]
  rw [hend] at hlim
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← integral_mul_bumpPath]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show segBump n y * Kt y = K y * segBump n y
  by_cases hy : y ∈ rectN r
  · rw [hKt]; dsimp only; rw [clampN_of_mem hr.le hy, mul_comm]
  · have hle : (2 : ℝ)⁻¹ ^ n ≤ r :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans hN.le
    have hy' : y ∉ rectN ((2 : ℝ)⁻¹ ^ n) := fun h => hy (by
      rw [mem_rectN] at h ⊢
      exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, ⟨by linarith [h.2.1], by linarith [h.2.2]⟩⟩)
    rw [segBump_eq_zero hy', zero_mul, mul_zero]

/-! ## (b5) -/

/-- **The pairing identity (b5)**: if almost surely `⟨h, τλ_n⟩ = ⟨h̄, λ_n⟩ + ∫ K λ_n` for all large
`n`, with `K` continuous on a closed rectangle around `[0,1]`, then almost surely
`measPairing(h̄, λ) = measPairing(h, Ψ_*λ) − ∫ K dλ`. -/
theorem ae_measPairing_eq {D : NIC.NearIdPair} (hD : PsiLip D) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h hbar : Ω → DistC} {K : Ω → ℂ → ℝ} (hh : IsWholePlaneGFF h P)
    (hhb : IsWholePlaneGFF hbar P) {r : ℝ} (hr : 0 < r) (hK : ∀ ω, ContinuousOn (K ω) (rectN r))
    (hcoup : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      h ω (D.transport (segBump n)) = hbar ω (segBump n) + ∫ y, K ω y * segBump n y) :
    ∀ᵐ ω ∂P, GaussianLQG.measPairing (hbar ω) (pathMeas segPath) =
      GaussianLQG.measPairing (h ω) (pathMeas (invPath D)) - ∫ w, K ω w ∂pathMeas segPath := by
  filter_upwards [hcoup, ae_tendsto_bumpPath segPath hhb one_pos lip_segPath,
    ae_tendsto_bumpPath (invPath D) hh (by norm_num : (0 : ℝ) < 1 / 2) (lip_invPath hD),
    ae_tendsto_transport_sub hD hh] with ω hc h1 h2 h3
  have hA : Tendsto (fun n => h ω (D.transport (segBump n))) atTop
      (𝓝 (GaussianLQG.measPairing (hbar ω) (pathMeas segPath) +
        ∫ w, K ω w ∂pathMeas segPath)) :=
    (h1.add (tendsto_integral_mul_segBump hr (hK ω))).congr' (hc.mono fun n hn => hn.symm)
  have hB : Tendsto (fun n => h ω (D.transport (segBump n))) atTop
      (𝓝 (GaussianLQG.measPairing (h ω) (pathMeas (invPath D)))) := by
    have := h2.add h3
    rw [add_zero] at this
    refine this.congr fun n => ?_
    ring
  have := tendsto_nhds_unique hA hB
  linarith

end Coupling42

end SmallGammaGeodesics

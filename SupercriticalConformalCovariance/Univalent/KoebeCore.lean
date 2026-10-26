import QuantumZipper.Proofs.Complex.KoebeDistortion
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.LocallyUniformLimit

noncomputable section

open Set Metric
open scoped Topology

namespace SupercriticalConformalCovariance.Univalent

private abbrev C : ℝ := 16 * QuantumZipper.CA.Koebe.koebeDistExp *
  QuantumZipper.CA.Koebe.koebeGrowthConst

/-- A quantitative form of the normalized Koebe limit, valid on one quarter of the disk. -/
theorem normalized_deriv_bound {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball 0 r)) (hinj : InjOn f (ball 0 r))
    (hderiv : deriv f 0 = 1) {z : ℂ} (hz : ‖z‖ ≤ r / 4) :
    ‖deriv f z - 1‖ ≤ C * ‖z‖ / r := by
  have hquarter : closedBall (0 : ℂ) (r / 4) ⊆ ball 0 r := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have hw' : ‖w‖ ≤ r / 4 := by simpa only [mem_closedBall, dist_zero_right] using hw
    linarith
  have hdiff : ∀ w ∈ closedBall (0 : ℂ) (r / 4),
      DifferentiableAt ℂ (deriv f) w := by
    intro w hw
    exact (hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds (hquarter hw))
  have hbound : ∀ w ∈ closedBall (0 : ℂ) (r / 4),
      ‖deriv (deriv f) w‖ ≤ C / r := by
    intro w hw
    have hzw : dist w 0 ≤ r / 4 := by simpa only [mem_closedBall] using hw
    have hsub : ball w (r / 2) ⊆ ball 0 r := by
      apply ball_subset_ball'
      linarith
    have hfirst : ‖deriv f w‖ ≤ 8 * QuantumZipper.CA.Koebe.koebeGrowthConst := by
      have h := QuantumZipper.CA.Koebe.norm_deriv_le_of_dist_le_half hd hinj hr
        (show dist w 0 ≤ r / 2 by linarith)
      simpa only [hderiv, norm_one, mul_one] using h
    have hsecond := QuantumZipper.CA.Koebe.mul_norm_deriv2_le
      (hd.mono hsub) (hinj.mono hsub) (show 0 < r / 2 by positivity)
    have : r / 2 * ‖deriv (deriv f) w‖ ≤
        QuantumZipper.CA.Koebe.koebeDistExp * ‖deriv f w‖ := hsecond
    dsimp [C]
    have hp : 0 ≤ QuantumZipper.CA.Koebe.koebeDistExp :=
      QuantumZipper.CA.Koebe.koebeDistExp_pos.le
    apply (le_div_iff₀ hr).2
    nlinarith [mul_le_mul_of_nonneg_left hfirst hp]
  have h0 : (0 : ℂ) ∈ closedBall 0 (r / 4) := mem_closedBall_self (by positivity)
  have hz' : z ∈ closedBall 0 (r / 4) := by simpa only [mem_closedBall, dist_zero_right] using hz
  have h := (convex_closedBall (0 : ℂ) (r / 4)).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound h0 hz'
  calc
    ‖deriv f z - 1‖ ≤ C / r * ‖z‖ := by simpa only [hderiv, sub_zero] using h
    _ = C * ‖z‖ / r := by ring

/-- Quantitative normalized-map estimate on the inner quarter disk. -/
theorem normalized_map_bound {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball 0 r)) (hinj : InjOn f (ball 0 r))
    (hzero : f 0 = 0) (hderiv : deriv f 0 = 1)
    {z : ℂ} (hz : ‖z‖ ≤ r / 4) :
    ‖f z - z‖ ≤ C * ‖z‖ ^ 2 / r := by
  let g : ℂ → ℂ := fun w => f w - w
  have hsub : closedBall (0 : ℂ) ‖z‖ ⊆ ball 0 r := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have hw' : ‖w‖ ≤ ‖z‖ := by simpa only [mem_closedBall, dist_zero_right] using hw
    linarith
  have hdiff : ∀ w ∈ closedBall (0 : ℂ) ‖z‖, DifferentiableAt ℂ g w := by
    intro w hw
    exact (hd.differentiableAt (isOpen_ball.mem_nhds (hsub hw))).sub differentiableAt_id
  have hbound : ∀ w ∈ closedBall (0 : ℂ) ‖z‖,
      ‖deriv g w‖ ≤ C * ‖z‖ / r := by
    intro w hw
    have hzw : ‖w‖ ≤ ‖z‖ := by simpa only [mem_closedBall, dist_zero_right] using hw
    have hqw : ‖w‖ ≤ r / 4 := hzw.trans hz
    have h := normalized_deriv_bound hr hd hinj hderiv hqw
    have hg : deriv g w = deriv f w - 1 := by
      exact (deriv_fun_sub (hd.differentiableAt (isOpen_ball.mem_nhds (hsub hw)))
        differentiableAt_id).trans (by simp)
    rw [hg]
    exact h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hzw (by
        dsimp [C]
        exact mul_nonneg (mul_nonneg (by norm_num)
          QuantumZipper.CA.Koebe.koebeDistExp_pos.le)
          QuantumZipper.CA.Koebe.koebeGrowthConst_pos.le)) hr.le)
  have h0 : (0 : ℂ) ∈ closedBall 0 ‖z‖ := mem_closedBall_self (norm_nonneg _)
  have hz' : z ∈ closedBall 0 ‖z‖ := by simp
  have h := (convex_closedBall (0 : ℂ) ‖z‖).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound h0 hz'
  dsimp [g] at h
  rw [hzero, sub_zero, sub_zero, norm_sub_rev] at h
  calc
    ‖f z - z‖ ≤ (C * ‖z‖ / r) * ‖z‖ := by simpa only [norm_sub_rev, sub_zero] using h
    _ = C * ‖z‖ ^ 2 / r := by ring

/-- Normalized univalent maps on expanding disks converge locally uniformly to the identity. -/
theorem normalized_maps_tendsto {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hzero : ∀ n, f n 0 = 0) (hderiv : ∀ n, deriv (f n) 0 = 1) :
    TendstoLocallyUniformlyOn f id Filter.atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R, hRpos, hRK⟩ := hK.isBounded.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hs : ∀ᶠ n in Filter.atTop, C * R ^ 2 / r n < ε := by
    have ht := hrLarge.const_div_atTop (C * R ^ 2)
    exact ht.eventually (Iio_mem_nhds hε)
  filter_upwards [hrLarge.eventually_gt_atTop (4 * R), hs] with n hn hs z hz
  have hzR : ‖z‖ ≤ R := hRK z hz
  have hzr : ‖z‖ ≤ r n / 4 := by linarith
  have h := normalized_map_bound (hr n) (hd n) (hinj n) (hzero n) (hderiv n) hzr
  have hpow : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num)
      QuantumZipper.CA.Koebe.koebeDistExp_pos.le)
      QuantumZipper.CA.Koebe.koebeGrowthConst_pos.le
  have hle : C * ‖z‖ ^ 2 / r n ≤ C * R ^ 2 / r n := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (hr n).le
  have : ‖f n z - z‖ < ε := (h.trans hle).trans_lt hs
  simpa only [Function.id_def, dist_eq_norm, norm_sub_rev] using this

/-- First derivatives of normalized univalent maps converge locally uniformly to one. -/
theorem normalized_derivs_tendsto {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hderiv : ∀ n, deriv (f n) 0 = 1) :
    TendstoLocallyUniformlyOn (fun n => deriv (f n)) (fun _ => 1)
      Filter.atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R, hRpos, hRK⟩ := hK.isBounded.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hs : ∀ᶠ n in Filter.atTop, C * R / r n < ε := by
    have ht := hrLarge.const_div_atTop (C * R)
    exact ht.eventually (Iio_mem_nhds hε)
  filter_upwards [hrLarge.eventually_gt_atTop (4 * R), hs] with n hn hs z hz
  have hzR : ‖z‖ ≤ R := hRK z hz
  have hzr : ‖z‖ ≤ r n / 4 := by linarith
  have h := normalized_deriv_bound (hr n) (hd n) (hinj n) (hderiv n) hzr
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num)
      QuantumZipper.CA.Koebe.koebeDistExp_pos.le)
      QuantumZipper.CA.Koebe.koebeGrowthConst_pos.le
  have hle : C * ‖z‖ / r n ≤ C * R / r n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzR hC) (hr n).le
  have : ‖deriv (f n) z - 1‖ < ε := (h.trans hle).trans_lt hs
  simpa only [dist_eq_norm, norm_sub_rev] using this

/-- Each fixed derivative order converges on every fixed disk. -/
theorem normalized_iteratedDeriv_tendsto_on_ball {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hzero : ∀ n, f n 0 = 0) (hderiv : ∀ n, deriv (f n) 0 = 1)
    (S : ℝ) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (f n))
      (iteratedDeriv k id) Filter.atTop (ball 0 S) := by
  have hiter : ∀ n k, DifferentiableOn ℂ (iteratedDeriv k (f n)) (ball 0 (r n)) := by
    intro n k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hd n
    | succ k ih =>
      simpa only [iteratedDeriv_succ] using ih.deriv isOpen_ball
  induction k with
  | zero =>
      simpa only [iteratedDeriv_zero] using
        (normalized_maps_tendsto hr hrLarge hd hinj hzero hderiv).mono (subset_univ _)
  | succ k ih =>
      have hev : ∀ᶠ n in Filter.atTop,
          DifferentiableOn ℂ (iteratedDeriv k (f n)) (ball 0 S) := by
        filter_upwards [hrLarge.eventually_gt_atTop S] with n hn
        exact (hiter n k).mono (ball_subset_ball hn.le)
      simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hev isOpen_ball

/-- Cauchy estimates upgrade local uniform holomorphic convergence to each fixed derivative order. -/
theorem iteratedDeriv_tendsto_on_ball {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : TendstoLocallyUniformlyOn F g Filter.atTop Set.univ)
    (hlocal : ∀ S : ℝ, ∀ᶠ n in Filter.atTop,
      DifferentiableOn ℂ (F n) (ball 0 S))
    (S : ℝ) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n))
      (iteratedDeriv k g) Filter.atTop (ball 0 S) := by
  have hiter : ∀ (n k : ℕ), DifferentiableOn ℂ (F n) (ball 0 S) →
      DifferentiableOn ℂ (iteratedDeriv k (F n)) (ball 0 S) := by
    intro n j hj
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using hj
    | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv isOpen_ball
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hF.mono (subset_univ _)
  | succ k ih =>
      have hev : ∀ᶠ n in Filter.atTop,
          DifferentiableOn ℂ (iteratedDeriv k (F n)) (ball 0 S) := by
        filter_upwards [hlocal S] with n hn
        exact hiter n k hn
      simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hev isOpen_ball

/-- The local inverse maps and their derivatives converge on compact sets. -/
theorem normalized_inverse_core {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hzero : ∀ n, f n 0 = 0) (hderiv : ∀ n, deriv (f n) 0 = 1) :
    TendstoLocallyUniformlyOn
      (fun n => Function.invFunOn (f n) (ball 0 (r n))) id Filter.atTop Set.univ ∧
    TendstoLocallyUniformlyOn
      (fun n => deriv (Function.invFunOn (f n) (ball 0 (r n)))) (fun _ => 1)
      Filter.atTop Set.univ := by
  let g : ℕ → ℂ → ℂ := fun n => Function.invFunOn (f n) (ball 0 (r n))
  let ρ : ℕ → ℝ := fun n => QuantumZipper.CA.Koebe.koebeCovConst * r n
  have hρpos : ∀ n, 0 < ρ n := fun n => mul_pos
    QuantumZipper.CA.Koebe.koebeCovConst_pos (hr n)
  have hρLarge : Filter.Tendsto ρ Filter.atTop Filter.atTop :=
    hrLarge.const_mul_atTop QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hcover : ∀ n, ball 0 (ρ n) ⊆ (f n) '' ball 0 (r n) := by
    intro n
    have h := QuantumZipper.CA.Koebe.ball_subset_image_koebe (hd n) (hinj n)
    simpa only [hzero n, hderiv n, norm_one, mul_one] using h
  have hgd : ∀ n, DifferentiableOn ℂ (g n) (ball 0 (ρ n)) := by
    intro n w hw
    obtain ⟨z, hz, rfl⟩ := hcover n hw
    exact (QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
      isOpen_ball (hd n) (hinj n) hz).differentiableAt.differentiableWithinAt
  have hgi : ∀ n, InjOn (g n) (ball 0 (ρ n)) := by
    intro n
    exact (Function.invFunOn_injOn_image (f n) (ball 0 (r n))).mono (hcover n)
  have hgzero : ∀ n, g n 0 = 0 := by
    intro n
    have hz : (0 : ℂ) ∈ ball 0 (r n) := mem_ball_self (hr n)
    have hx : ∃ z ∈ ball 0 (r n), f n z = 0 := ⟨0, hz, hzero n⟩
    exact (hinj n (Function.invFunOn_mem hx) hz
      ((Function.invFunOn_eq hx).trans (hzero n).symm))
  have hgderiv : ∀ n, deriv (g n) 0 = 1 := by
    intro n
    have hz : (0 : ℂ) ∈ ball 0 (r n) := mem_ball_self (hr n)
    have h := QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
      isOpen_ball (hd n) (hinj n) hz
    rw [hzero n, hderiv n] at h
    simpa only [inv_one] using h.deriv
  exact ⟨normalized_maps_tendsto hρpos hρLarge hgd hgi hgzero hgderiv,
    normalized_derivs_tendsto hρpos hρLarge hgd hgi hgderiv⟩

theorem normalized_inverses_tendsto {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hzero : ∀ n, f n 0 = 0) (hderiv : ∀ n, deriv (f n) 0 = 1) :
    TendstoLocallyUniformlyOn
      (fun n => Function.invFunOn (f n) (ball 0 (r n))) id Filter.atTop Set.univ :=
  (normalized_inverse_core hr hrLarge hd hinj hzero hderiv).1

/-- The normalized local inverses converge with every fixed derivative order. -/
theorem normalized_inverse_iteratedDeriv_tendsto_on_ball
    {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ} (S : ℝ) (k : ℕ)
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hzero : ∀ n, f n 0 = 0) (hderiv : ∀ n, deriv (f n) 0 = 1) :
    TendstoLocallyUniformlyOn
      (fun n => iteratedDeriv k (Function.invFunOn (f n) (ball 0 (r n))))
      (iteratedDeriv k id) Filter.atTop (ball 0 S) := by
  let ρ : ℕ → ℝ := fun n => QuantumZipper.CA.Koebe.koebeCovConst * r n
  have hρLarge : Filter.Tendsto ρ Filter.atTop Filter.atTop :=
    hrLarge.const_mul_atTop QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hlocal : ∀ T : ℝ, ∀ᶠ n in Filter.atTop,
      DifferentiableOn ℂ (Function.invFunOn (f n) (ball 0 (r n))) (ball 0 T) := by
    intro T
    filter_upwards [hρLarge.eventually_gt_atTop T] with n hn w hw
    have hk := QuantumZipper.CA.Koebe.ball_subset_image_koebe (hd n) (hinj n)
    have hcover : ball 0 (ρ n) ⊆ (f n) '' ball 0 (r n) := by
      simpa only [hzero n, hderiv n, norm_one, mul_one] using hk
    have hwρ : w ∈ ball 0 (ρ n) := (ball_subset_ball hn.le) hw
    obtain ⟨z, hz, rfl⟩ := hcover hwρ
    exact (QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
      isOpen_ball (hd n) (hinj n) hz).differentiableAt.differentiableWithinAt
  exact iteratedDeriv_tendsto_on_ball
    (normalized_inverses_tendsto hr hrLarge hd hinj hzero hderiv) hlocal S k

theorem normalized_inverse_derivs_tendsto {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hzero : ∀ n, f n 0 = 0) (hderiv : ∀ n, deriv (f n) 0 = 1) :
    TendstoLocallyUniformlyOn
      (fun n => deriv (Function.invFunOn (f n) (ball 0 (r n)))) (fun _ => 1)
      Filter.atTop Set.univ :=
  (normalized_inverse_core hr hrLarge hd hinj hzero hderiv).2

/-- A nonzero local uniform limit has a locally uniform logarithmic norm limit. -/
theorem log_norm_tendsto_of_nonzero {F : ℕ → ℂ → ℂ} {b : ℂ} (hb : b ≠ 0)
    (hF : TendstoLocallyUniformlyOn F (fun _ => b) Filter.atTop Set.univ) :
    TendstoLocallyUniformlyOn (fun n z => Real.log ‖F n z‖) (fun _ => Real.log ‖b‖)
      Filter.atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  have hFK : TendstoUniformlyOn F (fun _ => b) Filter.atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hF K
      (subset_univ _) hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc : ContinuousAt (fun z : ℂ => Real.log ‖z‖) b := by
    exact (Real.continuousAt_log (norm_ne_zero_iff.mpr hb)).comp
      continuous_norm.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hc ε hε
  have hs := (Metric.tendstoUniformlyOn_iff.mp hFK) δ hδpos
  filter_upwards [hs] with n hn z hz
  have h := hδ (show dist (F n z) b < δ by simpa only [dist_comm] using hn z hz)
  simpa only [dist_comm] using h

theorem log_norm_tendsto_of_one {F : ℕ → ℂ → ℂ}
    (hF : TendstoLocallyUniformlyOn F (fun _ => (1 : ℂ)) Filter.atTop Set.univ) :
    TendstoLocallyUniformlyOn (fun n z => Real.log ‖F n z‖) (fun _ => 0)
      Filter.atTop Set.univ := by
  simpa only [norm_one, Real.log_one] using
    log_norm_tendsto_of_nonzero (show (1 : ℂ) ≠ 0 by norm_num) hF

theorem normalized_log_derivs_tendsto {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hderiv : ∀ n, deriv (f n) 0 = 1) :
    TendstoLocallyUniformlyOn (fun n z => Real.log ‖deriv (f n) z‖)
      (fun _ => 0) Filter.atTop Set.univ :=
  log_norm_tendsto_of_one (normalized_derivs_tendsto hr hrLarge hd hinj hderiv)

theorem normalized_inverse_log_derivs_tendsto {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hzero : ∀ n, f n 0 = 0) (hderiv : ∀ n, deriv (f n) 0 = 1) :
    TendstoLocallyUniformlyOn
      (fun n z => Real.log ‖deriv (Function.invFunOn (f n) (ball 0 (r n))) z‖)
      (fun _ => 0) Filter.atTop Set.univ :=
  log_norm_tendsto_of_one
    (normalized_inverse_derivs_tendsto hr hrLarge hd hinj hzero hderiv)

/-- A varying affine factor can be restored after normalized convergence. -/
theorem scaled_normalized_maps_tendsto {f : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    {a : ℕ → ℂ} {a₀ : ℂ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (f n) (ball 0 (r n)))
    (hzero : ∀ n, f n 0 = 0) (hderiv : ∀ n, deriv (f n) 0 = 1)
    (ha : Filter.Tendsto a Filter.atTop (nhds a₀)) :
    TendstoLocallyUniformlyOn (fun n z => a n * f n z) (fun z => a₀ * z)
      Filter.atTop Set.univ := by
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => a n)
      (fun _ => a₀) Filter.atTop Set.univ :=
    ha.tendstoUniformlyOn_const Set.univ |>.tendstoLocallyUniformlyOn
  have h := hconst.mul₀ (normalized_maps_tendsto hr hrLarge hd hinj hzero hderiv)
    continuousOn_const continuousOn_id
  convert h using 1
  · funext n z; rfl
  · funext z; rfl

/-- An univalent sequence on expanding centered disks has the affine limit set by its derivative. -/
theorem univalent_maps_tendsto {ψ : ℕ → ℂ → ℂ} {r : ℕ → ℝ} {a : ℂ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (ψ n) (ball 0 (r n)))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a)) :
    TendstoLocallyUniformlyOn ψ (fun z => a * z) Filter.atTop Set.univ := by
  let b : ℕ → ℂ := fun n => deriv (ψ n) 0
  have hb : ∀ n, b n ≠ 0 := by
    intro n
    exact QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball (hd n) (hinj n)
      (mem_ball_self (hr n))
  let f : ℕ → ℂ → ℂ := fun n z => ψ n z / b n
  have hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)) := by
    intro n
    exact (hd n).div_const _
  have hfi : ∀ n, InjOn (f n) (ball 0 (r n)) := by
    intro n x hx y hy hxy
    apply hinj n hx hy
    exact (div_left_inj' (hb n)).mp hxy
  have hfzero : ∀ n, f n 0 = 0 := by
    intro n
    simp only [f, hzero, zero_div]
  have hfderiv : ∀ n, deriv (f n) 0 = 1 := by
    intro n
    simp only [f, deriv_div_const, b, div_self (hb n)]
  have h := scaled_normalized_maps_tendsto hr hrLarge hfd hfi hfzero hfderiv ha
  convert h using 1
  · funext n z
    dsimp [f, b]
    exact (mul_div_cancel₀ _ (hb n)).symm

/-- Derivatives of univalent maps on expanding disks converge to the affine slope. -/
theorem univalent_derivs_tendsto {ψ : ℕ → ℂ → ℂ} {r : ℕ → ℝ} {a : ℂ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (ψ n) (ball 0 (r n)))
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a)) :
    TendstoLocallyUniformlyOn (fun n z => deriv (ψ n) z) (fun _ => a)
      Filter.atTop Set.univ := by
  let b : ℕ → ℂ := fun n => deriv (ψ n) 0
  have hb : ∀ n, b n ≠ 0 := by
    intro n
    exact QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball (hd n) (hinj n)
      (mem_ball_self (hr n))
  let f : ℕ → ℂ → ℂ := fun n z => ψ n z / b n
  have hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 (r n)) := by
    intro n
    exact (hd n).div_const _
  have hfi : ∀ n, InjOn (f n) (ball 0 (r n)) := by
    intro n x hx y hy hxy
    apply hinj n hx hy
    exact (div_left_inj' (hb n)).mp hxy
  have hfderiv : ∀ n, deriv (f n) 0 = 1 := by
    intro n
    simp only [f, deriv_div_const, b, div_self (hb n)]
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => b n)
      (fun _ => a) Filter.atTop Set.univ :=
    ha.tendstoUniformlyOn_const Set.univ |>.tendstoLocallyUniformlyOn
  have h := hconst.mul₀ (normalized_derivs_tendsto hr hrLarge hfd hfi hfderiv)
    continuousOn_const continuousOn_const
  convert h using 1
  · funext n z
    dsimp [f, b]
    rw [deriv_div_const]
    exact (mul_div_cancel₀ _ (hb n)).symm
  · funext z; simp

/-- The inverses and their derivatives converge to the inverse limiting dilation. -/
theorem univalent_inverse_core {ψ : ℕ → ℂ → ℂ} {r : ℕ → ℝ} {a : ℂ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (ψ n) (ball 0 (r n)))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a))
    (ha0 : a ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n => Function.invFunOn (ψ n) (ball 0 (r n)))
      (fun z => a⁻¹ * z) Filter.atTop Set.univ ∧
    TendstoLocallyUniformlyOn
      (fun n z => deriv (Function.invFunOn (ψ n) (ball 0 (r n))) z)
      (fun _ => a⁻¹) Filter.atTop Set.univ := by
  let g : ℕ → ℂ → ℂ := fun n => Function.invFunOn (ψ n) (ball 0 (r n))
  let ρ : ℕ → ℝ := fun n =>
    QuantumZipper.CA.Koebe.koebeCovConst * (r n * ‖deriv (ψ n) 0‖)
  have hψderiv : ∀ n, deriv (ψ n) 0 ≠ 0 := by
    intro n
    exact QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball (hd n) (hinj n)
      (mem_ball_self (hr n))
  have hρpos : ∀ n, 0 < ρ n := by
    intro n
    exact mul_pos QuantumZipper.CA.Koebe.koebeCovConst_pos
      (mul_pos (hr n) (norm_pos_iff.mpr (hψderiv n)))
  have hρLarge : Filter.Tendsto ρ Filter.atTop Filter.atTop := by
    have hnorm : Filter.Tendsto (fun n => ‖deriv (ψ n) 0‖)
        Filter.atTop (nhds ‖a‖) := ha.norm
    have hprod := hrLarge.atTop_mul_pos (norm_pos_iff.mpr ha0) hnorm
    exact hprod.const_mul_atTop QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hcover : ∀ n, ball 0 (ρ n) ⊆ (ψ n) '' ball 0 (r n) := by
    intro n
    have h := QuantumZipper.CA.Koebe.ball_subset_image_koebe (hd n) (hinj n)
    simpa only [hzero n, ρ, mul_assoc] using h
  have hgd : ∀ n, DifferentiableOn ℂ (g n) (ball 0 (ρ n)) := by
    intro n w hw
    obtain ⟨z, hz, rfl⟩ := hcover n hw
    exact (QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
      isOpen_ball (hd n) (hinj n) hz).differentiableAt.differentiableWithinAt
  have hgi : ∀ n, InjOn (g n) (ball 0 (ρ n)) := by
    intro n
    exact (Function.invFunOn_injOn_image (ψ n) (ball 0 (r n))).mono (hcover n)
  have hgzero : ∀ n, g n 0 = 0 := by
    intro n
    have hz : (0 : ℂ) ∈ ball 0 (r n) := mem_ball_self (hr n)
    have hx : ∃ z ∈ ball 0 (r n), ψ n z = 0 := ⟨0, hz, hzero n⟩
    exact (hinj n (Function.invFunOn_mem hx) hz
      ((Function.invFunOn_eq hx).trans (hzero n).symm))
  have hgderiv : ∀ n, deriv (g n) 0 = (deriv (ψ n) 0)⁻¹ := by
    intro n
    have hz : (0 : ℂ) ∈ ball 0 (r n) := mem_ball_self (hr n)
    have h := QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
      isOpen_ball (hd n) (hinj n) hz
    rw [hzero n] at h
    exact h.deriv
  have hga : Filter.Tendsto (fun n => deriv (g n) 0) Filter.atTop (nhds a⁻¹) := by
    simpa only [hgderiv] using ha.inv₀ ha0
  exact ⟨univalent_maps_tendsto hρpos hρLarge hgd hgi hgzero hga,
    univalent_derivs_tendsto hρpos hρLarge hgd hgi hga⟩

theorem univalent_inverses_tendsto {ψ : ℕ → ℂ → ℂ} {r : ℕ → ℝ} {a : ℂ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (ψ n) (ball 0 (r n)))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a))
    (ha0 : a ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n => Function.invFunOn (ψ n) (ball 0 (r n)))
      (fun z => a⁻¹ * z) Filter.atTop Set.univ :=
  (univalent_inverse_core hr hrLarge hd hinj hzero ha ha0).1

theorem univalent_inverse_derivs_tendsto {ψ : ℕ → ℂ → ℂ} {r : ℕ → ℝ} {a : ℂ}
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (ψ n) (ball 0 (r n)))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a))
    (ha0 : a ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n z => deriv (Function.invFunOn (ψ n) (ball 0 (r n))) z)
      (fun _ => a⁻¹) Filter.atTop Set.univ :=
  (univalent_inverse_core hr hrLarge hd hinj hzero ha ha0).2

/-- The Weyl correction from the inverse derivative vanishes on compact sets. -/
theorem univalent_inverse_log_derivs_tendsto {ψ : ℕ → ℂ → ℂ} {r : ℕ → ℝ}
    {a : ℂ} (Q : ℝ)
    (hr : ∀ n, 0 < r n) (hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (ball 0 (r n)))
    (hinj : ∀ n, InjOn (ψ n) (ball 0 (r n)))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a))
    (ha0 : a ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n z => Q * Real.log ‖deriv (Function.invFunOn (ψ n) (ball 0 (r n))) z‖ +
        Q * Real.log ‖a‖)
      (fun _ => 0) Filter.atTop Set.univ := by
  have hlog := log_norm_tendsto_of_nonzero (inv_ne_zero ha0)
    (univalent_inverse_derivs_tendsto hr hrLarge hd hinj hzero ha ha0)
  have huc : UniformContinuous (fun x : ℝ => Q * x + Q * Real.log ‖a‖) :=
    Real.uniformContinuous_const_mul.add_const _
  have h := huc.comp_tendstoLocallyUniformlyOn hlog
  have hlim : Q * Real.log ‖a⁻¹‖ + Q * Real.log ‖a‖ = 0 := by
    rw [norm_inv, Real.log_inv]
    ring
  convert h using 1
  · funext n z; rfl
  · funext z; exact hlim.symm

/-- A scale small relative to an interior disk produces expanding normalized disks. -/
theorem relative_radius_tendsto {t s : ℕ → ℝ}
    (ht : ∀ n, 0 < t n) (hs : ∀ n, 0 < s n)
    (hrel : Filter.Tendsto (fun n => t n / s n) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => s n / t n) Filter.atTop Filter.atTop := by
  have hpos : ∀ᶠ n in Filter.atTop, 0 < t n / s n :=
    Filter.Eventually.of_forall (fun n => div_pos (ht n) (hs n))
  have hgt : Filter.Tendsto (fun n => t n / s n) Filter.atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrel, hpos⟩
  have h := hgt.inv_tendsto_nhdsGT_zero
  change Filter.Tendsto (fun n => (t n / s n)⁻¹) Filter.atTop Filter.atTop at h
  simpa only [inv_div] using h

/-- The paper's centered, rescaled maps satisfy the normalized Koebe hypotheses. -/
theorem relative_normalized_core {φ : ℕ → ℂ → ℂ} {z : ℕ → ℂ}
    {t s : ℕ → ℝ} (ht : ∀ n, 0 < t n) (hs : ∀ n, 0 < s n)
    (hrel : Filter.Tendsto (fun n => t n / s n) Filter.atTop (nhds 0))
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (ball (z n) (s n)))
    (hinj : ∀ n, InjOn (φ n) (ball (z n) (s n))) :
    let F : ℕ → ℂ → ℂ := fun n w =>
      (φ n (z n + (t n : ℂ) * w) - φ n (z n)) /
        ((t n : ℂ) * deriv (φ n) (z n))
    TendstoLocallyUniformlyOn F id Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn (fun n => deriv (F n)) (fun _ => 1)
        Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn (fun n w => Real.log ‖deriv (F n) w‖)
        (fun _ => 0) Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn
        (fun n => Function.invFunOn (F n) (ball 0 (s n / t n))) id
        Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn
        (fun n => deriv (Function.invFunOn (F n) (ball 0 (s n / t n))))
        (fun _ => 1) Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn
        (fun n w => Real.log ‖deriv (Function.invFunOn (F n)
          (ball 0 (s n / t n))) w‖)
        (fun _ => 0) Filter.atTop Set.univ ∧
      (∀ (S : ℝ) (k : ℕ),
        TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n))
          (iteratedDeriv k id) Filter.atTop (ball 0 S)) ∧
      (∀ (S : ℝ) (k : ℕ),
        TendstoLocallyUniformlyOn
          (fun n => iteratedDeriv k (Function.invFunOn (F n)
            (ball 0 (s n / t n))))
          (iteratedDeriv k id) Filter.atTop (ball 0 S)) := by
  dsimp
  let R : ℕ → ℝ := fun n => s n / t n
  let F : ℕ → ℂ → ℂ := fun n w =>
    (φ n (z n + (t n : ℂ) * w) - φ n (z n)) /
      ((t n : ℂ) * deriv (φ n) (z n))
  have hRpos : ∀ n, 0 < R n := fun n => div_pos (hs n) (ht n)
  have hRLarge : Filter.Tendsto R Filter.atTop Filter.atTop :=
    relative_radius_tendsto ht hs hrel
  have hφderiv : ∀ n, deriv (φ n) (z n) ≠ 0 := by
    intro n
    exact QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball (hd n) (hinj n)
      (mem_ball_self (hs n))
  have hden : ∀ n, (t n : ℂ) * deriv (φ n) (z n) ≠ 0 := by
    intro n
    have htn : (t n : ℂ) ≠ 0 := by exact_mod_cast (ht n).ne'
    exact mul_ne_zero htn (hφderiv n)
  have hinto : ∀ n, ∀ w ∈ ball 0 (R n),
      z n + (t n : ℂ) * w ∈ ball (z n) (s n) := by
    intro n w hw
    have hwr : ‖w‖ < s n / t n := by simpa only [mem_ball, dist_zero_right] using hw
    have htw : t n * ‖w‖ < s n := by
      simpa only [mul_comm] using (lt_div_iff₀ (ht n)).mp hwr
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ht n)]
    exact htw
  have hFd : ∀ n, DifferentiableOn ℂ (F n) (ball 0 (R n)) := by
    intro n w hw
    have hφ : DifferentiableAt ℂ (φ n) (z n + (t n : ℂ) * w) :=
      (hd n).differentiableAt (isOpen_ball.mem_nhds (hinto n w hw))
    have harg : DifferentiableAt ℂ (fun v : ℂ => z n + (t n : ℂ) * v) w := by
      fun_prop
    exact ((hφ.comp w harg).sub_const _).div_const _ |>.differentiableWithinAt
  have hFi : ∀ n, InjOn (F n) (ball 0 (R n)) := by
    intro n x hx y hy hxy
    have hnum : φ n (z n + (t n : ℂ) * x) - φ n (z n) =
        φ n (z n + (t n : ℂ) * y) - φ n (z n) :=
      (div_left_inj' (hden n)).mp hxy
    have hφeq : φ n (z n + (t n : ℂ) * x) =
        φ n (z n + (t n : ℂ) * y) := sub_left_inj.mp hnum
    have harg := hinj n (hinto n x hx) (hinto n y hy) hφeq
    have hmul : (t n : ℂ) * x = (t n : ℂ) * y := add_left_cancel harg
    have htn : (t n : ℂ) ≠ 0 := by exact_mod_cast (ht n).ne'
    exact mul_left_cancel₀ htn hmul
  have hFzero : ∀ n, F n 0 = 0 := by
    intro n
    simp only [F, mul_zero, add_zero, sub_self, zero_div]
  have hFderiv : ∀ n, deriv (F n) 0 = 1 := by
    intro n
    have hφ : HasDerivAt (φ n) (deriv (φ n) (z n)) (z n) :=
      ((hd n).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hs n)))).hasDerivAt
    have harg : HasDerivAt (fun w : ℂ => z n + (t n : ℂ) * w) (t n : ℂ) 0 :=
      (hasDerivAt_const_mul (t n : ℂ)).const_add (z n)
    have hcomp : HasDerivAt (fun w : ℂ => φ n (z n + (t n : ℂ) * w))
        (deriv (φ n) (z n) * (t n : ℂ)) 0 := by
      have hφ' : HasDerivAt (φ n) (deriv (φ n) (z n))
          (z n + (t n : ℂ) * 0) := by simpa using hφ
      exact hφ'.comp 0 harg
    have hF : HasDerivAt (F n)
        ((deriv (φ n) (z n) * (t n : ℂ)) /
          ((t n : ℂ) * deriv (φ n) (z n))) 0 :=
      (hcomp.sub_const _).div_const _
    rw [hF.deriv]
    rw [mul_comm (deriv (φ n) (z n)) (t n : ℂ), div_self (hden n)]
  exact ⟨normalized_maps_tendsto hRpos hRLarge hFd hFi hFzero hFderiv,
    normalized_derivs_tendsto hRpos hRLarge hFd hFi hFderiv,
    normalized_log_derivs_tendsto hRpos hRLarge hFd hFi hFderiv,
    normalized_inverses_tendsto hRpos hRLarge hFd hFi hFzero hFderiv,
    normalized_inverse_derivs_tendsto hRpos hRLarge hFd hFi hFzero hFderiv,
    normalized_inverse_log_derivs_tendsto hRpos hRLarge hFd hFi hFzero hFderiv,
    (fun S k => normalized_iteratedDeriv_tendsto_on_ball hRpos hRLarge hFd hFi
      hFzero hFderiv S k),
    (fun S k => normalized_inverse_iteratedDeriv_tendsto_on_ball S k hRpos hRLarge
      hFd hFi hFzero hFderiv)⟩

/-- Domain form of the small-relative-scale claim, using distance to the complement. -/
theorem relative_normalized_domain_core {U : ℕ → Set ℂ}
    {φ : ℕ → ℂ → ℂ} {z : ℕ → ℂ} {t : ℕ → ℝ}
    (hopen : ∀ n, IsOpen (U n)) (hz : ∀ n, z n ∈ U n)
    (hproper : ∀ n, (U n)ᶜ.Nonempty)
    (ht : ∀ n, 0 < t n)
    (hrel : Filter.Tendsto (fun n => t n / infDist (z n) (U n)ᶜ)
      Filter.atTop (nhds 0))
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n))
    (hinj : ∀ n, InjOn (φ n) (U n)) :
    let s : ℕ → ℝ := fun n => infDist (z n) (U n)ᶜ
    let F : ℕ → ℂ → ℂ := fun n w =>
      (φ n (z n + (t n : ℂ) * w) - φ n (z n)) /
        ((t n : ℂ) * deriv (φ n) (z n))
    TendstoLocallyUniformlyOn F id Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn (fun n => deriv (F n)) (fun _ => 1)
        Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn (fun n w => Real.log ‖deriv (F n) w‖)
        (fun _ => 0) Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn
        (fun n => Function.invFunOn (F n) (ball 0 (s n / t n))) id
        Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn
        (fun n => deriv (Function.invFunOn (F n) (ball 0 (s n / t n))))
        (fun _ => 1) Filter.atTop Set.univ ∧
      TendstoLocallyUniformlyOn
        (fun n w => Real.log ‖deriv (Function.invFunOn (F n)
          (ball 0 (s n / t n))) w‖)
        (fun _ => 0) Filter.atTop Set.univ ∧
      (∀ (S : ℝ) (k : ℕ),
        TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n))
          (iteratedDeriv k id) Filter.atTop (ball 0 S)) ∧
      (∀ (S : ℝ) (k : ℕ),
        TendstoLocallyUniformlyOn
          (fun n => iteratedDeriv k (Function.invFunOn (F n)
            (ball 0 (s n / t n))))
          (iteratedDeriv k id) Filter.atTop (ball 0 S)) := by
  dsimp
  let s : ℕ → ℝ := fun n => infDist (z n) (U n)ᶜ
  have hs : ∀ n, 0 < s n := by
    intro n
    apply ((hopen n).isClosed_compl.notMem_iff_infDist_pos (hproper n)).mp
    simpa only [mem_compl_iff, not_not] using hz n
  have hball : ∀ n, ball (z n) (s n) ⊆ U n := by
    intro n
    exact ball_infDist_compl_subset
  have hlocd : ∀ n, DifferentiableOn ℂ (φ n) (ball (z n) (s n)) :=
    fun n => (hd n).mono (hball n)
  have hloci : ∀ n, InjOn (φ n) (ball (z n) (s n)) :=
    fun n => (hinj n).mono (hball n)
  exact relative_normalized_core ht hs hrel hlocd hloci

/-- An exhaustion by open domains containing zero admits expanding centered disks. -/
theorem exhaustion_radii {U : ℕ → Set ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzero : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in Filter.atTop, K ⊆ U n) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧
      Filter.Tendsto r Filter.atTop Filter.atTop ∧
      ∀ n, ball 0 (r n) ⊆ U n := by
  classical
  let A : ℕ → Finset ℕ := fun n =>
    (Finset.range (n + 1)).filter (fun k => ball (0 : ℂ) (k : ℝ) ⊆ U n)
  have hA0 : ∀ n, 0 ∈ A n := by
    intro n
    simp [A, Metric.ball_zero]
  let m : ℕ → ℕ := fun n => (A n).max' ⟨0, hA0 n⟩
  have hmball : ∀ n, ball (0 : ℂ) (m n : ℝ) ⊆ U n := by
    intro n
    exact (Finset.mem_filter.mp ((A n).max'_mem ⟨0, hA0 n⟩)).2
  have hmLarge : Filter.Tendsto m Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro k
    have hcov : ∀ᶠ n in Filter.atTop,
        ball (0 : ℂ) (k : ℝ) ⊆ U n := by
      filter_upwards [hexhaust (closedBall (0 : ℂ) (k : ℝ))
        (isCompact_closedBall (0 : ℂ) (k : ℝ))] with n hn
      exact (ball_subset_closedBall.trans hn)
    filter_upwards [Filter.eventually_ge_atTop k, hcov] with n hn hU
    have hk : k ∈ A n := by
      simp only [A, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hU⟩
    exact (A n).le_max' k hk
  have hδ : ∀ n, ∃ δ : ℝ, 0 < δ ∧ ball (0 : ℂ) δ ⊆ U n := by
    intro n
    exact Metric.mem_nhds_iff.mp ((hopen n).mem_nhds (hzero n))
  let δ : ℕ → ℝ := fun n => (hδ n).choose
  have hδpos : ∀ n, 0 < δ n := fun n => (hδ n).choose_spec.1
  have hδsub : ∀ n, ball (0 : ℂ) (δ n) ⊆ U n :=
    fun n => (hδ n).choose_spec.2
  let r : ℕ → ℝ := fun n => if m n = 0 then δ n else (m n : ℝ)
  have hrpos : ∀ n, 0 < r n := by
    intro n
    by_cases hm : m n = 0
    · simpa [r, hm] using hδpos n
    · simp [r, hm, Nat.cast_pos, Nat.pos_of_ne_zero hm]
  have hrsub : ∀ n, ball (0 : ℂ) (r n) ⊆ U n := by
    intro n
    by_cases hm : m n = 0
    · simpa [r, hm] using hδsub n
    · simpa [r, hm] using hmball n
  have hrLarge : Filter.Tendsto r Filter.atTop Filter.atTop := by
    have hmone : ∀ᶠ n in Filter.atTop, m n ≠ 0 :=
      (hmLarge.eventually_ge_atTop 1).mono (fun n hn => by omega)
    have heq : r =ᶠ[Filter.atTop] (fun n => (m n : ℝ)) := by
      filter_upwards [hmone] with n hn
      simp [r, hn]
    exact (tendsto_natCast_atTop_atTop.comp hmLarge).congr' heq.symm
  exact ⟨r, hrpos, hrLarge, hrsub⟩

/-- The map and derivative limits for an exhaustion by domains. -/
theorem exhausting_maps_tendsto {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in Filter.atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n))
    (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a)) :
    TendstoLocallyUniformlyOn ψ (fun z => a * z) Filter.atTop Set.univ ∧
    TendstoLocallyUniformlyOn (fun n z => deriv (ψ n) z) (fun _ => a)
      Filter.atTop Set.univ := by
  obtain ⟨r, hrpos, hrLarge, hrsub⟩ := exhaustion_radii hopen hzeroU hexhaust
  have hdr : ∀ n, DifferentiableOn ℂ (ψ n) (ball 0 (r n)) :=
    fun n => (hd n).mono (hrsub n)
  have hir : ∀ n, InjOn (ψ n) (ball 0 (r n)) :=
    fun n => (hinj n).mono (hrsub n)
  exact ⟨univalent_maps_tendsto hrpos hrLarge hdr hir hzero ha,
    univalent_derivs_tendsto hrpos hrLarge hdr hir ha⟩

/-- Every fixed derivative order of the exhausting-domain maps converges locally uniformly. -/
theorem exhausting_maps_iteratedDeriv_tendsto {U : ℕ → Set ℂ}
    {ψ : ℕ → ℂ → ℂ} {a : ℂ} (S : ℝ) (k : ℕ)
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in Filter.atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n))
    (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a)) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (ψ n))
      (iteratedDeriv k (fun z => a * z)) Filter.atTop (ball 0 S) := by
  have hlocal : ∀ T : ℝ, ∀ᶠ n in Filter.atTop,
      DifferentiableOn ℂ (ψ n) (ball 0 T) := by
    intro T
    filter_upwards [hexhaust (closedBall (0 : ℂ) T)
      (isCompact_closedBall (0 : ℂ) T)] with n hn
    exact (hd n).mono (ball_subset_closedBall.trans hn)
  exact iteratedDeriv_tendsto_on_ball
    (exhausting_maps_tendsto hopen hzeroU hexhaust hd hinj hzero ha).1
    hlocal S k

/-- The inverse and inverse-derivative limits on the actual image domains. -/
theorem exhausting_inverse_core {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in Filter.atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n))
    (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a))
    (ha0 : a ≠ 0) :
    TendstoLocallyUniformlyOn (fun n => Function.invFunOn (ψ n) (U n))
      (fun z => a⁻¹ * z) Filter.atTop Set.univ ∧
    TendstoLocallyUniformlyOn
      (fun n z => deriv (Function.invFunOn (ψ n) (U n)) z)
      (fun _ => a⁻¹) Filter.atTop Set.univ := by
  obtain ⟨r, hrpos, hrLarge, hrsub⟩ := exhaustion_radii hopen hzeroU hexhaust
  let g : ℕ → ℂ → ℂ := fun n => Function.invFunOn (ψ n) (U n)
  let ρ : ℕ → ℝ := fun n =>
    QuantumZipper.CA.Koebe.koebeCovConst * (r n * ‖deriv (ψ n) 0‖)
  have hψderiv : ∀ n, deriv (ψ n) 0 ≠ 0 := by
    intro n
    exact QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn (hopen n) (hd n) (hinj n)
      (hzeroU n)
  have hρpos : ∀ n, 0 < ρ n := by
    intro n
    exact mul_pos QuantumZipper.CA.Koebe.koebeCovConst_pos
      (mul_pos (hrpos n) (norm_pos_iff.mpr (hψderiv n)))
  have hρLarge : Filter.Tendsto ρ Filter.atTop Filter.atTop := by
    have hnorm : Filter.Tendsto (fun n => ‖deriv (ψ n) 0‖)
        Filter.atTop (nhds ‖a‖) := ha.norm
    have hprod := hrLarge.atTop_mul_pos (norm_pos_iff.mpr ha0) hnorm
    exact hprod.const_mul_atTop QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hcover : ∀ n, ball 0 (ρ n) ⊆ (ψ n) '' U n := by
    intro n
    have hdr : DifferentiableOn ℂ (ψ n) (ball 0 (r n)) :=
      (hd n).mono (hrsub n)
    have hir : InjOn (ψ n) (ball 0 (r n)) :=
      (hinj n).mono (hrsub n)
    have hk := QuantumZipper.CA.Koebe.ball_subset_image_koebe hdr hir
    have hk' : ball 0 (ρ n) ⊆ (ψ n) '' ball 0 (r n) := by
      simpa only [hzero n, ρ, mul_assoc] using hk
    exact hk'.trans (Set.image_mono (hrsub n))
  have hgd : ∀ n, DifferentiableOn ℂ (g n) (ball 0 (ρ n)) := by
    intro n w hw
    obtain ⟨z, hz, rfl⟩ := hcover n hw
    exact (QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
      (hopen n) (hd n) (hinj n) hz).differentiableAt.differentiableWithinAt
  have hgi : ∀ n, InjOn (g n) (ball 0 (ρ n)) := by
    intro n
    exact (Function.invFunOn_injOn_image (ψ n) (U n)).mono (hcover n)
  have hgzero : ∀ n, g n 0 = 0 := by
    intro n
    have hx : ∃ z ∈ U n, ψ n z = 0 := ⟨0, hzeroU n, hzero n⟩
    exact (hinj n (Function.invFunOn_mem hx) (hzeroU n)
      ((Function.invFunOn_eq hx).trans (hzero n).symm))
  have hgderiv : ∀ n, deriv (g n) 0 = (deriv (ψ n) 0)⁻¹ := by
    intro n
    have h := QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
      (hopen n) (hd n) (hinj n) (hzeroU n)
    rw [hzero n] at h
    exact h.deriv
  have hga : Filter.Tendsto (fun n => deriv (g n) 0) Filter.atTop (nhds a⁻¹) := by
    simpa only [hgderiv] using ha.inv₀ ha0
  exact ⟨univalent_maps_tendsto hρpos hρLarge hgd hgi hgzero hga,
    univalent_derivs_tendsto hρpos hρLarge hgd hgi hga⟩

private theorem exhausting_inverse_eventually_holomorphic
    {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in Filter.atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n))
    (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a))
    (ha0 : a ≠ 0) (T : ℝ) :
    ∀ᶠ n in Filter.atTop,
      DifferentiableOn ℂ (Function.invFunOn (ψ n) (U n)) (ball 0 T) := by
  obtain ⟨r, hrpos, hrLarge, hrsub⟩ := exhaustion_radii hopen hzeroU hexhaust
  let ρ : ℕ → ℝ := fun n =>
    QuantumZipper.CA.Koebe.koebeCovConst * (r n * ‖deriv (ψ n) 0‖)
  have hnorm : Filter.Tendsto (fun n => ‖deriv (ψ n) 0‖)
      Filter.atTop (nhds ‖a‖) := ha.norm
  have hρLarge : Filter.Tendsto ρ Filter.atTop Filter.atTop := by
    have hprod := hrLarge.atTop_mul_pos (norm_pos_iff.mpr ha0) hnorm
    exact hprod.const_mul_atTop QuantumZipper.CA.Koebe.koebeCovConst_pos
  filter_upwards [hρLarge.eventually_gt_atTop T] with n hn
  have hdr : DifferentiableOn ℂ (ψ n) (ball 0 (r n)) := (hd n).mono (hrsub n)
  have hir : InjOn (ψ n) (ball 0 (r n)) := (hinj n).mono (hrsub n)
  have hk := QuantumZipper.CA.Koebe.ball_subset_image_koebe hdr hir
  have hcover : ball 0 (ρ n) ⊆ (ψ n) '' U n := by
    have hk' : ball 0 (ρ n) ⊆ (ψ n) '' ball 0 (r n) := by
      simpa only [hzero n, ρ, mul_assoc] using hk
    exact hk'.trans (Set.image_mono (hrsub n))
  intro w hw
  have hwρ : w ∈ ball 0 (ρ n) := (ball_subset_ball hn.le) hw
  obtain ⟨z, hz, rfl⟩ := hcover hwρ
  exact (QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn
    (hopen n) (hd n) (hinj n) hz).differentiableAt.differentiableWithinAt

/-- Every fixed derivative order of the actual inverse maps converges on compact disks. -/
theorem exhausting_inverse_iteratedDeriv_tendsto {U : ℕ → Set ℂ}
    {ψ : ℕ → ℂ → ℂ} {a : ℂ} (S : ℝ) (k : ℕ)
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in Filter.atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n))
    (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a))
    (ha0 : a ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n => iteratedDeriv k (Function.invFunOn (ψ n) (U n)))
      (iteratedDeriv k (fun z => a⁻¹ * z)) Filter.atTop (ball 0 S) := by
  exact iteratedDeriv_tendsto_on_ball
    (exhausting_inverse_core hopen hzeroU hexhaust hd hinj hzero ha ha0).1
    (exhausting_inverse_eventually_holomorphic hopen hzeroU hexhaust hd hinj hzero ha ha0)
    S k

/-- The paper's full analytic exhaustion claim, including the Weyl correction. -/
theorem exhausting_univalent_limits {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ}
    (Q : ℝ)
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in Filter.atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n))
    (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0)
    (ha : Filter.Tendsto (fun n => deriv (ψ n) 0) Filter.atTop (nhds a))
    (ha0 : a ≠ 0) :
    TendstoLocallyUniformlyOn ψ (fun z => a * z) Filter.atTop Set.univ ∧
    TendstoLocallyUniformlyOn (fun n z => deriv (ψ n) z) (fun _ => a)
      Filter.atTop Set.univ ∧
    TendstoLocallyUniformlyOn (fun n => Function.invFunOn (ψ n) (U n))
      (fun z => a⁻¹ * z) Filter.atTop Set.univ ∧
    TendstoLocallyUniformlyOn
      (fun n z => deriv (Function.invFunOn (ψ n) (U n)) z)
      (fun _ => a⁻¹) Filter.atTop Set.univ ∧
    TendstoLocallyUniformlyOn
      (fun n z => Q * Real.log ‖deriv (Function.invFunOn (ψ n) (U n)) z‖ +
        Q * Real.log ‖a‖)
      (fun _ => 0) Filter.atTop Set.univ := by
  obtain ⟨hmap, hderiv⟩ := exhausting_maps_tendsto hopen hzeroU hexhaust hd hinj hzero ha
  obtain ⟨hinv, hinvderiv⟩ :=
    exhausting_inverse_core hopen hzeroU hexhaust hd hinj hzero ha ha0
  have hlog := log_norm_tendsto_of_nonzero (inv_ne_zero ha0) hinvderiv
  have huc : UniformContinuous (fun x : ℝ => Q * x + Q * Real.log ‖a‖) :=
    Real.uniformContinuous_const_mul.add_const _
  have hlogQ := huc.comp_tendstoLocallyUniformlyOn hlog
  have hlim : Q * Real.log ‖a⁻¹‖ + Q * Real.log ‖a‖ = 0 := by
    rw [norm_inv, Real.log_inv]
    ring
  have hlogQ' : TendstoLocallyUniformlyOn
      (fun n z => Q * Real.log ‖deriv (Function.invFunOn (ψ n) (U n)) z‖ +
        Q * Real.log ‖a‖)
      (fun _ => 0) Filter.atTop Set.univ := by
    convert hlogQ using 1
    · funext n z; rfl
    · funext z; exact hlim.symm
  exact ⟨hmap, hderiv, hinv, hinvderiv, hlogQ'⟩

end SupercriticalConformalCovariance.Univalent

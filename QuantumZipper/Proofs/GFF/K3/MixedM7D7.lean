import QuantumZipper.Proofs.GFF.K3.MixedM7D6

/-!
# K3-mixed M7-a3, half-disc covariance, step D7: the explicit kernels

With `G_B(x, y) = log ‖r² − (x − t)(ȳ − t)‖ − log r − log ‖x − y‖` (`discG t r`), the Dirichlet
Green function of the disc `ball t r` (normalization `−log|x − y| + harmonic`):

* `greenH_discMap_m7d`: `G_ℍ(φ x, φ y) = G_B(x, y)` for `x ≠ y` in the disc, `φ = discMap t r`
  (the Cayley map; Möbius invariance, Sheffield 2007 §2.2);
* `halfDiscGreen_eq_discG_m7d`: `halfDiscGreen t r x y = G_B(x, y) + G_B(x, ȳ)` for `x` in the
  disc and `y ∈ closedBall t r'` (`r' < r`): the Poisson part of `neumannH (·, y)` is the harmonic
  function `u ↦ −log ‖r² − (u − t)(ȳ − t)‖ − log ‖r² − (u − t)(y − t)‖ + 2 log r`, which agrees
  with `neumannH (·, y)` on the circle (`|u − t| = r`: `r² − (u − t)(ȳ − t) = (u − t)·conj(u − y)`)
  and is even, so the half-disc Poisson formula (node L1) applies;
* `discG_conj_conj_m7d`: `G_B(x̄, ȳ) = G_B(x, y)`.

Own elementary computations (the method of images for the disc, e.g. Sheffield 2007, §2.2).
-/

noncomputable section

open MeasureTheory Set Metric Filter InnerProductSpace
open scoped Real Topology ComplexConjugate

namespace QuantumZipper.K3

/-- The Dirichlet Green function of the disc `ball t r` (`t` real). -/
def discG (t r : ℝ) (x y : ℂ) : ℝ :=
  Real.log ‖(r : ℂ) ^ 2 - (x - t) * (conj y - t)‖ - Real.log r - Real.log ‖x - y‖

theorem discG_conj_conj_m7d (t r : ℝ) (x y : ℂ) : discG t r (conj x) (conj y) = discG t r x y := by
  unfold discG
  have h1 : (r : ℂ) ^ 2 - (conj x - t) * (conj (conj y) - t) =
      conj ((r : ℂ) ^ 2 - (x - t) * (conj y - t)) := by
    simp [map_sub, map_mul, Complex.conj_ofReal]
  have h2 : conj x - conj y = conj (x - y) := (map_sub _ _ _).symm
  rw [h1, Complex.norm_conj, h2, Complex.norm_conj]

theorem numer_ne_zero_m7d {t r : ℝ} {x y : ℂ} (h : ‖x - t‖ * ‖y - t‖ < r ^ 2) :
    (r : ℂ) ^ 2 - (x - t) * (conj y - t) ≠ 0 := by
  intro h0
  have h1 : (x - t) * (conj y - t) = (r : ℂ) ^ 2 := (sub_eq_zero.1 h0).symm
  have h2 := congrArg norm h1
  rw [norm_mul, norm_conj_sub_ofReal_k3, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at h2
  linarith

/-- On the circle `|u − t| = r`: `‖r² − (u − t)(ȳ − t)‖ = r ‖u − y‖`. -/
theorem norm_numer_sphere_m7d {t r : ℝ} {u : ℂ} (hu : ‖u - t‖ = r) (y : ℂ) :
    ‖(r : ℂ) ^ 2 - (u - t) * (conj y - t)‖ = r * ‖u - y‖ := by
  have hr2 : (r : ℂ) ^ 2 = (u - t) * conj (u - t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; push_cast; ring
  have : (r : ℂ) ^ 2 - (u - t) * (conj y - t) = (u - t) * conj (u - y) := by
    rw [hr2]; simp only [map_sub, Complex.conj_ofReal]; ring
  rw [this, norm_mul, Complex.norm_conj, hu]

/-- The harmonic (Poisson) part of `neumannH (·, y)` on the disc. -/
def discHarm (t r : ℝ) (y u : ℂ) : ℝ :=
  -Real.log ‖(r : ℂ) ^ 2 - (u - t) * (conj y - t)‖ -
    Real.log ‖(r : ℂ) ^ 2 - (u - t) * (y - t)‖ + 2 * Real.log r

theorem harmonicOnNhd_discHarm_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r) {y : ℂ}
    (hy : y ∈ closedBall (t : ℂ) r') :
    HarmonicOnNhd (discHarm t r y) (closedBall (t : ℂ) r) := by
  intro u hu
  rw [mem_closedBall, dist_eq_norm] at hu hy
  have hprod : ‖u - t‖ * ‖y - t‖ < r ^ 2 := by
    calc ‖u - t‖ * ‖y - t‖ ≤ r * r' := mul_le_mul hu hy (norm_nonneg _) (by linarith)
      _ < r * r := mul_lt_mul_of_pos_left hr'r (by linarith)
      _ = r ^ 2 := by ring
  have hprod' : ‖u - t‖ * ‖conj y - t‖ < r ^ 2 := by rwa [norm_conj_sub_ofReal_k3]
  have hg : ∀ c : ℂ, AnalyticAt ℂ (fun u : ℂ => (r : ℂ) ^ 2 - (u - t) * (c - t)) u := fun c =>
    analyticAt_const.sub ((analyticAt_id.sub analyticAt_const).mul analyticAt_const)
  have h1 := (hg (conj y)).harmonicAt_log_norm (numer_ne_zero_m7d hprod)
  have h2 := (hg y).harmonicAt_log_norm (by
    have := numer_ne_zero_m7d hprod'; rwa [Complex.conj_conj] at this)
  convert (h1.neg.add h2.neg).add (harmonicAt_const (2 * Real.log r)) using 1
  funext v
  simp only [discHarm, Pi.add_apply, Pi.neg_apply]
  ring

theorem discHarm_conj_m7d (t r : ℝ) (y u : ℂ) : discHarm t r y (conj u) = discHarm t r y u := by
  unfold discHarm
  have h1 : (r : ℂ) ^ 2 - (conj u - t) * (conj y - t) = conj ((r : ℂ) ^ 2 - (u - t) * (y - t)) := by
    simp [map_sub, map_mul, Complex.conj_ofReal]
  have h2 : (r : ℂ) ^ 2 - (conj u - t) * (y - t) = conj ((r : ℂ) ^ 2 - (u - t) * (conj y - t)) := by
    simp [map_sub, map_mul, Complex.conj_ofReal]
  rw [h1, h2, Complex.norm_conj, Complex.norm_conj]; ring

theorem discHarm_sphere_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r) {y : ℂ}
    (hy : y ∈ closedBall (t : ℂ) r') {u : ℂ} (hu : u ∈ sphere (t : ℂ) r) :
    discHarm t r y u = neumannH u y := by
  rw [mem_sphere, dist_eq_norm] at hu
  rw [mem_closedBall, dist_eq_norm] at hy
  have hr : 0 < r := hr'.trans hr'r
  have huy : u - y ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hu; linarith
  have huy' : u - conj y ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, norm_conj_sub_ofReal_k3] at hu; linarith
  unfold discHarm neumannH
  rw [norm_numer_sphere_m7d hu y]
  have e : (r : ℂ) ^ 2 - (u - t) * (y - t) = (r : ℂ) ^ 2 - (u - t) * (conj (conj y) - t) := by
    rw [Complex.conj_conj]
  rw [e, norm_numer_sphere_m7d hu (conj y), Real.log_mul hr.ne' (norm_ne_zero_iff.2 huy),
    Real.log_mul hr.ne' (norm_ne_zero_iff.2 huy')]
  ring

/-- **The half-disc Green function is the image sum of disc Green functions.** -/
theorem halfDiscGreen_eq_discG_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r) {x y : ℂ}
    (hx : x ∈ ball (t : ℂ) r) (hy : y ∈ closedBall (t : ℂ) r') :
    halfDiscGreen t r x y = discG t r x y + discG t r x (conj y) := by
  have hr : 0 < r := hr'.trans hr'r
  have hint : ∫ u, neumannH u y ∂(halfDiscPoisson t r x) = discHarm t r y x := by
    rw [← integral_halfDiscPoisson_of_harmonic hr hx (harmonicOnNhd_discHarm_m7d hr' hr'r hy)
      (fun u _ => discHarm_conj_m7d t r y u)]
    refine integral_congr_ae ?_
    filter_upwards [ae_halfDiscPoisson_mem hr x] with u hu
    exact (discHarm_sphere_m7d hr' hr'r hy hu.1).symm
  rw [halfDiscGreen, hint]
  unfold discG discHarm neumannH
  rw [Complex.conj_conj]
  ring

theorem conj_cayleyInv_m7d (b : ℂ) : conj (CA.cayleyInv b) = -CA.cayleyInv (conj b) := by
  unfold CA.cayleyInv
  simp only [map_div₀, map_mul, map_add, map_sub, map_one, Complex.conj_I]
  ring

theorem cayleyInv_add_m7d {a c : ℂ} (ha : a ≠ 1) (hc : c ≠ 1) :
    CA.cayleyInv a + CA.cayleyInv c = 2 * Complex.I * (1 - a * c) / ((1 - a) * (1 - c)) := by
  unfold CA.cayleyInv
  have ha' : 1 - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hc' : 1 - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
  field_simp
  ring

/-- **Möbius invariance:** the `ℍ` Green function transported by the Cayley map is `G_B`. -/
theorem greenH_discMap_m7d {t r : ℝ} (hr : 0 < r) {x y : ℂ} (hx : x ∈ ball (t : ℂ) r)
    (hy : y ∈ ball (t : ℂ) r) (hxy : x ≠ y) :
    greenH (discMap t r x) (discMap t r y) = discG t r x y := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set a := (x - t) / (r : ℂ) with ha_def
  set b := (y - t) / (r : ℂ) with hb_def
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.1 (aff_mem_ball_m7d hr hx)
  have hb1 : ‖b‖ < 1 := mem_ball_zero_iff.1 (aff_mem_ball_m7d hr hy)
  have ha := ne_one_of_norm_lt_m7d ha1
  have hb := ne_one_of_norm_lt_m7d hb1
  have hcb : ‖conj b‖ < 1 := by rwa [Complex.norm_conj]
  have hcb1 := ne_one_of_norm_lt_m7d hcb
  set N : ℂ := (r : ℂ) ^ 2 - (x - t) * (conj y - t) with hN
  have hxt : ‖x - t‖ < r := by rwa [mem_ball, dist_eq_norm] at hx
  have hyt : ‖y - t‖ < r := by rwa [mem_ball, dist_eq_norm] at hy
  have hN0 : N ≠ 0 := numer_ne_zero_m7d (by nlinarith [norm_nonneg (x - t), norm_nonneg (y - t)])
  have e1 : discMap t r x - conj (discMap t r y) =
      2 * Complex.I * (N / (r : ℂ) ^ 2) / ((1 - a) * (1 - conj b)) := by
    unfold discMap
    rw [conj_cayleyInv_m7d, sub_neg_eq_add, cayleyInv_add_m7d ha hcb1]
    congr 2
    simp only [hN, ha_def, hb_def, map_div₀, map_sub, Complex.conj_ofReal]
    field_simp
  have e2 : discMap t r x - discMap t r y =
      2 * Complex.I * ((x - y) / r) / ((1 - a) * (1 - b)) := by
    unfold discMap
    rw [cayleyInv_sub_m7d ha hb]
    congr 2
    simp only [ha_def, hb_def]
    field_simp
    ring
  have hcb' : ‖1 - conj b‖ = ‖1 - b‖ := by
    rw [show (1 : ℂ) - conj b = conj (1 - b) by simp, Complex.norm_conj]
  have hna : 0 < ‖1 - a‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm ha))
  have hnb : 0 < ‖1 - b‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hb))
  have hxy0 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hN0' : 0 < ‖N‖ := norm_pos_iff.2 hN0
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have nP : ‖discMap t r x - conj (discMap t r y)‖ =
      2 * (‖N‖ / r ^ 2) / (‖1 - a‖ * ‖1 - b‖) := by
    rw [e1, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, norm_div,
      norm_pow, hnr, hcb']
    ring
  have nQ : ‖discMap t r x - discMap t r y‖ = 2 * (‖x - y‖ / r) / (‖1 - a‖ * ‖1 - b‖) := by
    rw [e2, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, norm_div,
      hnr]
    ring
  have hratio : ‖discMap t r x - conj (discMap t r y)‖ =
      ‖discMap t r x - discMap t r y‖ * (‖N‖ / (r * ‖x - y‖)) := by
    rw [nP, nQ]; field_simp
  have hQ0 : ‖discMap t r x - discMap t r y‖ ≠ 0 := by rw [nQ]; positivity
  unfold greenH discG
  rw [hratio, Real.log_mul hQ0 (by positivity), Real.log_div hN0'.ne' (by positivity),
    Real.log_mul hr.ne' hxy0.ne']
  ring

end QuantumZipper.K3

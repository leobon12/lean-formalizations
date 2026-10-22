import HigherDimLQGMetric.LGF.Exists

/-!
# Band integrands of functions; fine band pairability (packet S5a, D-WN′ (a))

Source: MA3 Details (a) **D-WN′** (`planning/audits/MA3-sections-5-6.md`), construction steps (a)
and (2); blueprint `prop:wn-split` (construction (a)).

Throughout, `κ₀ = kappa0 d` is F2's fixed admissible kernel (HigherDimLFPP's `bumpKernel`) and
`K_t = scaleKernel κ₀ t`, `K_t(v) = t^{-(d+1)/2} κ₀(v/t)`. For a function `f` and a scale set `S`,
the band integrand of the white-noise pairing `⟨H_S, f⟩` is

  `wnsFn S f (t, y) = 1_S(t) ∫ K_t(z − y) f(z) dz`  (`wnsConv t y f = ∫ K_t(z − y) f(z) dz`).

* `bandFun_posM_sub_eq_wnsFn`: for bounded boundedly supported `f`, HigherDimLFPP's measure-level
  integrand of the pair `(f⁺ dz, f⁻ dz)` is `wnsFn S f`;
* `wnsConv_eq_zero` (**finite range**): if `f` vanishes outside `B(c, r)` and `‖y − c‖ ≥ r + ρ₀ t`
  (`κ₀ = 0` outside `B(0, ρ₀)`), then `wnsConv t y f = 0`;
* `memLp_wnsFn_Ioi`: for mean-zero `f`, `wnsFn (0, ∞) f ∈ L²` (F2's Gram identity);
* `memLp_wnsFn_theta`: the fine band integrand `wnsFn (0, b) θ` of F2's normalizing bump `θ` is in
  `L²` (`d ≥ 1`), by comparison with the mean-zero `θ − θ(· − e)` for a far point `e`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN scaleKernel bandFun bandVecM IsPairable)

variable {d : ℕ}

/-- F2's kernel `κ₀` is admissible. -/
theorem wns_isLFPPKernel : HigherDimLFPP.IsLFPPKernel (kappa0 d) :=
  HigherDimLFPP.isLFPPKernel_bumpKernel d

/-- `∫ K_t(z − y) f(z) dz` with `K_t = scaleKernel κ₀ t`. -/
def wnsConv (t : ℝ) (y : Rd d) (f : Rd d → ℝ) : ℝ :=
  ∫ z, scaleKernel (kappa0 d) t (z - y) * f z

/-- The band integrand of a function `f` over the scale set `S`:
`(t, y) ↦ 1_S(t) ∫ K_t(z − y) f(z) dz`. -/
def wnsFn (S : Set ℝ) (f : Rd d → ℝ) (p : ℝ × Rd d) : ℝ :=
  S.indicator (fun t => wnsConv t p.2 f) p.1

/-! ## Integrability and linearity -/

theorem integrable_scaleKernel_mul_wns (t : ℝ) (y : Rd d) {f : Rd d → ℝ} (hf : Integrable f) :
    Integrable fun z => scaleKernel (kappa0 d) t (z - y) * f z := by
  obtain ⟨A, hA⟩ := (wns_isLFPPKernel (d := d)).exists_bound
  refine hf.bdd_mul (c := |t ^ (-((d : ℝ) + 1) / 2)| * A)
    ((HigherDimLFPP.continuous_scaleKernel wns_isLFPPKernel t).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact HigherDimLFPP.abs_scaleKernel_le' hA t _

theorem wnsConv_sub_mul (t : ℝ) (y : Rd d) {f g : Rd d → ℝ} (hf : Integrable f)
    (hg : Integrable g) (c : ℝ) :
    wnsConv t y (fun z => f z - c * g z) = wnsConv t y f - c * wnsConv t y g := by
  unfold wnsConv
  have e : (fun z => scaleKernel (kappa0 d) t (z - y) * (f z - c * g z)) =
      fun z => scaleKernel (kappa0 d) t (z - y) * f z -
        c * (scaleKernel (kappa0 d) t (z - y) * g z) := by
    funext z
    ring
  rw [e, integral_sub (integrable_scaleKernel_mul_wns t y hf)
    ((integrable_scaleKernel_mul_wns t y hg).const_mul c), integral_const_mul]

theorem wnsConv_sub (t : ℝ) (y : Rd d) {f g : Rd d → ℝ} (hf : Integrable f)
    (hg : Integrable g) :
    wnsConv t y (fun z => f z - g z) = wnsConv t y f - wnsConv t y g := by
  have h := wnsConv_sub_mul t y hf hg 1
  simp only [one_mul] at h
  exact h

/-! ## The measure-level band integrands of `f⁺ dz`, `f⁻ dz` -/

theorem wns_scaleConv_posM {f : Rd d → ℝ} (hf : Measurable f) (t : ℝ) (y : Rd d) :
    HigherDimLFPP.scaleConv (kappa0 d) t (posM f) y =
      ∫ z, scaleKernel (kappa0 d) t (z - y) * max (f z) 0 := by
  rw [HigherDimLFPP.scaleConv, posM, integral_withDensity_eq_integral_toReal_smul
    hf.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  ring

/-- **The band integrand of `(f⁺ dz, f⁻ dz)`** is `wnsFn S f`. -/
theorem bandFun_posM_sub_eq_wnsFn {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D)
    (S : Set ℝ) :
    bandFun (kappa0 d) S (posM f) - bandFun (kappa0 d) S (posM (-f)) = wnsFn S f := by
  funext p
  simp only [Pi.sub_apply, HigherDimLFPP.bandFun_apply, wnsFn]
  by_cases ht : p.1 ∈ S
  · rw [indicator_of_mem ht, indicator_of_mem ht, indicator_of_mem ht,
      wns_scaleConv_posM hf.measurable, wns_scaleConv_posM hf.neg.measurable, wnsConv,
      ← integral_sub (integrable_scaleKernel_mul_wns _ _ hf.posPart.integrable)
        (integrable_scaleKernel_mul_wns _ _ hf.neg.posPart.integrable)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Pi.neg_apply]
    rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, indicator_of_notMem ht, sub_zero]

/-- For a nonnegative function, `f⁻ dz = 0`. -/
theorem wns_posM_neg_eq_zero {f : Rd d → ℝ} (hf : ∀ z, 0 ≤ f z) : posM (-f) = 0 := by
  have e : (fun z => ENNReal.ofReal ((-f) z)) = 0 := by
    funext z
    simp only [Pi.neg_apply, Pi.zero_apply]
    exact ENNReal.ofReal_of_nonpos (neg_nonpos.2 (hf z))
  rw [posM, e, withDensity_zero]

/-- For a nonnegative function, the band integrand of `f dz` is `wnsFn S f`. -/
theorem bandFun_posM_eq_wnsFn {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D)
    (hf0 : ∀ z, 0 ≤ f z) (S : Set ℝ) : bandFun (kappa0 d) S (posM f) = wnsFn S f := by
  have h := bandFun_posM_sub_eq_wnsFn hf S
  rwa [wns_posM_neg_eq_zero hf0, HigherDimLFPP.bandFun_zero_measure, sub_zero] at h

/-! ## Finite range -/

/-- **Finite range of the band integrands**: if `κ₀` vanishes outside `B(0, ρ₀)`, `f` vanishes
outside `B(c, r)`, `t > 0` and `‖y − c‖ ≥ r + ρ₀ t`, then `∫ K_t(z − y) f(z) dz = 0`. -/
theorem wnsConv_eq_zero {f : Rd d → ℝ} {c : Rd d} {r ρ₀ t : ℝ}
    (hρ : ∀ v : Rd d, ρ₀ ≤ ‖v‖ → kappa0 d v = 0) (ht : 0 < t)
    (hf : ∀ z, f z ≠ 0 → ‖z - c‖ < r) {y : Rd d} (hy : r + ρ₀ * t ≤ ‖y - c‖) :
    wnsConv t y f = 0 := by
  unfold wnsConv
  refine integral_eq_zero_of_ae (ae_of_all _ fun z => ?_)
  by_cases hz : f z = 0
  · simp only [hz, mul_zero, Pi.zero_apply]
  · have h1 := hf z hz
    have h2 : ‖y - c‖ - ‖z - c‖ ≤ ‖z - y‖ := by
      have h := norm_sub_norm_le (y - c) (z - c)
      rwa [sub_sub_sub_cancel_right, norm_sub_rev y z] at h
    have h3 : ρ₀ ≤ ‖t⁻¹ • (z - y)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
      linarith
    simp only [scaleKernel, hρ _ h3, mul_zero, zero_mul, Pi.zero_apply]

/-- Finite range for the bands `S ⊆ (0, b)`. -/
theorem wnsFn_eq_zero_of_far {S : Set ℝ} {b : ℝ} (hS : S ⊆ Ioo 0 b) {f : Rd d → ℝ} {c : Rd d}
    {r ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ : ∀ v : Rd d, ρ₀ ≤ ‖v‖ → kappa0 d v = 0)
    (hf : ∀ z, f z ≠ 0 → ‖z - c‖ < r) {p : ℝ × Rd d} (hp : r + ρ₀ * b ≤ ‖p.2 - c‖) :
    wnsFn S f p = 0 := by
  unfold wnsFn
  by_cases ht : p.1 ∈ S
  · rw [indicator_of_mem ht]
    have ht' := hS ht
    refine wnsConv_eq_zero hρ ht'.1 hf (le_trans ?_ hp)
    have : ρ₀ * p.1 ≤ ρ₀ * b := mul_le_mul_of_nonneg_left ht'.2.le hρ₀.le
    linarith
  · rw [indicator_of_notMem ht]

/-! ## Square integrability -/

theorem measurable_wnsFn {S : Set ℝ} (hS : MeasurableSet S) {f : Rd d → ℝ} {M D : ℝ}
    (hf : IsBddSupp f M D) : Measurable (wnsFn S f) := by
  have := isFiniteMeasure_posM hf
  have := isFiniteMeasure_posM hf.neg
  rw [← bandFun_posM_sub_eq_wnsFn hf S]
  exact (HigherDimLFPP.measurable_bandFun wns_isLFPPKernel hS _).sub
    (HigherDimLFPP.measurable_bandFun wns_isLFPPKernel hS _)

theorem wnsFn_eq_indicator {S T : Set ℝ} (hST : S ⊆ T) (f : Rd d → ℝ) :
    wnsFn S f = (S ×ˢ (univ : Set (Rd d))).indicator (wnsFn T f) := by
  funext p
  unfold wnsFn
  by_cases h : p.1 ∈ S
  · rw [indicator_of_mem (mk_mem_prod h (mem_univ p.2)), indicator_of_mem h,
      indicator_of_mem (hST h)]
  · rw [indicator_of_notMem h, indicator_of_notMem fun hp => h (mem_prod.1 hp).1]

theorem memLp_wnsFn_of_subset {S T : Set ℝ} (hS : MeasurableSet S) (hST : S ⊆ T)
    {f : Rd d → ℝ} (h : MemLp (wnsFn T f) 2 volume) : MemLp (wnsFn S f) 2 volume := by
  rw [wnsFn_eq_indicator hST]
  exact h.indicator (hS.prod MeasurableSet.univ)

/-- For mean-zero bounded boundedly supported `f`, the all-scale pair `(f⁺ dz, f⁻ dz)` is pairable
(F2's Gram identity, HigherDimLFPP's `scaleCov_eq_logCov`). -/
theorem wns_isPairable_Ioi_posM [NeZero d] {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D)
    (hf0 : ∫ z, f z = 0) : IsPairable (kappa0 d) (Ioi 0) (posM f) (posM (-f)) := by
  have := isFiniteMeasure_posM hf
  have := isFiniteMeasure_posM hf.neg
  exact (HigherDimLFPP.scaleCov_eq_logCov wns_isLFPPKernel (posM_real_univ_eq hf hf0)
    (posM_real_univ_eq hf hf0) (logPairable_posM hf hf)).1

theorem memLp_wnsFn_Ioi [NeZero d] {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D)
    (hf0 : ∫ z, f z = 0) : MemLp (wnsFn (Ioi 0) f) 2 volume := by
  have h := wns_isPairable_Ioi_posM hf hf0
  rwa [IsPairable, bandFun_posM_sub_eq_wnsFn hf] at h

/-- `θ` is bounded, measurable and vanishes outside `B̄(0, 1)`. -/
theorem wns_exists_isBddSupp_theta : ∃ M : ℝ, IsBddSupp (theta d : Rd d → ℝ) M 1 := by
  obtain ⟨C, -, hC⟩ := exists_theta_bound (d := d)
  exact ⟨C, (theta d).continuous.measurable, hC, fun z hz => theta_eq_zero hz.le⟩

theorem wns_theta_nonneg (z : Rd d) : 0 ≤ theta d z := bumpTest_nonneg 0 0 z

theorem wns_theta_ne_zero_imp {z : Rd d} (hz : theta d z ≠ 0) : ‖z - 0‖ < 1 := by
  rw [sub_zero]
  by_contra h
  exact hz (theta_eq_zero (not_lt.1 h))

/-- **The fine band of `θ` is square integrable** (`d ≥ 1`, `b > 0`): `wnsFn (0, b) θ ∈ L²`.
Comparison with the mean-zero `θ − θ(· − e)`, `‖e‖ ≥ 2(1 + ρ₀ b)`: on `‖y‖ < 1 + ρ₀ b` the two fine
integrands agree (finite range for `θ(· − e)`), and `wnsFn (0, b) θ` vanishes elsewhere. -/
theorem memLp_wnsFn_theta [NeZero d] {b : ℝ} (hb : 0 < b) :
    MemLp (wnsFn (Ioo 0 b) (theta d : Rd d → ℝ)) 2 volume := by
  obtain ⟨ρ₀, hρ₀, hρ⟩ := (wns_isLFPPKernel (d := d)).exists_radius
  obtain ⟨Mθ, hθ⟩ := wns_exists_isBddSupp_theta (d := d)
  set R : ℝ := 1 + ρ₀ * b with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨e, he⟩ := exists_norm_eq (Rd d) (by positivity : (0 : ℝ) ≤ 2 * R)
  set fe : Rd d → ℝ := fun z => theta d z - theta d (z - e) with hfe
  have hθe_int : Integrable fun z => theta d (z - e) :=
    (integrable_testOn (theta d)).comp_sub_right e
  have hfeS : IsBddSupp fe (Mθ + Mθ) (2 * R + 1) := by
    refine ⟨(theta d).continuous.measurable.sub
      ((theta d).continuous.comp (continuous_id.sub continuous_const)).measurable,
      fun z => (abs_sub _ _).trans (add_le_add (hθ.abs_le z) (hθ.abs_le (z - e))),
      fun z hz => ?_⟩
    have h1 : theta d z = 0 := theta_eq_zero (by linarith)
    have h2 : theta d (z - e) = 0 := by
      refine theta_eq_zero ?_
      have := norm_sub_norm_le z e
      linarith
    simp only [hfe, h1, h2, sub_self]
  have hfe0 : ∫ z, fe z = 0 := by
    simp only [hfe]
    rw [integral_sub (integrable_testOn (theta d)) hθe_int,
      integral_sub_right_eq_self (fun z => theta d z) e, sub_self]
  have hL2 : MemLp (wnsFn (Ioo 0 b) fe) 2 volume :=
    memLp_wnsFn_of_subset measurableSet_Ioo Ioo_subset_Ioi_self (memLp_wnsFn_Ioi hfeS hfe0)
  have e1 : wnsFn (Ioo 0 b) (theta d : Rd d → ℝ) =
      ((univ : Set ℝ) ×ˢ ball (0 : Rd d) R).indicator (wnsFn (Ioo 0 b) fe) := by
    funext p
    by_cases hp : p ∈ (univ : Set ℝ) ×ˢ ball (0 : Rd d) R
    · rw [indicator_of_mem hp]
      have hy : ‖p.2‖ < R := by
        have := (mem_prod.1 hp).2
        rwa [mem_ball, dist_zero_right] at this
      unfold wnsFn
      by_cases ht : p.1 ∈ Ioo 0 b
      · rw [indicator_of_mem ht, indicator_of_mem ht, hfe,
          wnsConv_sub _ _ (integrable_testOn (theta d)) hθe_int]
        have h0 : wnsConv p.1 p.2 (fun z => theta d (z - e)) = 0 := by
          refine wnsConv_eq_zero (c := e) (r := 1) hρ ht.1 (fun z hz => ?_) ?_
          · have := wns_theta_ne_zero_imp hz
            rwa [sub_zero] at this
          · have h1 := norm_sub_norm_le e p.2
            rw [norm_sub_rev] at h1
            have h2 : ρ₀ * p.1 ≤ ρ₀ * b := mul_le_mul_of_nonneg_left ht.2.le hρ₀.le
            linarith
        rw [h0, sub_zero]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]
    · rw [indicator_of_notMem hp]
      have hy : R ≤ ‖p.2 - 0‖ := by
        rw [sub_zero]
        by_contra h
        exact hp (mk_mem_prod (mem_univ _) (by rw [mem_ball, dist_zero_right]; linarith))
      exact wnsFn_eq_zero_of_far subset_rfl hρ₀ hρ (fun z hz => wns_theta_ne_zero_imp hz) hy
  rw [e1]
  exact hL2.indicator (MeasurableSet.univ.prod measurableSet_ball)

end HigherDimLQGMetric

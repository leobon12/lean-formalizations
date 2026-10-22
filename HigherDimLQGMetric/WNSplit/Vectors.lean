import HigherDimLQGMetric.WNSplit.Band

/-!
# The fine, coarse and coarse-point white-noise vectors (packet S5a, D-WN′ (a), (b))

Source: MA3 Details (a) **D-WN′** (`planning/audits/MA3-sections-5-6.md`), construction (a)–(b),
(1)–(2); blueprint `prop:wn-split`.

For a cutoff `b > 0`, with F2's realization `⟨h, φ⟩ = W(gramVec (φ − (∫ φ) θ))`
(`gramVec f = bandVecM κ₀ (0, ∞) (f⁺ dz) (f⁻ dz)`):

* `wnsFine b φ = bandVecM κ₀ (0, b) (φ⁺ dz) (φ⁻ dz)`: the fine vector `k^φ_{(0,b)}`, with
  representative `wnsFn (0, b) φ` (`coeFn_wnsFine`); it vanishes outside `(0, b) × B(w, ρ + ρ₀ b)`
  when `tsupport φ ⊆ B(w, ρ)` (`ae_wnsFine_eq_zero`, finite range);
* `wnsPt b x = bandVecM κ₀ [b, ∞) δ_x (θ dz) − bandVecM κ₀ (0, b) (θ dz) 0`: the coarse field at `x`
  normalized so that the fine part of F2's normalization `⟨h, θ⟩ = 0` is removed, i.e.
  `"coarse(δ_x − θ) − fine(θ)"`; explicit representative `wnsPtRep b x` (`coeFn_wnsPt`) and
  increments `‖wnsPt b x − wnsPt b x'‖² ≤ L ‖x − x'‖² / b²` with `L` independent of `b`
  (`exists_norm_wnsPt_sub_sq_le`);
* `wnsCoarse b φ = gramVec (φ − (∫ φ) θ) − wnsFine b φ`, whose representative is
  `p ↦ ∫ φ(x) wnsPtRep b x p dx` (`coeFn_wnsCoarse`): the coarse vector is the integral of the
  coarse point vectors against `φ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN scaleKernel bandFun bandVecM IsPairable)

variable {d : ℕ}

/-! ## Definitions -/

/-- The fine vector `k^f_{(0,b)} = bandVecM κ₀ (0, b) (f⁺ dz) (f⁻ dz)` of a function `f`. -/
def wnsFine (b : ℝ) (f : Rd d → ℝ) : WN d :=
  bandVecM (kappa0 d) (Ioo 0 b) (posM f) (posM (-f))

/-- The coarse point vector at `x` for the cutoff `b`: `coarse(δ_x − θ) − fine(θ)`. -/
def wnsPt (b : ℝ) (x : Rd d) : WN d :=
  bandVecM (kappa0 d) (Ici b) (Measure.dirac x) (posM (theta d)) -
    bandVecM (kappa0 d) (Ioo 0 b) (posM (theta d)) 0

/-- The coarse vector of a test function: `gramVec (φ − (∫ φ) θ) − k^φ_{(0,b)}`. -/
def wnsCoarse (b : ℝ) (φ : TestRd d) : WN d := gramVec (subTheta φ) - wnsFine b φ

/-- The explicit representative of `wnsPt b x`:
`(t, y) ↦ 1_{t ≥ b} K_t(x − y) − 1_{t ≥ b} (θ ⋆ K_t)(y) − 1_{0 < t < b} (θ ⋆ K_t)(y)`. -/
def wnsPtRep (b : ℝ) (x : Rd d) (p : ℝ × Rd d) : ℝ :=
  (Ici b).indicator (fun t => scaleKernel (kappa0 d) t (x - p.2)) p.1 -
    wnsFn (Ici b) (theta d : Rd d → ℝ) p - wnsFn (Ioo 0 b) (theta d : Rd d → ℝ) p

/-! ## Pairability -/

theorem wns_isPairable_theta_fine [NeZero d] {b : ℝ} (hb : 0 < b) :
    IsPairable (kappa0 d) (Ioo 0 b) (posM (theta d)) 0 := by
  obtain ⟨Mθ, hθ⟩ := wns_exists_isBddSupp_theta (d := d)
  rw [IsPairable, HigherDimLFPP.bandFun_zero_measure, sub_zero,
    bandFun_posM_eq_wnsFn hθ wns_theta_nonneg]
  exact memLp_wnsFn_theta hb

theorem memLp_wnsFn_fine [NeZero d] {b : ℝ} (hb : 0 < b) (φ : TestRd d) :
    MemLp (wnsFn (Ioo 0 b) (φ : Rd d → ℝ)) 2 volume := by
  obtain ⟨M, D, hS⟩ := exists_isBddSupp_subTheta φ
  have h1 : MemLp (wnsFn (Ioo 0 b) (subTheta φ)) 2 volume :=
    memLp_wnsFn_of_subset measurableSet_Ioo Ioo_subset_Ioi_self
      (memLp_wnsFn_Ioi hS (integral_subTheta φ))
  have h2 := memLp_wnsFn_theta (d := d) hb
  have hφi : Integrable (φ : Rd d → ℝ) := integrable_testOn φ
  have hθi : Integrable (theta d : Rd d → ℝ) := integrable_testOn (theta d)
  have e : wnsFn (Ioo 0 b) (φ : Rd d → ℝ) =
      wnsFn (Ioo 0 b) (subTheta φ) + (∫ y, φ y) • wnsFn (Ioo 0 b) (theta d : Rd d → ℝ) := by
    funext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wnsFn]
    by_cases ht : p.1 ∈ Ioo 0 b
    · rw [indicator_of_mem ht, indicator_of_mem ht, indicator_of_mem ht,
        show subTheta φ = fun z => φ z - (∫ y, φ y) * theta d z from rfl,
        wnsConv_sub_mul p.1 p.2 hφi hθi]
      ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, indicator_of_notMem ht]
      ring
  rw [e]
  exact h1.add (h2.const_smul _)

theorem wns_isPairable_fine [NeZero d] {b : ℝ} (hb : 0 < b) (φ : TestRd d) :
    IsPairable (kappa0 d) (Ioo 0 b) (posM φ) (posM (-(φ : Rd d → ℝ))) := by
  obtain ⟨M, D, hφ'⟩ := exists_isBddSupp_testOn φ
  have hφ : IsBddSupp (φ : Rd d → ℝ) M D := hφ'
  rw [IsPairable, bandFun_posM_sub_eq_wnsFn hφ]
  exact memLp_wnsFn_fine hb φ

theorem wns_isPairable_pt {b : ℝ} (hb : 0 < b) (x : Rd d) :
    IsPairable (kappa0 d) (Ici b) (Measure.dirac x) (posM (theta d)) := by
  obtain ⟨Mθ, hθ⟩ := wns_exists_isBddSupp_theta (d := d)
  have := isFiniteMeasure_posM hθ
  refine HigherDimLFPP.isPairable_of_subset_Ici wns_isLFPPKernel measurableSet_Ici hb subset_rfl
    _ _ ?_ (D := max ‖x‖ 1) ?_ ?_
  · rw [posM_real_univ_of_nonneg hθ wns_theta_nonneg, integral_theta, probReal_univ]
  · exact (ae_dirac_iff (measurableSet_le continuous_norm.measurable measurable_const)).2
      (le_max_left _ _)
  · exact (ae_posM_norm_le hθ).mono fun z hz => hz.trans (le_max_right _ _)

/-! ## Representatives -/

theorem coeFn_wnsFine [NeZero d] {b : ℝ} (hb : 0 < b) (φ : TestRd d) :
    (wnsFine b φ : ℝ × Rd d → ℝ) =ᵐ[volume] wnsFn (Ioo 0 b) (φ : Rd d → ℝ) := by
  obtain ⟨M, D, hφ'⟩ := exists_isBddSupp_testOn φ
  have hφ : IsBddSupp (φ : Rd d → ℝ) M D := hφ'
  have h := HigherDimLFPP.coeFn_bandVecM (wns_isPairable_fine hb φ)
  rw [bandFun_posM_sub_eq_wnsFn hφ] at h
  exact h

theorem wns_coeFn_gramVec_subTheta [NeZero d] (φ : TestRd d) :
    (gramVec (subTheta φ) : ℝ × Rd d → ℝ) =ᵐ[volume] wnsFn (Ioi 0) (subTheta φ) := by
  obtain ⟨M, D, hS⟩ := exists_isBddSupp_subTheta φ
  have h := HigherDimLFPP.coeFn_bandVecM (wns_isPairable_Ioi_posM hS (integral_subTheta φ))
  rw [bandFun_posM_sub_eq_wnsFn hS] at h
  exact h

theorem wns_bandFun_dirac_apply (S : Set ℝ) (x : Rd d) (p : ℝ × Rd d) :
    bandFun (kappa0 d) S (Measure.dirac x) p =
      S.indicator (fun t => scaleKernel (kappa0 d) t (x - p.2)) p.1 := by
  simp only [HigherDimLFPP.bandFun_apply, HigherDimLFPP.scaleConv, integral_dirac]

theorem coeFn_wnsPt [NeZero d] {b : ℝ} (hb : 0 < b) (x : Rd d) :
    (wnsPt b x : ℝ × Rd d → ℝ) =ᵐ[volume] wnsPtRep b x := by
  obtain ⟨Mθ, hθ⟩ := wns_exists_isBddSupp_theta (d := d)
  filter_upwards [Lp.coeFn_sub
      (bandVecM (kappa0 d) (Ici b) (Measure.dirac x) (posM (theta d)))
      (bandVecM (kappa0 d) (Ioo 0 b) (posM (theta d)) 0),
    HigherDimLFPP.coeFn_bandVecM (wns_isPairable_pt hb x),
    HigherDimLFPP.coeFn_bandVecM (wns_isPairable_theta_fine (d := d) hb)] with p h1 h2 h3
  simp only [wnsPt]
  rw [h1, Pi.sub_apply, h2, h3]
  simp only [Pi.sub_apply, HigherDimLFPP.bandFun_zero_measure, Pi.zero_apply, sub_zero,
    wnsPtRep]
  rw [bandFun_posM_eq_wnsFn hθ wns_theta_nonneg, bandFun_posM_eq_wnsFn hθ wns_theta_nonneg,
    wns_bandFun_dirac_apply]

theorem measurable_wnsPtRep (b : ℝ) :
    Measurable fun q : Rd d × (ℝ × Rd d) => wnsPtRep b q.1 q.2 := by
  classical
  obtain ⟨Mθ, hθ⟩ := wns_exists_isBddSupp_theta (d := d)
  have hκ := wns_isLFPPKernel (d := d)
  have hK : Measurable fun q : Rd d × (ℝ × Rd d) => scaleKernel (kappa0 d) q.2.1 (q.1 - q.2.2) := by
    unfold scaleKernel
    exact (measurable_snd.fst.pow_const _).mul (hκ.continuous.measurable.comp
      (measurable_snd.fst.inv.smul (measurable_fst.sub measurable_snd.snd)))
  have h1 : Measurable fun q : Rd d × (ℝ × Rd d) =>
      (Ici b).indicator (fun t => scaleKernel (kappa0 d) t (q.1 - q.2.2)) q.2.1 := by
    simp only [indicator_apply]
    exact Measurable.ite (measurableSet_Ici.preimage measurable_snd.fst) hK measurable_const
  exact (h1.sub ((measurable_wnsFn measurableSet_Ici hθ).comp measurable_snd)).sub
    ((measurable_wnsFn measurableSet_Ioo hθ).comp measurable_snd)

/-- **The coarse vector is the integral of the point vectors** (pointwise identity of
representatives): `∫ φ(x) wnsPtRep b x p dx = wnsFn (0, ∞) (φ − (∫ φ) θ) p − wnsFn (0, b) φ p`. -/
theorem integral_mul_wnsPtRep {b : ℝ} (hb : 0 < b) (φ : TestRd d) (p : ℝ × Rd d) :
    ∫ x, φ x * wnsPtRep b x p =
      wnsFn (Ioi 0) (subTheta φ) p - wnsFn (Ioo 0 b) (φ : Rd d → ℝ) p := by
  obtain ⟨t, y⟩ := p
  have hφi : Integrable (φ : Rd d → ℝ) := integrable_testOn φ
  have hθi : Integrable (theta d : Rd d → ℝ) := integrable_testOn (theta d)
  have hsub : wnsConv t y (subTheta φ) =
      wnsConv t y (φ : Rd d → ℝ) - (∫ y, φ y) * wnsConv t y (theta d : Rd d → ℝ) := by
    rw [show subTheta φ = fun z => φ z - (∫ y, φ y) * theta d z from rfl,
      wnsConv_sub_mul t y hφi hθi]
  rcases lt_or_ge t b with htb | hbt
  · have h1 : t ∉ Ici b := fun h => absurd (mem_Ici.1 h) (not_le.2 htb)
    rcases le_or_gt t 0 with ht0 | ht0
    · have h2 : t ∉ Ioo 0 b := fun h => absurd h.1 (not_lt.2 ht0)
      have h3 : t ∉ Ioi 0 := fun h => absurd (mem_Ioi.1 h) (not_lt.2 ht0)
      have e : (fun x => φ x * wnsPtRep b x (t, y)) = fun _ => 0 := by
        funext x
        simp only [wnsPtRep, wnsFn, indicator_of_notMem h1, indicator_of_notMem h2, sub_self,
          mul_zero]
      rw [e, integral_zero]
      simp only [wnsFn, indicator_of_notMem h2, indicator_of_notMem h3, sub_self]
    · have h2 : t ∈ Ioo 0 b := ⟨ht0, htb⟩
      have h3 : t ∈ Ioi 0 := ht0
      have e : (fun x => φ x * wnsPtRep b x (t, y)) =
          fun x => -wnsConv t y (theta d : Rd d → ℝ) * φ x := by
        funext x
        simp only [wnsPtRep, wnsFn, indicator_of_notMem h1, indicator_of_mem h2]
        ring
      rw [e, integral_const_mul]
      simp only [wnsFn, indicator_of_mem h2, indicator_of_mem h3]
      rw [hsub]
      ring
  · have h1 : t ∈ Ici b := hbt
    have h2 : t ∉ Ioo 0 b := fun h => absurd h.2 (not_lt.2 hbt)
    have h3 : t ∈ Ioi 0 := lt_of_lt_of_le hb hbt
    have e : (fun x => φ x * wnsPtRep b x (t, y)) =
        fun x => scaleKernel (kappa0 d) t (x - y) * φ x -
          wnsConv t y (theta d : Rd d → ℝ) * φ x := by
      funext x
      simp only [wnsPtRep, wnsFn, indicator_of_mem h1, indicator_of_notMem h2]
      ring
    rw [e, integral_sub (integrable_scaleKernel_mul_wns t y hφi) (hφi.const_mul _),
      integral_const_mul]
    simp only [wnsFn, indicator_of_mem h3, indicator_of_notMem h2, sub_zero]
    rw [hsub]
    unfold wnsConv
    ring

theorem coeFn_wnsCoarse [NeZero d] {b : ℝ} (hb : 0 < b) (φ : TestRd d) :
    (wnsCoarse b φ : ℝ × Rd d → ℝ) =ᵐ[volume] fun p => ∫ x, φ x * wnsPtRep b x p := by
  filter_upwards [Lp.coeFn_sub (gramVec (subTheta φ)) (wnsFine b φ), wns_coeFn_gramVec_subTheta φ,
    coeFn_wnsFine hb φ] with p h1 h2 h3
  rw [wnsCoarse, h1, Pi.sub_apply, h2, h3, integral_mul_wnsPtRep hb φ p]

/-! ## Finite range of the fine vectors -/

/-- **Finite range** (MA3 D-WN′ (2)): if `tsupport φ ⊆ B(w, ρ)` then `k^φ_{(0,b)}` vanishes a.e.
outside `(0, b) × B(w, ρ + ρ₀ b)`. -/
theorem ae_wnsFine_eq_zero [NeZero d] {b : ℝ} (hb : 0 < b) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ : ∀ v : Rd d, ρ₀ ≤ ‖v‖ → kappa0 d v = 0) (φ : TestRd d) {w : Rd d} {ρ : ℝ}
    (hφ : tsupport (φ : Rd d → ℝ) ⊆ ball w ρ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × Rd d)), p ∉ Ioo 0 b ×ˢ ball w (ρ + ρ₀ * b) →
      (wnsFine b φ : ℝ × Rd d → ℝ) p = 0 := by
  filter_upwards [coeFn_wnsFine hb φ] with p hp hpn
  rw [hp]
  by_cases ht : p.1 ∈ Ioo 0 b
  · have hy : ρ + ρ₀ * b ≤ ‖p.2 - w‖ := by
      by_contra h
      exact hpn (mem_prod.2 ⟨ht, by rw [mem_ball, dist_eq_norm]; exact not_le.1 h⟩)
    refine wnsFn_eq_zero_of_far subset_rfl hρ₀ hρ (fun z hz => ?_) hy
    have h := hφ (subset_tsupport _ hz)
    rwa [mem_ball, dist_eq_norm] at h
  · simp only [wnsFn, indicator_of_notMem ht]

/-! ## Increments of the coarse point vectors -/

theorem wns_scalePair_dirac {t : ℝ} (x x' : Rd d) :
    HigherDimLFPP.scalePair (kappa0 d) t (Measure.dirac x) (Measure.dirac x') (Measure.dirac x)
      (Measure.dirac x') =
      2 * (1 - HigherDimLFPP.autoCorr (kappa0 d) (t⁻¹ • (x - x'))) / t := by
  have hκ := wns_isLFPPKernel (d := d)
  have e : t⁻¹ • (x' - x) = -(t⁻¹ • (x - x')) := by rw [← smul_neg, neg_sub]
  simp only [HigherDimLFPP.scalePair, HigherDimLFPP.mixInt, Measure.dirac_prod_dirac,
    integral_dirac, sub_self, smul_zero, HigherDimLFPP.autoCorr_zero hκ, e,
    HigherDimLFPP.autoCorr_neg]
  ring

/-- **Increments of the coarse point vectors**: `‖wnsPt b x − wnsPt b x'‖² ≤ L ‖x − x'‖² / b²`,
with `L` independent of `b` (from `1 − C(v) ≤ L ‖v‖²` and `∫_b^∞ 2 t⁻³ dt = b⁻²`). -/
theorem exists_norm_wnsPt_sub_sq_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ b : ℝ, 0 < b → ∀ x x' : Rd d,
      ‖wnsPt b x - wnsPt b x'‖ ^ 2 ≤ L * ‖x - x'‖ ^ 2 / b ^ 2 := by
  have hκ := wns_isLFPPKernel (d := d)
  obtain ⟨L, hL0, hL⟩ := HigherDimLFPP.exists_one_sub_autoCorr_le hκ
  refine ⟨L, hL0, fun b hb x x' => ?_⟩
  obtain ⟨Mθ, hθ⟩ := wns_exists_isBddSupp_theta (d := d)
  have := isFiniteMeasure_posM hθ
  have e1 : wnsPt b x - wnsPt b x' =
      bandVecM (kappa0 d) (Ici b) (Measure.dirac x) (Measure.dirac x') := by
    rw [wnsPt, wnsPt, sub_sub_sub_cancel_right,
      HigherDimLFPP.bandVecM_sub_bandVecM hκ (wns_isPairable_pt hb x) (wns_isPairable_pt hb x'),
      add_comm (posM (theta d)) (Measure.dirac x'), HigherDimLFPP.bandVecM_add_right hκ]
  have hD : ∀ z : Rd d, ‖z‖ ≤ max ‖x‖ ‖x'‖ → ∀ᵐ u ∂(Measure.dirac z), ‖u‖ ≤ max ‖x‖ ‖x'‖ :=
    fun z hz => (ae_dirac_iff (measurableSet_le continuous_norm.measurable measurable_const)).2 hz
  have hS0 : Ici b ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hb ht
  have hp : IsPairable (kappa0 d) (Ici b) (Measure.dirac x) (Measure.dirac x') :=
    HigherDimLFPP.isPairable_of_subset_Ici hκ measurableSet_Ici hb subset_rfl _ _
      (by rw [probReal_univ, probReal_univ]) (hD x (le_max_left _ _))
      (hD x' (le_max_right _ _))
  set c : ℝ := 2 * L * ‖x - x'‖ ^ 2 with hc
  have hbound : ∀ t ∈ Ici b, HigherDimLFPP.scalePair (kappa0 d) t (Measure.dirac x)
      (Measure.dirac x') (Measure.dirac x) (Measure.dirac x') ≤ c * t ^ (-3 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := hS0 ht
    rw [wns_scalePair_dirac, show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le,
      Real.rpow_natCast]
    have h1 := (hL (t⁻¹ • (x - x'))).2
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)] at h1
    calc 2 * (1 - HigherDimLFPP.autoCorr (kappa0 d) (t⁻¹ • (x - x'))) / t
        ≤ 2 * (L * (t⁻¹ * ‖x - x'‖) ^ 2) / t := by gcongr
      _ = c * (t ^ 3)⁻¹ := by rw [hc]; field_simp
  have hint : IntegrableOn (fun t : ℝ => c * t ^ (-3 : ℝ)) (Ici b) := by
    have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hb).const_mul c
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 h
  have hval : ∫ t in Ici b, c * t ^ (-3 : ℝ) = L * ‖x - x'‖ ^ 2 / b ^ 2 := by
    rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hb,
      show (-3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hb.le, Real.rpow_natCast, hc]
    field_simp
    ring
  rw [e1, ← HigherDimLFPP.scaleCov_self,
    HigherDimLFPP.scaleCov_eq_integral hκ measurableSet_Ici hS0 hp hp, ← hval]
  exact setIntegral_mono_on (HigherDimLFPP.integrableOn_scalePair hκ measurableSet_Ici hS0 hp hp)
    hint measurableSet_Ici hbound

end HigherDimLQGMetric

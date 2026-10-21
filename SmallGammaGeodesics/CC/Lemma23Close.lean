import SmallGammaGeodesics.CC.ZoomNIC
import SmallGammaGeodesics.CC.PullbackCov
import SmallGammaGeodesics.NIC.Transport
import Mathlib.Probability.Moments.Variance

/-!
# [3] Lemma 2.3*, part 1: closeness of the coupled pairings (track CC, packet CC6a, T2)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D9**, step 3.

Setting: a sequence of near-identity couplings on `B_R` (`IsNICCoupling`, CC4): on `(Ω n, P n)`,
whole-plane GFFs `h n`, `h̄ n` and a harmonic `K n` with `⟨h n, τ_n g⟩ = ⟨h̄ n, g⟩ + ∫ K n g` for
`g` supported in `B_R`, where `τ_n g = |det DΦ_n| (g ∘ Φ_n)`, `Φ_n` is an `ε_n`-near-identity
diffeomorphism (`IsNearIdDiffeo`, `‖Φ_n − id‖ ≤ ε_n`), and `E sup_{B̄_{R/2}} |K n − K n (0)| ≤ ε_n`,
with `ε_n → 0`.

**Pairing closeness** (`tendsto_prob_pairing`): for every test function `φ` supported in `B̄_{R/2}`,
`⟨h̄ n, φ⟩ − ⟨h n, φ⟩ + (∫ φ) K n(0) → 0` in probability. Indeed, on the coupling event it equals
`⟨h n, τ_n φ − φ⟩ − ∫ (K n − K n(0)) φ`:
* `τ_n φ − φ` has mean zero and tends to `0` uniformly with supports in a fixed ball
  (`tendstoUniformly_transport`, `transport_eq_zero_of_lt_norm`), so its `logCov` tends to `0`
  (CC1's `tendsto_logCov_sub_of_tendstoUniformly`, i.e. [3] (2.5)), and Chebyshev's inequality for
  the Gaussian pairing applies (`prob_le_logCov_of_wp`);
* `|∫ (K − K(0)) φ| ≤ sup_{B̄_{R/2}} |K − K(0)| · ∫ |φ|` (`abs_integral_mul_sub_le`), and Markov's
  inequality applies to the supremum (`tendsto_prob_supDev`).

The quantities `⟨h̄ n, e₀⟩ − ⟨h n, e₀⟩` for mean-zero `e₀` (the coordinates of D9 step 3) and
`⟨h̄ n, ρ⟩ − ⟨h n, ρ⟩ + K n(0)` for `∫ ρ = 1` (the normalization of D9 step 6) are both of this
form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## 1. Elementary helpers -/

/-- a function vanishing off a closed set `C` has topological support in `C` -/
theorem tsupport_subset_of_eq_zero {f : ℂ → ℝ} {C : Set ℂ} (hC : IsClosed C)
    (h : ∀ x ∉ C, f x = 0) : tsupport f ⊆ C :=
  closure_minimal (fun x hx => by_contra fun hxC => hx (h x hxC)) hC

/-- a test function supported in `B̄_ρ` vanishes for `ρ < ‖y‖` -/
theorem test_eq_zero_of_lt_norm {φ : TestC} {ρ : ℝ} (hφ : tsupport (φ : ℂ → ℝ) ⊆ closedBall 0 ρ)
    {y : ℂ} (hy : ρ < ‖y‖) : φ y = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => by
    have := mem_closedBall_zero_iff.1 (hφ h)
    linarith

/-- **Chebyshev for a Gaussian pairing**: `P(t ≤ |⟨h, φ⟩|) ≤ logCov(φ, φ)/t²` for a whole-plane GFF
`h` and a mean-zero test function `φ`. -/
theorem prob_le_logCov_of_wp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (φ : TestC0) {t : ℝ}
    (ht : 0 < t) : P {ω | t ≤ |h ω φ.1|} ≤ ENNReal.ofReal (logCov φ.1 φ.1 / t ^ 2) := by
  have hm := hh.gaussian.aemeasurable φ
  have h1 := meas_ge_le_variance_div_sq (hh.memLp_two φ) ht
  have hmean : P[fun ω => h ω φ.1] = 0 := hh.centered φ
  have hvar : variance (fun ω => h ω φ.1) P = logCov φ.1 φ.1 := by
    rw [← covariance_self hm, hh.covariance_eq φ φ]
  rw [hmean, hvar] at h1
  simpa only [sub_zero] using h1

/-- **The `K`-term of the coupling**: for `k` measurable and continuous on `B̄_ρ` and a test
function
`φ` supported in `B̄_ρ`, `|∫ k φ − (∫ φ) k(0)| ≤ sup_{B̄_ρ} |k − k(0)| · ∫ |φ|`. -/
theorem abs_integral_mul_sub_le {k : ℂ → ℝ} {ρ : ℝ} (hk : ContinuousOn k (closedBall 0 ρ))
    (hkm : Measurable k) {φ : TestC} (hφ : tsupport (φ : ℂ → ℝ) ⊆ closedBall 0 ρ) :
    |(∫ y, k y * φ y) - (∫ y, φ y) * k 0| ≤ (supDev k ρ).toReal * ∫ y, |φ y| := by
  have hφi : Integrable (fun y => φ y) := GFFInv.integrable_test φ
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn hk
  have hzero : ∀ y, y ∉ closedBall (0 : ℂ) ρ → φ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hφ h)
  have hkφ : Integrable (fun y => k y * φ y) := by
    refine Integrable.mono' (hφi.norm.const_mul (max M 0)) (hkm.aestronglyMeasurable.mul
      hφi.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ closedBall (0 : ℂ) ρ
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hM y hy).trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hzero y hy, mul_zero, norm_zero, mul_zero]
  have e : (∫ y, k y * φ y) - (∫ y, φ y) * k 0 = ∫ y, (k y - k 0) * φ y := by
    rw [← integral_mul_const, ← integral_sub hkφ (hφi.mul_const _)]
    congr 1
    funext y
    ring
  rw [e]
  set σ := (supDev k ρ).toReal
  have hσ : 0 ≤ σ := ENNReal.toReal_nonneg
  calc |∫ y, (k y - k 0) * φ y| ≤ ∫ y, |(k y - k 0) * φ y| := by
        rw [← Real.norm_eq_abs]
        exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Real.norm_eq_abs])
    _ ≤ ∫ y, σ * |φ y| := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
          (hφi.abs.const_mul σ) (ae_of_all _ fun y => ?_)
        show |(k y - k 0) * φ y| ≤ σ * |φ y|
        rw [abs_mul]
        by_cases hy : y ∈ closedBall (0 : ℂ) ρ
        · exact mul_le_mul_of_nonneg_right (abs_sub_le_toReal_supDev hk hy) (abs_nonneg _)
        · rw [hzero y hy, abs_zero, mul_zero, mul_zero]
    _ = σ * ∫ y, |φ y| := integral_const_mul σ _

/-! ## 2. Near-identity transports converge to the identity (deterministic) -/

/-- The transport `τ φ = jac Φ · (φ ∘ Φ)` vanishes far out: if `‖Φ − id‖ ≤ b` and `φ = 0` off
`B̄_ρ`, then `τ φ = 0` off `B̄_{ρ + b}`. -/
theorem transport_eq_zero_of_lt_norm (D : NIC.NearIdPair) {b ρ : ℝ}
    (hΦ : ∀ x, ‖D.Φ x - x‖ ≤ b) {φ : TestC} (hφ : ∀ y, ρ < ‖y‖ → φ y = 0) {x : ℂ}
    (hx : ρ + b < ‖x‖) : D.transport φ x = 0 := by
  rw [NIC.NearIdPair.transport_apply]
  have h1 : ‖x‖ - ‖D.Φ x - x‖ ≤ ‖D.Φ x‖ := by
    have := norm_sub_norm_le x (x - D.Φ x)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  rw [hφ (D.Φ x) (by linarith [hΦ x]), mul_zero]

/-- **Uniform convergence of near-identity transports** (deterministic part of D9 step 3): if
`δ(D n) → 0` and `‖Φ_n − id‖ ≤ b n → 0`, then `τ_n φ → φ` uniformly. -/
theorem tendstoUniformly_transport {D : ℕ → NIC.NearIdPair} {b : ℕ → ℝ}
    (hδ : Tendsto (fun n => (D n).δ) atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hΦ : ∀ n x, ‖(D n).Φ x - x‖ ≤ b n) (φ : TestC) :
    TendstoUniformly (fun n x => (D n).transport φ x) (fun x => φ x) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have huc := φ.hasCompactSupport.uniformContinuous_of_continuous φ.continuous
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨η, hη, hηφ⟩ := huc (ε / 2) (by positivity)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h1 : ∀ᶠ n in atTop, b n < η := hb.eventually (gt_mem_nhds hη)
  have h2 : ∀ᶠ n in atTop, (D n).δ < ε / (6 * (M + 1)) :=
    hδ.eventually (gt_mem_nhds (by positivity))
  filter_upwards [h1, h2] with n hn1 hn2 x
  rw [NIC.NearIdPair.transport_apply, Real.dist_eq]
  set j := NIC.jac (D n).Φ x
  obtain ⟨hj1, hj2⟩ := (D n).jac_mem_Icc x
  have hδ0 := (D n).δ_nonneg
  have hj : |1 - j| ≤ 3 * (D n).δ := by
    rw [abs_le]; constructor <;> linarith
  have hφd : |φ x - φ ((D n).Φ x)| < ε / 2 := by
    have := hηφ (a := x) (b := (D n).Φ x) (by
      rw [dist_comm, dist_eq_norm]; exact lt_of_le_of_lt (hΦ n x) hn1)
    rwa [Real.dist_eq] at this
  have hφb : |φ ((D n).Φ x)| ≤ M := by
    have := hM ((D n).Φ x); rwa [Real.norm_eq_abs] at this
  have hsmall : 3 * (D n).δ * M < ε / 2 := by
    have h6 : 6 * (D n).δ * (M + 1) < ε := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 6 * (M + 1))).1 hn2
      linarith
    nlinarith
  calc |φ x - j * φ ((D n).Φ x)| = |(φ x - φ ((D n).Φ x)) + (1 - j) * φ ((D n).Φ x)| := by
        congr 1; ring
    _ ≤ |φ x - φ ((D n).Φ x)| + |1 - j| * |φ ((D n).Φ x)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
        have : |1 - j| * |φ ((D n).Φ x)| ≤ 3 * (D n).δ * M :=
          mul_le_mul hj hφb (abs_nonneg _) (by linarith)
        linarith
    _ = ε := add_halves ε

/-- `∫ (τ φ − φ) = 0` -/
theorem integral_transport_sub (D : NIC.NearIdPair) (φ : TestC) :
    ∫ x, (D.transport φ - φ) x = 0 := by
  show ∫ x, (D.transport φ x - φ x) = 0
  rw [integral_sub (GFFInv.integrable_test _) (GFFInv.integrable_test _), D.integral_transport,
    sub_self]

/-- `τ φ − φ` as a mean-zero test function -/
def transportSub0 (D : NIC.NearIdPair) (φ : TestC) : TestC0 :=
  ⟨D.transport φ - φ, integral_transport_sub D φ⟩

/-- **[3] (2.5) for near-identity transports**: `logCov(τ_n φ − φ, τ_n φ − φ) → 0`. -/
theorem tendsto_logCov_transportSub0 {D : ℕ → NIC.NearIdPair} {b : ℕ → ℝ}
    (hδ : Tendsto (fun n => (D n).δ) atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hΦ : ∀ n x, ‖(D n).Φ x - x‖ ≤ b n) (φ : TestC) :
    Tendsto (fun n => logCov (transportSub0 (D n) φ).1 (transportSub0 (D n) φ).1) atTop (𝓝 0) := by
  obtain ⟨Rφ, hRφ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  have hφ0 : ∀ y, Rφ < ‖y‖ → φ y = 0 := fun y hy => test_eq_zero_of_lt_norm hRφ hy
  have hb1 : ∀ᶠ n in atTop, b n < 1 := hb.eventually (gt_mem_nhds one_pos)
  have hgR : ∀ᶠ n in atTop, ∀ x, Rφ + 1 < ‖x‖ → (D n).transport φ x = 0 := by
    filter_upwards [hb1] with n hn x hx
    exact transport_eq_zero_of_lt_norm (D n) (hΦ n) hφ0 (by linarith)
  have hg₀R : ∀ x, Rφ + 1 < ‖x‖ → φ x = 0 := fun x hx => hφ0 x (by linarith)
  exact tendsto_logCov_sub_of_tendstoUniformly (g := fun n x => (D n).transport φ x)
    (g₀ := fun x => φ x) (tendstoUniformly_transport hδ hb hΦ φ) hgR hg₀R

/-! ## 3. Pairing closeness in probability -/

/-- **Markov for the supremum**: if `E sup_{B̄_ρ} |K n − K n(0)| ≤ ε_n → 0`, the supremum tends to
`0`
in probability. -/
theorem tendsto_prob_supDev {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} {K : ∀ n, Ω n → ℂ → ℝ} {ρ : ℝ} {ε : ℕ → ℝ}
    (hm : ∀ n, AEMeasurable (fun ω => supDev (K n ω) ρ) (P n))
    (hsup : ∀ n, ∫⁻ ω, supDev (K n ω) ρ ∂(P n) ≤ ENNReal.ofReal (ε n))
    (hε : Tendsto ε atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => P n {ω | ENNReal.ofReal t ≤ supDev (K n ω) ρ}) atTop (𝓝 0) := by
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
  have hup : Tendsto (fun n => ENNReal.ofReal (ε n) / ENNReal.ofReal t) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal hε) (Or.inr ht0)
    rwa [ENNReal.ofReal_zero, ENNReal.zero_div] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le)
    fun n => ?_
  exact (meas_ge_le_lintegral_div (hm n) ht0 ENNReal.ofReal_ne_top).trans
    (ENNReal.div_le_div_right (hsup n) _)

/-- the transport pair of a near-identity diffeomorphism with `0 ≤ ε ≤ 1/32` -/
abbrev nicPair {Φ Ψ : ℂ → ℂ} {U : Set ℂ} {ε : ℝ} (hΦ : IsNearIdDiffeo Φ Ψ U ε)
    (hε : ε ≤ 1 / 32) : NIC.NearIdPair :=
  NIC.NearIdPair.ofDiffeo hΦ ((norm_nonneg _).trans (hΦ.deriv_close 0)) hε

/-- **Pairing closeness in probability** (CC0 D9 step 3, in the form used for the coordinates and
the normalization): along a sequence of `ε_n`-near-identity couplings on `B_R` with `ε_n → 0`, for
every test function `φ` supported in `B̄_{R/2}`,
`P_n(η ≤ |⟨h̄ n, φ⟩ − ⟨h n, φ⟩ + (∫ φ) K n(0)|) → 0` for every `η > 0`. -/
theorem tendsto_prob_pairing {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {R : ℝ} (hR : 0 < R)
    {Φ Ψ : ℕ → ℂ → ℂ} {B ε : ℕ → ℝ} {h hbar : ∀ n, Ω n → DistC} {K : ∀ n, Ω n → ℂ → ℝ}
    (hc : ∀ n, IsNICCoupling (P n) (Φ n) (ball 0 R) (B n) (h n) (hbar n) (K n))
    (hΦ : ∀ n, IsNearIdDiffeo (Φ n) (Ψ n) (ball 0 R) (ε n))
    (hΦsub : ∀ n x, ‖Φ n x - x‖ ≤ ε n) (hε32 : ∀ n, ε n ≤ 1 / 32)
    (hε : Tendsto ε atTop (𝓝 0))
    (hsup : ∀ n, ∫⁻ ω, supDev (K n ω) (R / 2) ∂(P n) ≤ ENNReal.ofReal (ε n))
    {φ : TestC} (hφ : tsupport (φ : ℂ → ℝ) ⊆ closedBall 0 (R / 2)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => P n {ω | η ≤ |hbar n ω φ - h n ω φ + (∫ x, φ x) * K n ω 0|}) atTop
      (𝓝 0) := by
  set D : ℕ → NIC.NearIdPair := fun n => nicPair (hΦ n) (hε32 n) with hDdef
  have hDδ : Tendsto (fun n => (D n).δ) atTop (𝓝 0) := by
    have := hε.const_mul 2
    rwa [mul_zero] at this
  have hDΦ : ∀ n x, ‖(D n).Φ x - x‖ ≤ ε n := hΦsub
  set L : ℝ := ∫ y, |φ y| with hL
  have hL0 : 0 ≤ L := integral_nonneg fun y => abs_nonneg _
  set t : ℝ := η / (2 * (L + 1)) with ht
  have ht0 : 0 < t := by positivity
  have hsub : (closedBall (0 : ℂ) (R / 2)) ⊆ ball 0 R := closedBall_subset_ball (by linarith)
  -- the two bounds
  have hA : Tendsto (fun n => P n {ω | η / 2 ≤ |h n ω (transportSub0 (D n) φ).1|}) atTop
      (𝓝 0) := by
    have hlog := tendsto_logCov_transportSub0 hDδ hε hDΦ φ
    have hup : Tendsto (fun n => ENNReal.ofReal
        (logCov (transportSub0 (D n) φ).1 (transportSub0 (D n) φ).1 / (η / 2) ^ 2)) atTop
        (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (hlog.div_const ((η / 2) ^ 2))
      rwa [zero_div, ENNReal.ofReal_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le)
      fun n => prob_le_logCov_of_wp (hc n).isWholePlaneGFF _ (by positivity)
  have hB : Tendsto (fun n => P n {ω | ENNReal.ofReal t ≤ supDev (K n ω) (R / 2)}) atTop
      (𝓝 0) :=
    tendsto_prob_supDev (fun n => (measurable_supDev (by positivity) (by linarith)
      (hc n).measurable fun ω => ((hc n).harmonic ω).continuousOn).aemeasurable) hsup hε ht0
  -- on the coupling event, the event is contained in the union of the two events
  have hincl : ∀ n, {ω | η ≤ |hbar n ω φ - h n ω φ + (∫ x, φ x) * K n ω 0|} ≤ᵐ[P n]
      ({ω | η / 2 ≤ |h n ω (transportSub0 (D n) φ).1|} ∪
        {ω | ENNReal.ofReal t ≤ supDev (K n ω) (R / 2)}) := by
    intro n
    filter_upwards [(hc n).coupling] with ω hω hmem
    have hcpl : h n ω ((D n).transport φ) = hbar n ω φ + ∫ y, K n ω y * φ y :=
      hω φ ((D n).transport φ) (hφ.trans hsub) fun x => rfl
    have hKc : ContinuousOn (K n ω) (closedBall 0 (R / 2)) :=
      ((hc n).harmonic ω).continuousOn.mono hsub
    have hKm : Measurable (K n ω) :=
      (hc n).measurable.comp (measurable_const.prodMk measurable_id)
    have hbound := abs_integral_mul_sub_le hKc hKm hφ
    set σ := (supDev (K n ω) (R / 2)).toReal with hσ
    have hZ : hbar n ω φ - h n ω φ + (∫ x, φ x) * K n ω 0 =
        h n ω (transportSub0 (D n) φ).1 - ((∫ y, K n ω y * φ y) - (∫ y, φ y) * K n ω 0) := by
      have e : h n ω (transportSub0 (D n) φ).1 = h n ω ((D n).transport φ) - h n ω φ :=
        map_sub (h n ω) _ _
      rw [e, hcpl]
      ring
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    obtain ⟨h1, h2⟩ := hnot
    have hσt : σ ≤ t := (ENNReal.toReal_lt_of_lt_ofReal h2).le
    have htL : t * L ≤ η / 2 := by
      rw [ht, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hlt : |hbar n ω φ - h n ω φ + (∫ x, φ x) * K n ω 0| < η := by
      rw [hZ]
      calc |h n ω (transportSub0 (D n) φ).1 - ((∫ y, K n ω y * φ y) - (∫ y, φ y) * K n ω 0)|
          ≤ |h n ω (transportSub0 (D n) φ).1| +
              |(∫ y, K n ω y * φ y) - (∫ y, φ y) * K n ω 0| := abs_sub _ _
        _ < η / 2 + t * L := by
            have : σ * L ≤ t * L := mul_le_mul_of_nonneg_right hσt hL0
            linarith
        _ ≤ η / 2 + η / 2 := by linarith
        _ = η := add_halves η
    exact absurd hmem (not_le.2 hlt)
  have hsum : Tendsto (fun n => P n {ω | η / 2 ≤ |h n ω (transportSub0 (D n) φ).1|} +
      P n {ω | ENNReal.ofReal t ≤ supDev (K n ω) (R / 2)}) atTop (𝓝 0) := by
    simpa only [add_zero] using hA.add hB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => ?_
  exact (measure_mono_ae (hincl n)).trans (measure_union_le _ _)

end SmallGammaGeodesics.CC

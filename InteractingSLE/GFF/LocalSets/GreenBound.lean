import LQGMetric.Field.GreenFn
import SupercriticalConformalCovariance.ZBConformal.Covariance
import SupercriticalConformalCovariance.ZBConformal.Pullback
import InteractingSLE.Foundations.Complex.RiemannMap
import InteractingSLE.Foundations.Loewner.Capacity
import QuantumZipper.Proofs.Complex.BasicsCayley
import QuantumZipper.GFF.Kernels


/-!
# Green-function comparison on conformal discs (specification Proposition 3.3, diagonal bound)

Source: `source/ig1-specification.pdf`, §3.1, proof of Proposition 3.3 (pp. 44–45; transcription
`source/spec/p001-048.md#prop-3.3-proof`). The proof bounds the variance of the harmonic projection
`h₁ = h − h_U` at a point by `Q(z, z) = G_D(z, z) − G_{D∖K}(z, z)`. The specification uses the
killed-Brownian-motion identity for `Q`; here no Brownian motion is needed (packet hint): by
monotonicity of the Dirichlet variance in the domain, `Q ≤ G_D − G_W` for any `W ⊆ D ∖ K`, and for
the conformal disc `W = φ⁻¹(B(0, r))` (`φ : D → 𝔻` conformal) both Green functions are explicit
after the Cayley map `C : ℍ → 𝔻`: with `p = C a`, `q = C b`,
`G_ℍ(C⁻¹p, C⁻¹q) = log |1 − p q̄| − log |p − q|` (`greenH_cayleyInv`), so
`G_D − G_W = log |1 − p q̄| − log |1 − p q̄ / r²| − log r ≤ log(1 + s²) − log(1 − s²/r²) − log r`
on `{|p|, |q| < s}` (`greenH_sub_greenH_cayleyDisk_le`).

## Main results

* `greenH_cayleyInv`: the Green function of `ℍ` in disc coordinates;
* `greenH_sub_greenH_cayleyDisk_le`: the kernel comparison above;
* `zeroGFFTestCov_sub_le_of_isConformalBijection_ball`: for `ρ ≥ 0` supported in `{‖φ‖ < s}`,
  `Var_D(ρ) − Var_W(ρ) ≤ (log(1 + s²) − log(1 − s²/r²) − log r) (∫ ρ)²`, `W = {‖φ‖ < r}`.

Reused: SupercriticalConformalCovariance `zeroGFFTestCov_conformal`, `integral_mul_confPushTest`
(conformal invariance and change of variables); LQGMetric `zeroGFFTestCov_eq_green`,
`integrable_greenDensProd`, `kerInt_ne_top`, `bddDens_test`, `ae_ne_diag` (Green representation of
the covariance on subdomains of `ℍ`); QuantumZipper `cayley`, `cayleyInv` and their lemmas.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric
open scoped ComplexConjugate

namespace InteractingSLE.GFF

open QuantumZipper QuantumZipper.CA

lemma cayleyInv_sub_cayleyInv {p q : ℂ} (hp : p ≠ 1) (hq : q ≠ 1) :
    cayleyInv p - cayleyInv q = 2 * I * (p - q) / ((1 - p) * (1 - q)) := by
  have h1 : (1 : ℂ) - p ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
  have h2 : (1 : ℂ) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  unfold cayleyInv
  field_simp
  ring

lemma cayleyInv_sub_conj_cayleyInv {p q : ℂ} (hp : p ≠ 1) (hq : q ≠ 1) :
    cayleyInv p - conj (cayleyInv q) = 2 * I * (1 - p * conj q) / ((1 - p) * (1 - conj q)) := by
  have h1 : (1 : ℂ) - p ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
  have h2 : (1 : ℂ) - conj q ≠ 0 := by
    intro h
    apply hq
    have : conj q = 1 := (sub_eq_zero.1 h).symm
    simpa using congrArg conj this
  unfold cayleyInv
  simp only [map_div₀, map_mul, map_add, map_sub, map_one, Complex.conj_I]
  field_simp
  ring

/-- The Green function of `ℍ` in disc coordinates:
`G_ℍ(C⁻¹p, C⁻¹q) = log |1 − p q̄| − log |p − q|`. -/
theorem greenH_cayleyInv {p q : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) (hpq : p ≠ q) :
    greenH (cayleyInv p) (cayleyInv q) = Real.log ‖1 - p * conj q‖ - Real.log ‖p - q‖ := by
  have hp1 : p ≠ 1 := fun h => by simp [h] at hp
  have hq1 : q ≠ 1 := fun h => by simp [h] at hq
  have hA : 0 < ‖1 - p‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hp1))
  have hB : 0 < ‖1 - q‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hq1))
  have hC : 0 < ‖1 - p * conj q‖ := by
    refine norm_pos_iff.2 (sub_ne_zero.2 fun h => ?_)
    have : ‖p * conj q‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg p, norm_nonneg q]
    rw [← h, norm_one] at this
    exact lt_irrefl _ this
  have hD : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq)
  have hcq : ‖1 - conj q‖ = ‖1 - q‖ := by
    rw [← Complex.norm_conj, map_sub, map_one, Complex.conj_conj]
  have n1 : ‖cayleyInv p - conj (cayleyInv q)‖ = 2 * ‖1 - p * conj q‖ / (‖1 - p‖ * ‖1 - q‖) := by
    rw [cayleyInv_sub_conj_cayleyInv hp1 hq1, norm_div, norm_mul, norm_mul, norm_mul, hcq]
    simp
  have n2 : ‖cayleyInv p - cayleyInv q‖ = 2 * ‖p - q‖ / (‖1 - p‖ * ‖1 - q‖) := by
    rw [cayleyInv_sub_cayleyInv hp1 hq1, norm_div, norm_mul, norm_mul, norm_mul]
    simp
  unfold greenH
  rw [n1, n2, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hC.ne',
    Real.log_mul (by norm_num) hD.ne']
  ring


/-- The conformal map `C⁻¹((C a)/r)` of the hyperbolic disc `{‖C a‖ < r}` onto `ℍ`. -/
def cayleyDisk (r : ℝ) (a : ℂ) : ℂ := cayleyInv (cayley a / r)

lemma cayley_ne_cayley {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) : cayley a ≠ cayley b :=
  fun h => hab (by
    rw [← cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt ha)),
      ← cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hb)), h])

/-- **Green kernel comparison.** For `a ≠ b` in the hyperbolic disc `{‖C a‖ < s}`, `s < r ≤ 1`,
`G_ℍ(a, b) − G_ℍ(M a, M b) ≤ log(1 + s²) − log(1 − s²/r²) − log r` with `M = cayleyDisk r`. -/
theorem greenH_sub_greenH_cayleyDisk_le {r s : ℝ} (hs : 0 ≤ s) (hsr : s < r) (hr : r ≤ 1)
    {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hca : ‖cayley a‖ < s) (hcb : ‖cayley b‖ < s)
    (hab : a ≠ b) :
    greenH a b - greenH (cayleyDisk r a) (cayleyDisk r b) ≤
      Real.log (1 + s ^ 2) - Real.log (1 - s ^ 2 / r ^ 2) - Real.log r := by
  set p := cayley a with hp
  set q := cayley b with hq
  have hr0 : 0 < r := lt_of_le_of_lt hs hsr
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hpq : p ≠ q := cayley_ne_cayley ha hb hab
  have hp1 : ‖p‖ < 1 := by linarith
  have hq1 : ‖q‖ < 1 := by linarith
  have hpr : ‖p / r‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, div_lt_one hr0]; linarith
  have hqr : ‖q / r‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, div_lt_one hr0]; linarith
  have hpqr : p / r ≠ q / r := fun h => hpq (by
    have := congrArg (· * (r : ℂ)) h
    simpa [div_mul_cancel₀ _ hr0'] using this)
  have e1 : greenH a b = Real.log ‖1 - p * conj q‖ - Real.log ‖p - q‖ := by
    rw [← greenH_cayleyInv hp1 hq1 hpq, hp, hq,
      cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt ha)),
      cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hb))]
  have e2 : greenH (cayleyDisk r a) (cayleyDisk r b) =
      Real.log ‖1 - p * conj q / (r ^ 2 : ℝ)‖ - (Real.log ‖p - q‖ - Real.log r) := by
    unfold cayleyDisk
    rw [greenH_cayleyInv hpr hqr hpqr]
    have h1 : p / r * conj (q / r) = p * conj q / (r ^ 2 : ℝ) := by
      rw [map_div₀, Complex.conj_ofReal]; push_cast; ring
    have h2 : p / r - q / r = (p - q) / r := by ring
    rw [h1, h2, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      Real.log_div (norm_pos_iff.2 (sub_ne_zero.2 hpq)).ne' hr0.ne']
  have hpq_le : ‖p * conj q‖ ≤ s ^ 2 := by
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul hca.le hcb.le (norm_nonneg _) hs
  have hs2 : s ^ 2 / r ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; exact pow_lt_pow_left₀ hsr hs two_ne_zero
  have hlow : 1 - s ^ 2 / r ^ 2 ≤ ‖1 - p * conj q / (r ^ 2 : ℝ)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (p * conj q / (r ^ 2 : ℝ))
    rw [norm_one, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
    have : ‖p * conj q‖ / r ^ 2 ≤ s ^ 2 / r ^ 2 :=
      div_le_div_of_nonneg_right hpq_le (by positivity)
    linarith
  have hup : ‖1 - p * conj q‖ ≤ 1 + s ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]; linarith
  have hpos : 0 < ‖1 - p * conj q‖ := by
    refine norm_pos_iff.2 (sub_ne_zero.2 fun h => ?_)
    have : ‖p * conj q‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg p, norm_nonneg q]
    rw [← h, norm_one] at this
    exact lt_irrefl _ this
  rw [e1, e2]
  have l1 : Real.log ‖1 - p * conj q‖ ≤ Real.log (1 + s ^ 2) := Real.log_le_log hpos hup
  have l2 : Real.log (1 - s ^ 2 / r ^ 2) ≤ Real.log ‖1 - p * conj q / (r ^ 2 : ℝ)‖ :=
    Real.log_le_log (by linarith) hlow
  linarith


open SupercriticalConformalCovariance (IsConformalBijection)
open TopologicalSpace MeasureTheory

/-- The hyperbolic disc `{a ∈ ℍ : ‖C a‖ < r}` (`C` the Cayley map onto `𝔻`). -/
def hypDisc (r : ℝ) : Set ℂ := {a | a ∈ H ∧ ‖cayley a‖ < r}

lemma isOpen_hypDisc (r : ℝ) : IsOpen (hypDisc r) := by
  have hc : ContinuousOn cayley H := continuousOn_cayley.mono fun z hz =>
    (ne_neg_I_iff.2 (add_I_ne_zero_of_im_nonneg (le_of_lt hz)))
  have := hc.isOpen_inter_preimage isOpen_H
    (isOpen_lt continuous_norm (continuous_const (y := r)) : IsOpen {w : ℂ | ‖w‖ < r})
  exact this

lemma isConformalBijection_cayleyDisk {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1) :
    IsConformalBijection (cayleyDisk r) (hypDisc r) H := by
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hmem : ∀ a ∈ hypDisc r, cayley a / r ∈ ball (0 : ℂ) 1 := fun a ha => by
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_lt_one hr0]
    exact ha.2
  refine ⟨fun a ha => ?_, fun a ha => cayleyInv_mem_H (hmem a ha), fun a ha b hb h => ?_,
    fun z hz => ?_⟩
  · have hI : a + I ≠ 0 := add_I_ne_zero_of_im_nonneg (le_of_lt ha.1)
    have hw : cayley a / r ≠ 1 := fun h => by
      have := hmem a ha; rw [h, mem_ball_zero_iff, norm_one] at this; exact lt_irrefl _ this
    exact ((differentiableAt_cayleyInv hw).comp a
      ((differentiableAt_cayley hI).div_const _)).differentiableWithinAt
  · have h1 := isConformalBijection_cayleyInv.2.injOn (hmem a ha) (hmem b hb) h
    have h2 : cayley a = cayley b := by
      have := congrArg (· * (r : ℂ)) h1
      simpa [div_mul_cancel₀ _ hr0'] using this
    rw [← cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt ha.1)),
      ← cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hb.1)), h2]
  · have hcz := cayley_mem_ball hz
    have hw : (r : ℂ) * cayley z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      rw [mem_ball_zero_iff] at hcz
      nlinarith [norm_nonneg (cayley z)]
    have hw1 : (r : ℂ) * cayley z ≠ 1 := fun h => by
      rw [h, mem_ball_zero_iff, norm_one] at hw; exact lt_irrefl _ hw
    refine ⟨cayleyInv (r * cayley z), ⟨cayleyInv_mem_H hw, ?_⟩, ?_⟩
    · rw [cayley_cayleyInv hw1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      rw [mem_ball_zero_iff] at hcz
      nlinarith [norm_nonneg (cayley z)]
    · simp only [cayleyDisk]
      rw [cayley_cayleyInv hw1, mul_div_cancel_left₀ _ hr0',
        cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hz))]


open LQGMetric (TestOn)
open SupercriticalConformalCovariance (confPushTest)

/-- `ℍ` as an open set. -/
abbrev hOpens : Opens ℂ := ⟨H, isOpen_H⟩

/-- The hyperbolic disc as an open set. -/
abbrev hypDiscOpens (r : ℝ) : Opens ℂ := ⟨hypDisc r, isOpen_hypDisc r⟩

lemma isConformalOnto_id_H : QuantumZipper.K3.IsConformalOnto id H H :=
  ⟨isOpen_H, differentiableOn_id, injOn_id _, image_id _, fun z _ => by simp⟩

/-- Restricting a conformal bijection does not change the transported test function. -/
lemma coe_confPushTest_restrict {Φ : ℂ → ℂ} {U V U' V' : Opens ℂ}
    (hΦ : IsConformalBijection Φ U V) (hΦ' : IsConformalBijection Φ U' V') (hU' : U' ≤ U)
    (ψ : TestOn U) (ψ' : TestOn U') (hψ : ⇑ψ' = ⇑ψ) :
    ⇑(confPushTest hΦ' ψ') = ⇑(confPushTest hΦ ψ) := by
  funext y
  change (V' : Set ℂ).indicator (fun y => ‖deriv (Function.invFunOn Φ U') y‖ ^ 2 *
      ψ' (Function.invFunOn Φ U' y)) y = (V : Set ℂ).indicator
      (fun y => ‖deriv (Function.invFunOn Φ U) y‖ ^ 2 * ψ (Function.invFunOn Φ U y)) y
  have hU'U : (U' : Set ℂ) ⊆ U := hU'
  have hV'V : (V' : Set ℂ) ⊆ V := by
    rw [← hΦ'.2.image_eq, ← hΦ.2.image_eq]; exact image_mono hU'U
  have key : ∀ z ∈ (V' : Set ℂ), Function.invFunOn Φ U' z = Function.invFunOn Φ U z := by
    intro z hz
    have e' : ∃ a ∈ (U' : Set ℂ), Φ a = z := by
      rw [← mem_image, hΦ'.2.image_eq]; exact hz
    have e : ∃ a ∈ (U : Set ℂ), Φ a = z := by
      rw [← mem_image, hΦ.2.image_eq]; exact hV'V hz
    exact hΦ.2.injOn (hU'U (Function.invFunOn_mem e')) (Function.invFunOn_mem e)
      ((Function.invFunOn_eq e').trans (Function.invFunOn_eq e).symm)
  by_cases hy : y ∈ (V' : Set ℂ)
  · rw [indicator_of_mem hy, indicator_of_mem (hV'V hy), key y hy, hψ]
    congr 3
    exact Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (V'.isOpen.mem_nhds hy) key)
  · rw [indicator_of_notMem hy]
    by_cases hyV : y ∈ (V : Set ℂ)
    · rw [indicator_of_mem hyV]
      have e : ∃ a ∈ (U : Set ℂ), Φ a = y := by
        rw [← mem_image, hΦ.2.image_eq]; exact hyV
      have hnot : Function.invFunOn Φ U y ∉ (U' : Set ℂ) := fun h => hy (by
        rw [← Function.invFunOn_eq e]; exact hΦ'.2.mapsTo h)
      have : ψ (Function.invFunOn Φ U y) = 0 := by
        rw [← hψ]; exact ψ'.zero_on_compl hnot
      rw [this, mul_zero]
    · rw [indicator_of_notMem hyV]

/-- Integrability of the Green integrand of a non-negative test function. -/
lemma integrable_green_mul {V : Opens ℂ} (hVH : (V : Set ℂ) ⊆ H) {m : ℂ → ℂ}
    (hm : QuantumZipper.K3.IsConformalOnto m V H) (f : TestOn V) (hf : ∀ x, 0 ≤ f x) :
    Integrable (fun p : ℂ × ℂ => f p.1 * f p.2 * greenH (m p.1) (m p.2))
      ((volume : Measure ℂ).prod volume) := by
  obtain ⟨M, R, b⟩ := LQGMetric.bddDens_test f.continuous f.hasCompactSupport
  have hf0 : ∀ x ∉ (V : Set ℂ), f x = 0 := fun x hx => f.zero_on_compl hx
  have hi := LQGMetric.integrable_greenDensProd hm f.continuous f.continuous hf0 hf0
    (LQGMetric.kerInt_ne_top hm hVH b b)
  refine hi.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [LQGMetric.greenDensProd]
  by_cases h1 : p.1 ∈ (V : Set ℂ)
  · by_cases h2 : p.2 ∈ (V : Set ℂ)
    · rw [QuantumZipper.K3.confMod_eqOn h1, QuantumZipper.K3.confMod_eqOn h2,
        max_eq_left (hf _), max_eq_left (hf _)]
    · simp [hf0 _ h2]
  · simp [hf0 _ h1]


lemma cayley_cayleyInv_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : cayley (cayleyInv w) = w :=
  cayley_cayleyInv fun h => by rw [h, mem_ball_zero_iff, norm_one] at hw; exact lt_irrefl _ hw

/-- `cayleyInv ∘ φ` restricted to `{‖φ‖ < r}` is a conformal bijection onto the hyperbolic disc. -/
lemma isConformalBijection_restrict_hypDisc {D : Set ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ D (ball 0 1)) (r : ℝ) :
    IsConformalBijection (cayleyInv ∘ φ) {x | x ∈ D ∧ ‖φ x‖ < r} (hypDisc r) := by
  have hΦ := isConformalBijection_comp isConformalBijection_cayleyInv hφ
  refine ⟨hΦ.1.mono fun x hx => hx.1, fun x hx => ?_, hΦ.2.injOn.mono fun x hx => hx.1,
    fun a ha => ?_⟩
  · have hb := hφ.2.mapsTo hx.1
    refine ⟨cayleyInv_mem_H hb, ?_⟩
    simp only [Function.comp_apply, cayley_cayleyInv_of_mem_ball hb]
    exact hx.2
  · obtain ⟨x, hx, hxa⟩ := hφ.2.surjOn (cayley_mem_ball ha.1)
    refine ⟨x, ⟨hx, by rw [hxa]; exact ha.2⟩, ?_⟩
    simp only [Function.comp_apply, hxa]
    exact cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt ha.1))

/-- **Variance comparison on a conformal disc.** Let `φ : D → 𝔻` be a conformal bijection,
`W = {x ∈ D : ‖φ x‖ < r}`, and `ρ ≥ 0` a test function on `D` supported in `{‖φ‖ < s}`, `s < r ≤ 1`.
Then `Var_D(ρ) − Var_W(ρ) ≤ (log(1 + s²) − log(1 − s²/r²) − log r) (∫ ρ)²`. -/
theorem zeroGFFTestCov_sub_le_of_isConformalBijection_ball {D W : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ D (ball 0 1)) {r s : ℝ} (hs : 0 ≤ s) (hsr : s < r)
    (hr : r ≤ 1) (hW : (W : Set ℂ) = {x | x ∈ D ∧ ‖φ x‖ < r}) (ρ : TestOn D) (ρW : TestOn W)
    (hρW : ⇑ρW = ⇑ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρs : ∀ x, ρ x ≠ 0 → ‖φ x‖ < s) :
    zeroGFFTestCov D ρ ρ - zeroGFFTestCov W ρW ρW ≤
      (Real.log (1 + s ^ 2) - Real.log (1 - s ^ 2 / r ^ 2) - Real.log r) * (∫ x, ρ x) ^ 2 := by
  have hr0 : 0 < r := lt_of_le_of_lt hs hsr
  set Φ : ℂ → ℂ := cayleyInv ∘ φ with hΦdef
  have hΦ : IsConformalBijection Φ D (hOpens : Set ℂ) :=
    isConformalBijection_comp isConformalBijection_cayleyInv hφ
  have hWD : W ≤ D := fun x hx => by
    have hx' : x ∈ (W : Set ℂ) := hx
    rw [hW] at hx'; exact hx'.1
  have hΦW : IsConformalBijection Φ W (hypDiscOpens r : Set ℂ) := by
    rw [hW]; exact isConformalBijection_restrict_hypDisc hφ r
  have hM : QuantumZipper.K3.IsConformalOnto (cayleyDisk r) (hypDiscOpens r : Set ℂ) H :=
    (isConformalBijection_iff_isConformalOnto (isOpen_hypDisc r)).1
      (isConformalBijection_cayleyDisk hr0 hr)
  set ρt := confPushTest hΦ ρ with hρt
  set ρtW := confPushTest hΦW ρW with hρtW
  have hfun : ⇑ρtW = ⇑ρt := coe_confPushTest_restrict hΦ hΦW hWD ρ ρW hρW
  -- the transported function
  have hval : ∀ y, ρt y = (H : Set ℂ).indicator (fun y => ‖deriv (Function.invFunOn Φ D) y‖ ^ 2 *
      ρ (Function.invFunOn Φ D y)) y := fun y => rfl
  have hnn : ∀ y, 0 ≤ ρt y := fun y => by
    rw [hval]; exact indicator_nonneg (fun y _ => mul_nonneg (by positivity) (hρ0 _)) y
  have hsupp : ∀ y, ρt y ≠ 0 → y ∈ H ∧ ‖cayley y‖ < s := by
    intro y hy
    rw [hval] at hy
    have hyH : y ∈ H := by by_contra h; exact hy (indicator_of_notMem h _)
    rw [indicator_of_mem hyH] at hy
    have hρ : ρ (Function.invFunOn Φ D y) ≠ 0 := fun h => hy (by rw [h, mul_zero])
    have e : ∃ a ∈ (D : Set ℂ), Φ a = y := by
      rw [← mem_image, hΦ.2.image_eq]; exact hyH
    have hx := Function.invFunOn_mem e
    have hy' := Function.invFunOn_eq e
    refine ⟨hyH, ?_⟩
    rw [← hy']
    show ‖cayley (cayleyInv (φ (Function.invFunOn Φ D y)))‖ < s
    rw [cayley_cayleyInv_of_mem_ball (hφ.2.mapsTo hx)]
    exact hρs _ hρ
  have e1 := SupercriticalConformalCovariance.ZBConformal.zeroGFFTestCov_conformal hΦ ρ ρ
  have e2 := SupercriticalConformalCovariance.ZBConformal.zeroGFFTestCov_conformal hΦW ρW ρW
  have g1 := LQGMetric.zeroGFFTestCov_eq_green (V := hOpens) subset_rfl isConformalOnto_id_H ρt ρt
  have g2 := LQGMetric.zeroGFFTestCov_eq_green (V := hypDiscOpens r) (fun a ha => ha.1) hM ρtW ρtW
  rw [← hρt] at e1
  rw [← hρtW] at e2
  have i1 := integrable_green_mul (V := hOpens) subset_rfl isConformalOnto_id_H ρt hnn
  have i2 := integrable_green_mul (V := hypDiscOpens r) (fun a ha => ha.1) hM ρtW
    (fun y => by rw [hfun]; exact hnn y)
  simp only [id] at g1 i1
  simp only [hfun] at g2 i2
  set Δ := Real.log (1 + s ^ 2) - Real.log (1 - s ^ 2 / r ^ 2) - Real.log r
  have hint : ∫ x, ρt x = ∫ x, ρ x := by
    have := SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest hΦ ρ
      (fun _ => (1 : ℝ))
    simpa only [one_mul] using this
  have hρti : Integrable (fun x => ρt x) :=
    ρt.continuous.integrable_of_hasCompactSupport ρt.hasCompactSupport
  rw [← e1, ← e2, hfun, g1, g2, ← integral_sub i1 i2]
  calc ∫ p, (ρt p.1 * ρt p.2 * greenH p.1 p.2 -
          ρt p.1 * ρt p.2 * greenH (cayleyDisk r p.1) (cayleyDisk r p.2))
        ∂((volume : Measure ℂ).prod volume)
      ≤ ∫ p, Δ * (ρt p.1 * ρt p.2) ∂((volume : Measure ℂ).prod volume) := by
        refine integral_mono_ae (i1.sub i2) ((hρti.mul_prod hρti).const_mul Δ) ?_
        filter_upwards [LQGMetric.ae_ne_diag] with p hp
        by_cases h1 : ρt p.1 = 0
        · simp [h1]
        by_cases h2 : ρt p.2 = 0
        · simp [h2]
        obtain ⟨ha, hca⟩ := hsupp _ h1
        obtain ⟨hb, hcb⟩ := hsupp _ h2
        have hk := greenH_sub_greenH_cayleyDisk_le hs hsr hr ha hb hca hcb hp
        have hpos : 0 ≤ ρt p.1 * ρt p.2 := mul_nonneg (hnn _) (hnn _)
        calc ρt p.1 * ρt p.2 * greenH p.1 p.2 -
              ρt p.1 * ρt p.2 * greenH (cayleyDisk r p.1) (cayleyDisk r p.2)
            = (ρt p.1 * ρt p.2) *
                (greenH p.1 p.2 - greenH (cayleyDisk r p.1) (cayleyDisk r p.2)) := by ring
          _ ≤ (ρt p.1 * ρt p.2) * Δ := mul_le_mul_of_nonneg_left hk hpos
          _ = Δ * (ρt p.1 * ρt p.2) := by ring
    _ = Δ * (∫ x, ρ x) ^ 2 := by
        rw [integral_const_mul, integral_prod_mul (fun x => ρt x) (fun x => ρt x), hint, sq]

end InteractingSLE.GFF

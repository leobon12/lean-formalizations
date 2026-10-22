import HigherDimLQGContinuity.Concentration.Majorant
import GaussianLQG.Probability.GaussianLp

/-!
# Shift-Lipschitz bound and coordinate derivatives on a pairing frame (packet N4)

Blueprint Part C Lemmas `c:lem-shiftlip` (hypothesis (H) of the Gaussian `L^p` inequality) and `c:lem-deriv`
(coordinate derivatives along geodesics); NA4 A1 Steps 3–4. These are the `ℝ^d` ports of GaussianLQG's
`Setup.abs_logD_shiftBy_sub_le` and `Setup.hasDerivAt_logD_of_isGeod01` (`LQG/Derivative.lean`).

Fix a pairing frame `F` (`e_j`, `T`, `good`, `C_b`), a strong `D` at `ξ ≥ 0` and the log unit distance on the
frame `G(ω) = log ρ_{T ω}(0, e₁)` (`logRhoFrame`, `ρ = rho D`).

* (H) (`logRhoFrame_shiftLipschitz`): at a base point `ω ∈ good` where Weyl scaling holds at `T ω`,
  `|G(ω + v) - G(ω + v')| ≤ ∑_j ξ ‖e_j‖_∞ |v_j - v'_j|`: by the frame shift `T(ω + v) = T ω + f_v` and Weyl scaling,
  `G(ω + v) = log (e^{ξ f_v}·D_{T ω})(0, e₁) - logMean D`, and HDLM's ratio bound `weylScale_le_exp_mul`.
  `exists_good_shiftLipschitz` produces the measurable full-measure set for `gaussian_Lp_inequality`.
* Derivative (`hasDerivAt_logRhoFrame_of_isConstSpeedGeod`, `abs_coordDeriv_logRho_le`): for every constant-speed
  `ρ_{T ω}`-geodesic `η` from `0` to `e₁`, `|∂_j G(ω)| ≤ ξ |∫ e_j dν_η|`. The competitor bound
  `G(ω + t δ_j) ≤ G(ω) + ξ t ∫ e_j dν_η + (ξ t ‖e_j‖_∞)²` (`logRhoFrame_shiftBy_single_le`) makes `0` a local
  maximum of `t ↦ G(ω + tδ_j) - a t - c t²`; where `G` is differentiable along `δ_j` its derivative is
  `a = ξ ∫ e_j dν_η` (the derivative identity), and elsewhere Mathlib's `deriv` is `0` (no almost-everywhere
  differentiability is needed).
* Square function (`tsum_coordDeriv_sq_le`): with the frame's Bessel clause, `∑_j (∂_j G(ω))² ≤ ξ² C_b U` whenever
  the geodesic satisfies the confinement and ball bounds of the majorant `U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)
open GaussianLQG (Coord stdP shiftBy coordDeriv)

variable {d : ℕ}

/-! ## Frame functions -/

/-- `f_v(x) = ∑_j v_j e_j(x)`. -/
theorem n4_frameFunRd_apply (e : ℕ → C(Rd d, ℝ)) (v : ℕ →₀ ℝ) (x : Rd d) :
    frameFunRd e v x = v.sum fun j c => c * e j x := by
  unfold frameFunRd Finsupp.sum
  rw [ContinuousMap.sum_apply]
  rfl

/-- `f_v(x) = ∑_{j ∈ s} v_j e_j(x)` for every finite `s` containing the support of `v`. -/
theorem n4_frameFunRd_eq_sum (e : ℕ → C(Rd d, ℝ)) {v : ℕ →₀ ℝ} {s : Finset ℕ} (hs : v.support ⊆ s)
    (x : Rd d) : frameFunRd e v x = ∑ j ∈ s, v j * e j x := by
  rw [n4_frameFunRd_apply]
  exact Finsupp.sum_of_support_subset v hs (fun j c => c * e j x) (fun j _ => zero_mul _)

/-- `f_{t δ_j} = t e_j`. -/
theorem n4_frameFunRd_single (e : ℕ → C(Rd d, ℝ)) (j : ℕ) (t : ℝ) (x : Rd d) :
    frameFunRd e (Finsupp.single j t) x = t * e j x := by
  rw [n4_frameFunRd_apply]
  exact Finsupp.sum_single_index (zero_mul _)

/-- A sup-norm bound `‖e_j‖_∞ ≤ frameBound F j` of the frame functions (from the field `bdd`). -/
def frameBound (F : PairingFrame d) (j : ℕ) : ℝ := max 0 (Classical.choose (F.bdd j))

theorem frameBound_nonneg (F : PairingFrame d) (j : ℕ) : 0 ≤ frameBound F j := le_max_left _ _

theorem abs_le_frameBound (F : PairingFrame d) (j : ℕ) (x : Rd d) : |F.e j x| ≤ frameBound F j :=
  (Classical.choose_spec (F.bdd j) x).trans (le_max_right _ _)

/-- `|f_v(x) - f_{v'}(x)| ≤ ∑_j ‖e_j‖_∞ |v_j - v'_j|`. -/
theorem abs_frameFunRd_sub_le (F : PairingFrame d) (v v' : ℕ →₀ ℝ) (x : Rd d) :
    |frameFunRd F.e v x - frameFunRd F.e v' x| ≤
      ∑ j ∈ v.support ∪ v'.support, frameBound F j * |v j - v' j| := by
  rw [n4_frameFunRd_eq_sum F.e Finset.subset_union_left x,
    n4_frameFunRd_eq_sum F.e Finset.subset_union_right x, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← sub_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_le_frameBound F j x) (abs_nonneg _)

/-! ## Geodesics of `rho` -/

/-- Constant-speed geodesics of `ρ = rho D` and of `D` coincide (`ρ` is a positive multiple of `D`). -/
theorem isConstSpeedGeod_rho_iff (D : DistRd d → ContMetric d) (g : DistRd d) (x y : Rd d)
    (η : C(unitInterval, Rd d)) : IsConstSpeedGeod (rho D g) x y η ↔ IsConstSpeedGeod (D g) x y η := by
  rw [isConstSpeedGeod_iff, isConstSpeedGeod_iff]
  exact isConstSpeedGeodFn_smul_iff (D g).1 x y η _ (Real.exp_pos _)

/-! ## The log unit distance on the frame -/

/-- The log unit distance on the frame: `G(ω) = log ρ_{T ω}(0, e₁)`, `ρ = rho D`. -/
def logRhoFrame (F : PairingFrame d) (D : DistRd d → ContMetric d) (ω : Coord) : ℝ :=
  Real.log ((rho D (F.T ω)).1 (0, e₁ d))

theorem measurable_logRhoFrame (F : PairingFrame d) {D : DistRd d → ContMetric d}
    (hD : Measurable D) : Measurable (logRhoFrame F D) :=
  (measurable_log_rho_apply hD (0, e₁ d)).comp F.measurable_T

/-- Weyl scaling at the base field `T ω`, for every continuous `f` (axiom (III) at `T ω`). -/
def WeylAt (ξ : ℝ) (D : DistRd d → ContMetric d) (g : DistRd d) : Prop :=
  ∀ (f : C(Rd d, ℝ)) (z w : Rd d), weylScale ξ f (D g) z w = ENNReal.ofReal ((D (addFun g f)).1 (z, w))

/-- On `good`, `G(ω + v) = log D_{T ω + f_v}(0, e₁) - logMean D`. -/
theorem logRhoFrame_shiftBy (hd : 1 ≤ d) (F : PairingFrame d) (D : DistRd d → ContMetric d)
    {ω : Coord} (hω : ω ∈ F.good) (v : ℕ →₀ ℝ) :
    logRhoFrame F D (shiftBy ω v) =
      Real.log ((D (addFun (F.T ω) (frameFunRd F.e v))).1 (0, e₁ d)) - logMean D := by
  unfold logRhoFrame
  rw [F.shift ω hω v, log_rho_apply D _ (p2_zero_ne_e₁ hd)]

/-- **Hypothesis (H)** at one base point (blueprint `c:lem-shiftlip`; port of GaussianLQG's
`Setup.abs_logD_shiftBy_sub_le`): for `ω ∈ good` with Weyl scaling at `T ω` and `ξ ≥ 0`,
`|G(ω + v) - G(ω + v')| ≤ ∑_j ξ ‖e_j‖_∞ |v_j - v'_j|`. -/
theorem logRhoFrame_shiftLipschitz (hd : 1 ≤ d) (F : PairingFrame d) {ξ : ℝ} (hξ : 0 ≤ ξ)
    {D : DistRd d → ContMetric d} {ω : Coord} (hω : ω ∈ F.good) (hW : WeylAt ξ D (F.T ω))
    (v v' : ℕ →₀ ℝ) :
    |logRhoFrame F D (shiftBy ω v) - logRhoFrame F D (shiftBy ω v')| ≤
      ∑ j ∈ v.support ∪ v'.support, ξ * frameBound F j * |v j - v' j| := by
  set c := ∑ j ∈ v.support ∪ v'.support, frameBound F j * |v j - v' j| with hc
  have hsum : ∑ j ∈ v.support ∪ v'.support, ξ * frameBound F j * |v j - v' j| = ξ * c := by
    rw [hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, logRhoFrame_shiftBy hd F D hω v, logRhoFrame_shiftBy hd F D hω v', sub_sub_sub_cancel_right]
  set a := (D (addFun (F.T ω) (frameFunRd F.e v))).1 (0, e₁ d) with ha
  set b := (D (addFun (F.T ω) (frameFunRd F.e v'))).1 (0, e₁ d) with hb
  have ha0 : 0 < a := ContMetric.apply_pos _ (p2_zero_ne_e₁ hd)
  have hb0 : 0 < b := ContMetric.apply_pos _ (p2_zero_ne_e₁ hd)
  have hdiff := abs_frameFunRd_sub_le F v v'
  have h1 : Real.log a ≤ ξ * c + Real.log b :=
    log_le_add_log_of_weylScale (fun x => by
      have := (le_abs_self _).trans (hdiff x)
      nlinarith) ha0 hb0 (hW _ 0 (e₁ d)) (hW _ 0 (e₁ d))
  have hdiff' : ∀ x, |frameFunRd F.e v' x - frameFunRd F.e v x| ≤ c := fun x => by
    rw [abs_sub_comm]
    exact hdiff x
  have h2 : Real.log b ≤ ξ * c + Real.log a :=
    log_le_add_log_of_weylScale (fun x => by
      have := (le_abs_self _).trans (hdiff' x)
      nlinarith) hb0 ha0 (hW _ 0 (e₁ d)) (hW _ 0 (e₁ d))
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## The derivative along geodesics -/

/-- **The competitor bound** (proof of blueprint `c:lem-deriv`; port of GaussianLQG's
`Setup.logD_shiftBy_single_le`): at `ω ∈ good` with Weyl scaling at `T ω`, for a constant-speed
`ρ_{T ω}`-geodesic `η` from `0` to `e₁` and `|ξ t| ‖e_j‖_∞ ≤ 1`,
`G(ω + t δ_j) ≤ G(ω) + ξ t ∫ e_j dν_η + (ξ t ‖e_j‖_∞)²`. -/
theorem logRhoFrame_shiftBy_single_le (hd : 1 ≤ d) (F : PairingFrame d) {ξ : ℝ}
    {D : DistRd d → ContMetric d} {ω : Coord} (hω : ω ∈ F.good) (hW : WeylAt ξ D (F.T ω)) (j : ℕ)
    {η : C(unitInterval, Rd d)} (hη : IsConstSpeedGeod (rho D (F.T ω)) 0 (e₁ d) η) {t : ℝ}
    (ht : |ξ * t| * frameBound F j ≤ 1) :
    logRhoFrame F D (shiftBy ω (Finsupp.single j t)) ≤
      logRhoFrame F D ω + ξ * t * ∫ x, F.e j x ∂(pathMeasure η) + (ξ * t * frameBound F j) ^ 2 := by
  have hηD : IsConstSpeedGeod (D (F.T ω)) 0 (e₁ d) η := (isConstSpeedGeod_rho_iff D _ _ _ η).1 hη
  set M := frameBound F j with hMdef
  set φ : ℝ → ℝ := fun s => F.e j (η (projIcc 0 1 zero_le_one s)) with hφdef
  have hφc : Continuous φ := (F.e j).continuous.comp (continuous_pathParam η)
  have hφM : ∀ s, |φ s| ≤ M := fun s => abs_le_frameBound F j _
  set J := ∫ s in (0 : ℝ)..1, Real.exp (ξ * (t * φ s)) with hJdef
  have hexpc : Continuous fun s => Real.exp (ξ * (t * φ s)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul hφc))
  have hLpos : 0 < (D (F.T ω)).1 (0, e₁ d) := ContMetric.apply_pos _ (p2_zero_ne_e₁ hd)
  have hDpos : 0 < (D (addFun (F.T ω) (frameFunRd F.e (Finsupp.single j t)))).1 (0, e₁ d) :=
    ContMetric.apply_pos _ (p2_zero_ne_e₁ hd)
  have hJpos : 0 < J := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hexpc.intervalIntegrable 0 1) (fun s _ => Real.exp_pos _) zero_lt_one
  -- the Weyl comparison along `η`
  have h1 : (D (addFun (F.T ω) (frameFunRd F.e (Finsupp.single j t)))).1 (0, e₁ d) ≤
      (D (F.T ω)).1 (0, e₁ d) * J := by
    have hWg := weylScale_le_of_isConstSpeedGeod hηD ξ (frameFunRd F.e (Finsupp.single j t))
    rw [hW] at hWg
    have hint : (∫ s in (0 : ℝ)..1, Real.exp (ξ * frameFunRd F.e (Finsupp.single j t)
        (η (projIcc 0 1 zero_le_one s)))) = J := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hφdef, n4_frameFunRd_single]
    rw [hint] at hWg
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hLpos.le hJpos.le)).1 hWg
  -- the second-order bound `e^y ≤ 1 + y + y²` for `|y| ≤ 1`
  have hJle : J ≤ 1 + ξ * t * (∫ s in (0 : ℝ)..1, φ s) + (ξ * t * M) ^ 2 := by
    have hpt : ∀ s ∈ Icc (0 : ℝ) 1, Real.exp (ξ * (t * φ s)) ≤
        (1 + (ξ * t * M) ^ 2) + ξ * t * φ s := by
      intro s _
      have hy : |ξ * (t * φ s)| ≤ 1 := by
        rw [← mul_assoc, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hφM s) (abs_nonneg _)).trans ht
      have h2 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hy)).2
      have hsq : (ξ * (t * φ s)) ^ 2 ≤ (ξ * t * M) ^ 2 := by
        rw [← mul_assoc, mul_pow, mul_pow (ξ * t)]
        exact mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hφM s)).1 (abs_le.1 (hφM s)).2)
          (sq_nonneg _)
      have he : ξ * (t * φ s) = ξ * t * φ s := by ring
      rw [he] at h2 hsq ⊢
      linarith
    calc J ≤ ∫ s in (0 : ℝ)..1, ((1 + (ξ * t * M) ^ 2) + ξ * t * φ s) :=
          intervalIntegral.integral_mono_on zero_le_one (hexpc.intervalIntegrable 0 1)
            ((continuous_const.add (continuous_const.mul hφc)).intervalIntegrable 0 1) hpt
      _ = 1 + ξ * t * (∫ s in (0 : ℝ)..1, φ s) + (ξ * t * M) ^ 2 := by
          rw [intervalIntegral.integral_add intervalIntegrable_const
            ((hφc.intervalIntegrable 0 1).const_mul _), intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul]
          simp only [sub_zero, one_smul]
          ring
  -- conclude with `log x ≤ x - 1`
  have hI : ∫ x, F.e j x ∂(pathMeasure η) = ∫ s in (0 : ℝ)..1, φ s :=
    integral_pathMeasure η (F.e j).continuous
  have hG0 : logRhoFrame F D ω = Real.log ((D (F.T ω)).1 (0, e₁ d)) - logMean D := by
    unfold logRhoFrame
    rw [log_rho_apply D _ (p2_zero_ne_e₁ hd)]
  rw [hI, logRhoFrame_shiftBy hd F D hω, hG0]
  have hlog : Real.log ((D (addFun (F.T ω) (frameFunRd F.e (Finsupp.single j t)))).1 (0, e₁ d)) ≤
      Real.log ((D (F.T ω)).1 (0, e₁ d)) + (J - 1) := by
    calc Real.log ((D (addFun (F.T ω) (frameFunRd F.e (Finsupp.single j t)))).1 (0, e₁ d))
        ≤ Real.log ((D (F.T ω)).1 (0, e₁ d) * J) := Real.log_le_log hDpos h1
      _ = Real.log ((D (F.T ω)).1 (0, e₁ d)) + Real.log J := Real.log_mul hLpos.ne' hJpos.ne'
      _ ≤ Real.log ((D (F.T ω)).1 (0, e₁ d)) + (J - 1) := by
          linarith [Real.log_le_sub_one_of_pos hJpos]
  linarith

/-- **The derivative identity** (blueprint `c:lem-deriv`; port of GaussianLQG's
`Setup.hasDerivAt_logD_of_isGeod01`): at `ω ∈ good` with Weyl scaling at `T ω`, if `t ↦ G(ω + t δ_j)` is
differentiable at `0`, then for every constant-speed `ρ_{T ω}`-geodesic `η` from `0` to `e₁` its derivative there is
`ξ ∫ e_j dν_η` (`0` is a local maximum of `G(ω + tδ_j) - ξ t ∫ e_j dν_η - (ξ ‖e_j‖_∞ t)²`). -/
theorem hasDerivAt_logRhoFrame_of_isConstSpeedGeod (hd : 1 ≤ d) (F : PairingFrame d) {ξ : ℝ}
    {D : DistRd d → ContMetric d} {ω : Coord} (hω : ω ∈ F.good) (hW : WeylAt ξ D (F.T ω)) (j : ℕ)
    {η : C(unitInterval, Rd d)} (hη : IsConstSpeedGeod (rho D (F.T ω)) 0 (e₁ d) η)
    (hdiff : DifferentiableAt ℝ (fun t => logRhoFrame F D (shiftBy ω (Finsupp.single j t))) 0) :
    HasDerivAt (fun t => logRhoFrame F D (shiftBy ω (Finsupp.single j t)))
      (ξ * ∫ x, F.e j x ∂(pathMeasure η)) 0 := by
  set g : ℝ → ℝ := fun t => logRhoFrame F D (shiftBy ω (Finsupp.single j t)) with hg
  set a := ξ * ∫ x, F.e j x ∂(pathMeasure η) with ha
  set c := (ξ * frameBound F j) ^ 2 with hc
  have hg0 : g 0 = logRhoFrame F D ω := by
    simp only [hg, GaussianLQG.GaussLp.shiftBy_single_zero]
  have hM := frameBound_nonneg F j
  have hden : 0 < |ξ| * frameBound F j + 1 := by positivity
  have hmax : IsLocalMax (fun t => g t - a * t - c * t ^ 2) 0 := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) (one_div_pos.2 hden))
      fun t ht => ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have ht' : |ξ * t| * frameBound F j ≤ 1 := by
      rw [abs_mul]
      calc |ξ| * |t| * frameBound F j = (|ξ| * frameBound F j) * |t| := by ring
        _ ≤ (|ξ| * frameBound F j + 1) * |t| :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (abs_nonneg t)
        _ ≤ (|ξ| * frameBound F j + 1) * (1 / (|ξ| * frameBound F j + 1)) :=
            mul_le_mul_of_nonneg_left ht.le hden.le
        _ = 1 := by field_simp
    have hle := logRhoFrame_shiftBy_single_le hd F hω hW j hη ht'
    have hct : (ξ * t * frameBound F j) ^ 2 = c * t ^ 2 := by rw [hc]; ring
    have hat : ξ * t * ∫ x, F.e j x ∂(pathMeasure η) = a * t := by rw [ha]; ring
    rw [hct, hat, ← hg0] at hle
    show g t - a * t - c * t ^ 2 ≤ g 0 - a * 0 - c * 0 ^ 2
    linarith
  have hderiv : HasDerivAt (fun t => g t - a * t - c * t ^ 2) (deriv g 0 - a - 0) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => a * t) a 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
    have h3 : HasDerivAt (fun t : ℝ => c * t ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_mul c
    exact (hdiff.hasDerivAt.sub h2).sub h3
  have h0 := hmax.hasDerivAt_eq_zero hderiv
  have hd' : deriv g 0 = a := by linarith
  rw [← hd']
  exact hdiff.hasDerivAt

/-- **Coordinate derivatives along geodesics** (blueprint `c:lem-deriv`): at `ω ∈ good` with Weyl scaling at
`T ω` and `ξ ≥ 0`, for every constant-speed `ρ_{T ω}`-geodesic `η` from `0` to `e₁`,
`|∂_j G(ω)| ≤ ξ |∫ e_j dν_η|`. Where `t ↦ G(ω + t δ_j)` is differentiable at `0` this is the derivative identity;
elsewhere `coordDeriv` is `0` (no almost-everywhere differentiability is needed). -/
theorem abs_coordDeriv_logRho_le (hd : 1 ≤ d) (F : PairingFrame d) {ξ : ℝ} (hξ : 0 ≤ ξ)
    {D : DistRd d → ContMetric d} {ω : Coord} (hω : ω ∈ F.good) (hW : WeylAt ξ D (F.T ω)) (j : ℕ)
    {η : C(unitInterval, Rd d)} (hη : IsConstSpeedGeod (rho D (F.T ω)) 0 (e₁ d) η) :
    |coordDeriv (logRhoFrame F D) j ω| ≤ ξ * |∫ x, F.e j x ∂(pathMeasure η)| := by
  have hcd : coordDeriv (logRhoFrame F D) j ω =
      deriv (fun t => logRhoFrame F D (shiftBy ω (Finsupp.single j t))) 0 := rfl
  rw [hcd]
  by_cases hdiff : DifferentiableAt ℝ (fun t => logRhoFrame F D (shiftBy ω (Finsupp.single j t))) 0
  · rw [(hasDerivAt_logRhoFrame_of_isConstSpeedGeod hd F hω hW j hη hdiff).deriv, abs_mul,
      abs_of_nonneg hξ]
  · rw [deriv_zero_of_not_differentiableAt hdiff, abs_zero]
    positivity

/-- **The square function along a confined geodesic** (blueprint `c:lem-deriv`, consequence via the frame's
Bessel clause): if `η` is a constant-speed `ρ_{T ω}`-geodesic from `0` to `e₁` with `η ⊆ B̄_S` and
`ν_η(B̄_r(z)) ≤ B r^σ` (`S, B ≥ 1`, `0 < σ < 1`), then
`∑'_j (∂_j G(ω))² ≤ ξ² C_b (1 + (log B + 1)/σ + log (2 + S))` in `[0, ∞]`. -/
theorem tsum_coordDeriv_sq_le (hd : 1 ≤ d) (F : PairingFrame d) {ξ : ℝ} (hξ : 0 ≤ ξ)
    {D : DistRd d → ContMetric d} {ω : Coord} (hω : ω ∈ F.good) (hW : WeylAt ξ D (F.T ω))
    {η : C(unitInterval, Rd d)} (hη : IsConstSpeedGeod (rho D (F.T ω)) 0 (e₁ d) η)
    {S B σ : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hrange : range η ⊆ closedBall (0 : Rd d) S)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      (pathMeasure η (closedBall z r)).toReal ≤ B * r ^ σ) :
    ∑' j, ENNReal.ofReal (coordDeriv (logRhoFrame F D) j ω ^ 2) ≤
      ENNReal.ofReal (ξ ^ 2 * (F.Cb * (1 + (Real.log B + 1) / σ + Real.log (2 + S)))) := by
  have hbess := F.bessel (pathMeasure η) (isProbabilityMeasure_pathMeasure η) S B σ hS hB hσ hσ1
    (pathMeasure_compl_eq_zero η hrange) hball
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  calc ∑ j ∈ Finset.range n, ENNReal.ofReal (coordDeriv (logRhoFrame F D) j ω ^ 2)
      ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (ξ ^ 2 * (∫ x, F.e j x ∂(pathMeasure η)) ^ 2) := by
        refine Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal ?_
        have h := abs_coordDeriv_logRho_le hd F hξ hω hW j hη
        rw [← sq_abs]
        calc |coordDeriv (logRhoFrame F D) j ω| ^ 2
            ≤ (ξ * |∫ x, F.e j x ∂(pathMeasure η)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
          _ = ξ ^ 2 * (∫ x, F.e j x ∂(pathMeasure η)) ^ 2 := by rw [mul_pow, sq_abs]
    _ = ENNReal.ofReal (ξ ^ 2 * ∑ j ∈ Finset.range n, (∫ x, F.e j x ∂(pathMeasure η)) ^ 2) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    _ ≤ ENNReal.ofReal (ξ ^ 2 * (F.Cb * (1 + (Real.log B + 1) / σ + Real.log (2 + S)))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hbess n) (sq_nonneg ξ))

/-! ## The full-measure set for hypothesis (H) -/

/-- **Hypothesis (H) on a measurable full set** (blueprint `c:lem-shiftlip`): for `D` strong at `(ξ, Q)` with
`ξ ≥ 0` there is a measurable `𝒢 ⊆ good` of full `stdP`-measure on which Weyl scaling holds at `T ω` and
`|G(ω + v) - G(ω + v')| ≤ ∑_j ξ ‖e_j‖_∞ |v_j - v'_j|`. -/
theorem exists_good_shiftLipschitz (hd : 1 ≤ d) (F : PairingFrame d) {ξ Q : ℝ} (hξ : 0 ≤ ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D) :
    ∃ 𝒢 : Set Coord, MeasurableSet 𝒢 ∧ stdP 𝒢ᶜ = 0 ∧ 𝒢 ⊆ F.good ∧
      (∀ ω ∈ 𝒢, WeylAt ξ D (F.T ω)) ∧
      ∀ ω ∈ 𝒢, ∀ v v' : ℕ →₀ ℝ,
        |logRhoFrame F D (shiftBy ω v) - logRhoFrame F D (shiftBy ω v')| ≤
          ∑ j ∈ v.support ∪ v'.support, ξ * frameBound F j * |v j - v' j| := by
  have hlgf : IsLGFPlusCont F.T stdP := F.normalized.1.isLGFPlusCont
  have hweyl : ∀ᵐ ω ∂stdP, WeylAt ξ D (F.T ω) := hD.weyl stdP F.T hlgf
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hweyl)
  have hW : ∀ ω ∉ t, WeylAt ξ D (F.T ω) := fun ω hω => by
    by_contra h
    exact hω (hst h)
  refine ⟨F.good ∩ tᶜ, F.measurableSet_good.inter htm.compl, ?_, inter_subset_left,
    fun ω hω => hW ω hω.2, fun ω hω v v' =>
      logRhoFrame_shiftLipschitz hd F hξ hω.1 (hW ω hω.2) v v'⟩
  rw [compl_inter, compl_compl]
  exact measure_union_null F.ae_good ht0

/-- **The derivative identity, almost surely** (the `ℝ^d` port of GaussianLQG's `Setup.ae_hasDerivAt_logD`): for
`D` strong at `(ξ, Q)` with `ξ ≥ 0`, almost surely, for every `j`, `t ↦ G(ω + t δ_j)` is differentiable at `0`
(by (H) and GaussianLQG's `ae_differentiableAt_coord`), and for every constant-speed `ρ_{T ω}`-geodesic `η` from
`0` to `e₁` its derivative there is `ξ ∫ e_j dν_η`. (The proof of `concentration_logRho` only needs the bound
`abs_coordDeriv_logRho_le`.) -/
theorem ae_hasDerivAt_logRhoFrame (hd : 1 ≤ d) (F : PairingFrame d) {ξ Q : ℝ} (hξ : 0 ≤ ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ Q D) :
    ∀ᵐ ω ∂stdP, ∀ j : ℕ,
      DifferentiableAt ℝ (fun t => logRhoFrame F D (shiftBy ω (Finsupp.single j t))) 0 ∧
        ∀ η : C(unitInterval, Rd d), IsConstSpeedGeod (rho D (F.T ω)) 0 (e₁ d) η →
          HasDerivAt (fun t => logRhoFrame F D (shiftBy ω (Finsupp.single j t)))
            (ξ * ∫ x, F.e j x ∂(pathMeasure η)) 0 := by
  obtain ⟨𝒢, h𝒢m, h𝒢c, h𝒢good, h𝒢W, hH⟩ := exists_good_shiftLipschitz hd F hξ hD
  have hdiff : ∀ j : ℕ, ∀ᵐ ω ∂stdP,
      DifferentiableAt ℝ (fun t => logRhoFrame F D (shiftBy ω (Finsupp.single j t))) 0 :=
    fun j => GaussianLQG.ae_differentiableAt_coord (measurable_logRhoFrame F hD.measurable) h𝒢m
      h𝒢c (L := fun j => ξ * frameBound F j) hH j
  have h𝒢ae : ∀ᵐ ω ∂stdP, ω ∈ 𝒢 := mem_ae_iff.2 h𝒢c
  filter_upwards [ae_all_iff.2 hdiff, h𝒢ae] with ω hdω hω j
  exact ⟨hdω j, fun η hη =>
    hasDerivAt_logRhoFrame_of_isConstSpeedGeod hd F (h𝒢good hω) (h𝒢W ω hω) j hη (hdω j)⟩

end HigherDimLQGContinuity

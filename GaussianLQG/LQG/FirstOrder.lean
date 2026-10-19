import GaussianLQG.LQG.Concentration
import GaussianLQG.Core.InterfacesEuclid
import GaussianLQG.Core.Interfaces
import GaussianLQG.Field.Pairing
import GaussianLQG.LQG.Scaling
import GaussianLQG.LQG.Geodesics
import GaussianLQG.LQG.Exponents
import GaussianLQG.Energy.All

/-!
# First-order expansion of `log D(z, w)` (blueprint Proposition `prop:first-order`)

For `S : Setup`, `z ≠ w` and `γ > 0` let
`F_{z,w}(ω) = (log D^γ(z, w) - b_γ - ξ_γ Q_γ log |z - w|) / ξ_γ - (h, λ_{z,w})`
(`Setup.firstOrderErr`). Assuming blueprint Lemma `lem:energy-approx` (`Setup.EnergyApprox`):

* `Setup.firstOrder` (blueprint Proposition `prop:first-order`, source Proposition 5.1): for compact
  `K`, `δ > 0` and `p ≥ 1` there are `γ* > 0` and `C` such that for `γ ∈ (0, γ*]` and all
  `z, w ∈ K` with `|z - w| ≥ δ`, `‖F_{z,w}‖_p ≤ C ξ_γ^{1/24}`;
* `Setup.fixedPairConv` (blueprint Corollary `cor:fixed-pair`, source (5.5)): the interface
  proposition `Setup.FixedPairConv`, `(log D^γ(0, 1) - b_γ) / ξ_γ → H(0, 0)` in probability.

Proof of `prop:first-order` (blueprint). `F ∈ L^p` by Lemma `lem:scaling`(a),(b) and Lemma
`lem:field`(b) (`Setup.exists_memLp_log_D_pair`), and `E F = 0` by Lemma `lem:scaling`(b). On the
full-measure set `𝒢 = Ω_γ ∩ Ω_{λ_{z,w}}`, Lemma `lem:derivative`(a) and Lemma `lem:field`(a) give
hypothesis (H) of the Gaussian `L^p` inequality with `L_j = 2 ‖e_j‖_∞`
(`Setup.abs_firstOrderErr_shiftBy_sub_le`). Almost surely `∂_j F = ∫ e_j dν_η - ∫ e_j dλ_{z,w}`
for every geodesic `η` (Lemma `lem:derivative`(b), `Setup.hasDerivAt_firstOrderErr`), so by the
polarized frame identity `∑_j (∂_j F)² = ‖ν_η - λ_{z,w}‖_*² ≤ Y_γ²`
(`Setup.hasSum_sq_sub_frameCoef`, Lemma `lem:energy-approx`); geodesics exist a.s. by Lemma
`lem:geodesics-exist`. Proposition `prop:gaussian-Lp` gives `‖F‖_p ≤ c_p ‖Y_γ‖_p`. The constants
are uniform in `z, w` because `Y_γ` does not depend on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

namespace Setup

variable (S : Setup)

/-! ## The first-order error -/

/-- `F_{z,w}(ω) = (log D^γ(z, w) - b_γ - ξ_γ Q_γ log |z - w|) / ξ_γ - (h, λ_{z,w})(ω)`, the
quantity inside the norm in blueprint Proposition `prop:first-order`. -/
def firstOrderErr (γ : ℝ) (z w : ℂ) (ω : Coord) : ℝ :=
  (Real.log ((S.D γ ω).1 (z, w)) - S.b γ - S.ξ γ * Q γ * Real.log ‖z - w‖) / S.ξ γ -
    pairing S.e (segMeasure z w) ω

theorem measurable_firstOrderErr (γ : ℝ) (z w : ℂ) : Measurable (S.firstOrderErr γ z w) :=
  ((((S.measurable_log_D γ z w).sub_const _).sub_const _).div_const _).sub
    (measurable_pairing _ _)

/-! ## The square function -/

/-- `∑_j (∫ e_j dν - ∫ e_j dμ)² = ℰ(ν, ν) - 2 ℰ(ν, μ) + ℰ(μ, μ) = ‖ν - μ‖_*²` for regular `ν, μ`
(the polarized frame identity, blueprint (eq:frame)). -/
theorem hasSum_sq_sub_frameCoef {ν μ : Measure ℂ} (hν : IsRegular ν) (hμ : IsRegular μ) :
    HasSum (fun j => (∫ x, S.e j x ∂ν - ∫ x, S.e j x ∂μ) ^ 2)
      (energy ν ν - 2 * energy ν μ + energy μ μ) := by
  have h1 := S.frame.2.2 ν ν hν hν
  have h2 := (S.frame.2.2 ν μ hν hμ).mul_left 2
  have h3 := S.frame.2.2 μ μ hμ hμ
  have e : (fun j => (∫ x, S.e j x ∂ν - ∫ x, S.e j x ∂μ) ^ 2) = fun j =>
      (∫ x, S.e j x ∂ν) * (∫ x, S.e j x ∂ν) - 2 * ((∫ x, S.e j x ∂ν) * (∫ x, S.e j x ∂μ)) +
        (∫ x, S.e j x ∂μ) * (∫ x, S.e j x ∂μ) := by
    funext j
    ring
  rw [e]
  exact (h1.sub h2).add h3

/-! ## Moments of `log D(z, w)` -/

/-- **Lemma `lem:scaling`(a),(b)**, `L^p` form for every pair: for `p ≥ 1` there is `γ* ∈ (0, 2)`
such that `log D^γ(z, w) ∈ L^p` for all `γ ∈ (0, γ*]` and `z ≠ w`. -/
theorem exists_memLp_log_D_pair {p : ℝ} (hp : 1 ≤ p) :
    ∃ γs : ℝ, 0 < γs ∧ γs < 2 ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ z w : ℂ, z ≠ w →
      MemLp (fun ω => Real.log ((S.D γ ω).1 (z, w))) (ENNReal.ofReal p) stdP := by
  obtain ⟨γ1, hγ1, h1⟩ := S.memLp_log_D p hp
  refine ⟨min γ1 1, lt_min hγ1 one_pos, (min_le_right _ _).trans_lt one_lt_two,
    fun γ hγ z w hzw => ?_⟩
  have hγ0 : 0 < γ := hγ.1
  have hγ2 : γ < 2 := (hγ.2.trans (min_le_right _ _)).trans_lt one_lt_two
  have hY := h1 γ ⟨hγ0, hγ.2.trans (min_le_left _ _)⟩
  have hr : 0 < ‖w - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw.symm)
  set X : Coord → ℝ := fun ω => Real.log ((S.D γ ω).1 (z, w)) -
    S.ξ γ * Q γ * Real.log ‖w - z‖ - S.ξ γ * pairing S.e (circleMeasure z ‖w - z‖) ω with hXdef
  have hXm : Measurable X :=
    ((S.measurable_log_D γ z w).sub_const _).sub ((measurable_pairing _ _).const_mul _)
  have hmap := S.map_log_D_sub hγ0 hγ2 hzw
  have hX : MemLp X (ENNReal.ofReal p) stdP := by
    have hYm := S.measurable_log_D γ 0 1
    have e1 := (memLp_map_measure_iff (g := id) aestronglyMeasurable_id hYm.aemeasurable).2 hY
    rw [← hmap] at e1
    exact (memLp_map_measure_iff (g := id) aestronglyMeasurable_id hXm.aemeasurable).1 e1
  have hc : MemLp (pairing S.e (circleMeasure z ‖w - z‖)) (ENNReal.ofReal p) stdP :=
    memLp_pairing S.frame (isRegular_circleMeasure z hr) ENNReal.ofReal_ne_top
  have e : (fun ω => Real.log ((S.D γ ω).1 (z, w))) = fun ω =>
      X ω + S.ξ γ * Q γ * Real.log ‖w - z‖ + S.ξ γ * pairing S.e (circleMeasure z ‖w - z‖) ω := by
    funext ω
    simp only [hXdef]
    ring
  rw [e]
  exact (hX.add (memLp_const _)).add (hc.const_mul _)

/-! ## Hypothesis (H) of the Gaussian `L^p` inequality -/

/-- `f_v` is integrable against any finite measure. -/
theorem integrable_frameFun (μ : Measure ℂ) [IsFiniteMeasure μ] (v : ℕ →₀ ℝ) :
    Integrable (frameFun S.e v) μ := by
  obtain ⟨M, hM⟩ := S.exists_abs_frameFun_le v
  exact Integrable.of_bound (frameFunC S.e S.frame.1 v).continuous.aestronglyMeasurable M
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- `|∫ f_v dμ - ∫ f_{v'} dμ| ≤ ∑_j ‖e_j‖_∞ |v_j - v'_j|` for a probability measure `μ`. -/
theorem abs_integral_frameFun_sub_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (v v' : ℕ →₀ ℝ) :
    |∫ x, frameFun S.e v x ∂μ - ∫ x, frameFun S.e v' x ∂μ| ≤
      ∑ j ∈ v.support ∪ v'.support, S.supE j * |v j - v' j| := by
  rw [← integral_sub (S.integrable_frameFun μ v) (S.integrable_frameFun μ v'), ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x => frameFun S.e v x - frameFun S.e v' x)
    (C := ∑ j ∈ v.support ∪ v'.support, S.supE j * |v j - v' j|)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact S.abs_frameFun_sub_le v v' x)
  rwa [probReal_univ, mul_one] at h

/-- **Hypothesis (H) for `F_{z,w}`** (blueprint proof of Proposition `prop:first-order`): at a base
point `ω ∈ Ω_{λ_{z,w}}` where the Lipschitz bound of Lemma `lem:derivative`(a) holds,
`|F(ω + v) - F(ω + v')| ≤ ∑_j 2 ‖e_j‖_∞ |v_j - v'_j|`. -/
theorem abs_firstOrderErr_shiftBy_sub_le {γ : ℝ} (hξ : 0 < S.ξ γ) {z w : ℂ} {ω : Coord}
    (hlog : ∀ v v' : ℕ →₀ ℝ, |Real.log ((S.D γ (shiftBy ω v)).1 (z, w)) -
        Real.log ((S.D γ (shiftBy ω v')).1 (z, w))| ≤
      ∑ j ∈ v.support ∪ v'.support, S.ξ γ * S.supE j * |v j - v' j|)
    (hω : ω ∈ pairingSet S.e (segMeasure z w)) (v v' : ℕ →₀ ℝ) :
    |S.firstOrderErr γ z w (shiftBy ω v) - S.firstOrderErr γ z w (shiftBy ω v')| ≤
      ∑ j ∈ v.support ∪ v'.support, 2 * S.supE j * |v j - v' j| := by
  set T := ∑ j ∈ v.support ∪ v'.support, S.supE j * |v j - v' j| with hT
  have h1 : |Real.log ((S.D γ (shiftBy ω v)).1 (z, w)) -
      Real.log ((S.D γ (shiftBy ω v')).1 (z, w))| ≤ S.ξ γ * T := by
    refine (hlog v v').trans (le_of_eq ?_)
    rw [hT, Finset.mul_sum]
    simp only [mul_assoc]
  have h2 := S.abs_integral_frameFun_sub_le (segMeasure z w) v v'
  rw [← hT] at h2
  have hpv := pairing_shiftBy S.frame hω v
  have hpv' := pairing_shiftBy S.frame hω v'
  have hsum : ∑ j ∈ v.support ∪ v'.support, 2 * S.supE j * |v j - v' j| = T + T := by
    rw [hT, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  unfold firstOrderErr
  rw [hpv, hpv']
  set a := Real.log ((S.D γ (shiftBy ω v)).1 (z, w))
  set a' := Real.log ((S.D γ (shiftBy ω v')).1 (z, w))
  have e : (a - S.b γ - S.ξ γ * Q γ * Real.log ‖z - w‖) / S.ξ γ -
      (pairing S.e (segMeasure z w) ω + ∫ x, frameFun S.e v x ∂(segMeasure z w)) -
      ((a' - S.b γ - S.ξ γ * Q γ * Real.log ‖z - w‖) / S.ξ γ -
        (pairing S.e (segMeasure z w) ω + ∫ x, frameFun S.e v' x ∂(segMeasure z w))) =
      (a - a') / S.ξ γ - (∫ x, frameFun S.e v x ∂(segMeasure z w) -
        ∫ x, frameFun S.e v' x ∂(segMeasure z w)) := by
    field_simp
    ring
  rw [e]
  have h3 : |(a - a') / S.ξ γ| ≤ T := by
    rw [abs_div, abs_of_pos hξ, div_le_iff₀ hξ, mul_comm]
    exact h1
  exact (abs_sub _ _).trans (add_le_add h3 h2)

/-! ## The derivative of `F_{z,w}` -/

/-- **Blueprint proof of Proposition `prop:first-order`**: at `ω ∈ Ω_{λ_{z,w}}`, if
`t ↦ log D(ω + t δ_j)(z, w)` has derivative `ξ d` at `0`, then `t ↦ F(ω + t δ_j)` has derivative
`d - ∫ e_j dλ_{z,w}` at `0`. -/
theorem hasDerivAt_firstOrderErr {γ : ℝ} (hξ : S.ξ γ ≠ 0) {z w : ℂ} {ω : Coord}
    (hω : ω ∈ pairingSet S.e (segMeasure z w)) {j : ℕ} {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w)))
      (S.ξ γ * d) 0) :
    HasDerivAt (fun t : ℝ => S.firstOrderErr γ z w (shiftBy ω (Finsupp.single j t)))
      (d - ∫ x, S.e j x ∂(segMeasure z w)) 0 := by
  set a := ∫ x, S.e j x ∂(segMeasure z w) with ha
  set c := S.b γ + S.ξ γ * Q γ * Real.log ‖z - w‖ with hc
  have e : (fun t : ℝ => S.firstOrderErr γ z w (shiftBy ω (Finsupp.single j t))) = fun t =>
      (Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w)) - c) / S.ξ γ -
        (pairing S.e (segMeasure z w) ω + t * a) := by
    funext t
    unfold firstOrderErr
    rw [pairing_shiftBy S.frame hω]
    have hint : ∫ x, frameFun S.e (Finsupp.single j t) x ∂(segMeasure z w) = t * a := by
      simp_rw [frameFun_single]
      rw [integral_const_mul]
    rw [hint, hc]
    ring
  rw [e]
  have h1 := (hd.sub_const c).div_const (S.ξ γ)
  have h2 : HasDerivAt (fun t : ℝ => pairing S.e (segMeasure z w) ω + t * a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add (pairing S.e (segMeasure z w) ω)
  have h := h1.sub h2
  rwa [mul_div_cancel_left₀ _ hξ] at h

/-! ## Proposition `prop:first-order` -/

/-- The constant `c_p = (π/2) (E|N|^p)^{1/p}` of the Gaussian `L^p` inequality is nonnegative. -/
theorem gaussLp_const_nonneg (p : ℝ) :
    0 ≤ Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p) := by
  have h : 0 ≤ ∫ x, |x| ^ p ∂gaussianReal 0 1 :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) p
  exact mul_nonneg (by positivity) (Real.rpow_nonneg h _)

/-- **Blueprint Proposition `prop:first-order`** (source Proposition 5.1), assuming Lemma
`lem:energy-approx` (`Setup.EnergyApprox`). For compact `K`, `δ > 0` and `p ≥ 1` there are
`γ* > 0` and `C` such that for `γ ∈ (0, γ*]` and all `z, w ∈ K` with `|z - w| ≥ δ`,
`‖(log D^γ(z,w) - b_γ - ξ_γ Q_γ log |z - w|) / ξ_γ - (h, λ_{z,w})‖_p ≤ C ξ_γ^{1/24}`. -/
theorem firstOrder (hY : S.EnergyApprox) {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ z ∈ K, ∀ w ∈ K, δ ≤ ‖z - w‖ →
      eLpNorm (fun ω => (Real.log ((S.D γ ω).1 (z, w)) - S.b γ -
          S.ξ γ * LQGMetric.Q γ * Real.log ‖z - w‖) / S.ξ γ - pairing S.e (segMeasure z w) ω)
        (ENNReal.ofReal p) stdP ≤ ENNReal.ofReal (C * S.ξ γ ^ (1 / 24 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨γY, CY, hγY, hYγ⟩ := hY K hK δ hδ p hp
  obtain ⟨γ1, hγ1, hγ12, hmem⟩ := S.exists_memLp_log_D_pair hp
  obtain ⟨γ2, hγ2, hint⟩ := S.exists_integral_log_D
  obtain ⟨γg, hγg, -, hgeo⟩ := S.exists_ae_geodesics S.annulusScaling
  set cp : ℝ := Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p) with hcp
  have hcp0 : 0 ≤ cp := gaussLp_const_nonneg p
  set C' : ℝ := max CY 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨min (min γY γ1) (min γ2 γg), cp * C' ^ (1 / p),
    lt_min (lt_min hγY hγ1) (lt_min hγ2 hγg), ?_⟩
  rintro γ ⟨hγ0, hγs⟩ z hz w hw hzw
  have hγY' : γ ≤ γY := hγs.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγ1' : γ ≤ γ1 := hγs.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγ2' : γ ≤ γ2 := hγs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγg' : γ ≤ γg := hγs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγlt2 : γ < 2 := hγ1'.trans_lt hγ12
  have hξ : 0 < S.ξ γ := S.ξ_pos γ hγ0 hγlt2
  have hzw' : z ≠ w := fun h => by
    rw [h, sub_self, norm_zero] at hzw
    linarith
  obtain ⟨Y, -, hYp, hYae⟩ := hYγ γ ⟨hγ0, hγY'⟩
  set F : Coord → ℝ := S.firstOrderErr γ z w with hF
  change eLpNorm F (ENNReal.ofReal p) stdP ≤ _
  -- measurability and moments
  have hFm : Measurable F := S.measurable_firstOrderErr γ z w
  have hlogp := hmem γ ⟨hγ0, hγ1'⟩ z w hzw'
  have hlam : IsRegular (segMeasure z w) := isRegular_segMeasure hzw'
  have hpairp : MemLp (pairing S.e (segMeasure z w)) (ENNReal.ofReal p) stdP :=
    memLp_pairing S.frame hlam ENNReal.ofReal_ne_top
  have hFp : MemLp F (ENNReal.ofReal p) stdP := by
    have h := (((hlogp.sub (memLp_const (S.b γ))).sub
      (memLp_const (S.ξ γ * Q γ * Real.log ‖z - w‖))).mul_const (S.ξ γ)⁻¹).sub hpairp
    refine h.congr_norm hFm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [hF, firstOrderErr, div_eq_mul_inv, Pi.sub_apply]
  -- `E F = 0` (Lemma `lem:scaling`(b))
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hF0 : ∫ ω, F ω ∂stdP = 0 := by
    have hi1 : Integrable (fun ω => Real.log ((S.D γ ω).1 (z, w))) stdP := hlogp.integrable hp1
    have hE := hint γ ⟨hγ0, hγ2'⟩ z w hzw'
    have hP := integral_pairing S.frame hlam
    have hi2 : Integrable (fun ω => Real.log ((S.D γ ω).1 (z, w)) - S.b γ) stdP :=
      hi1.sub (integrable_const _)
    have hi3 : Integrable (fun ω => Real.log ((S.D γ ω).1 (z, w)) - S.b γ -
        S.ξ γ * Q γ * Real.log ‖z - w‖) stdP := hi2.sub (integrable_const _)
    simp only [hF, firstOrderErr]
    rw [integral_sub (hi3.div_const _) (hpairp.integrable hp1), integral_div,
      integral_sub hi2 (integrable_const _), integral_sub hi1 (integrable_const _),
      integral_const, integral_const, probReal_univ, one_smul, one_smul, hE, hP, norm_sub_rev w z]
    simp
  -- hypothesis (H) on `𝒢 = Ω_γ ∩ Ω_{λ_{z,w}}`
  obtain ⟨Ω, hΩm, hΩc, hΩ⟩ := S.exists_logD_shiftLipschitz hγ0 hγlt2
  have h𝒢m : MeasurableSet (Ω ∩ pairingSet S.e (segMeasure z w)) :=
    hΩm.inter (measurableSet_pairingSet _ _)
  have h𝒢c : stdP (Ω ∩ pairingSet S.e (segMeasure z w))ᶜ = 0 := by
    rw [compl_inter]
    exact measure_union_null hΩc (ae_iff.1 (ae_mem_pairingSet S.frame hlam))
  have hH : ∀ ω ∈ Ω ∩ pairingSet S.e (segMeasure z w), ∀ v v' : ℕ →₀ ℝ,
      |F (shiftBy ω v) - F (shiftBy ω v')| ≤
        ∑ j ∈ v.support ∪ v'.support, (2 * S.supE j) * |v j - v' j| :=
    fun ω hω v v' => S.abs_firstOrderErr_shiftBy_sub_le hξ (hΩ ω hω.1 z w hzw') hω.2 v v'
  have hW1 := gaussian_Lp_inequality (L := fun j => 2 * S.supE j) hFm h𝒢m h𝒢c hH hp hFp
  -- the square function: `∑_j (∂_j F)² = ‖ν_η - λ_{z,w}‖_*² ≤ Y²` almost surely
  have hsq : ∀ᵐ ω ∂stdP, (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ≤ Y ω ^ 2 := by
    filter_upwards [S.ae_hasDerivAt_logD hγ0 hγlt2 hzw', ae_mem_pairingSet S.frame hlam,
      hgeo γ ⟨hγ0, hγg'⟩, hYae] with ω hd hωlam hg hYω
    obtain ⟨η, hη⟩ := hg.2.2.2 z w
    obtain ⟨hνreg, hE⟩ := hYω z hz w hw hzw η hη
    have hderiv : ∀ j, coordDeriv F j ω =
        ∫ x, S.e j x ∂(lengthMeasure η) - ∫ x, S.e j x ∂(segMeasure z w) :=
      fun j => (S.hasDerivAt_firstOrderErr hξ.ne' hωlam ((hd j).2 η hη)).deriv
    simp_rw [hderiv]
    have hs := S.hasSum_sq_sub_frameCoef hνreg hlam
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hs.summable, hs.tsum_eq]
    exact hE
  -- conclusion
  have hlhs : eLpNorm F (ENNReal.ofReal p) stdP =
      eLpNorm (fun ω => F ω - ∫ ω', F ω' ∂stdP) (ENNReal.ofReal p) stdP := by
    rw [hF0]
    simp only [sub_zero]
  rw [hlhs]
  refine hW1.trans ?_
  have hint2 : (∫⁻ ω, (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ^ (p / 2) ∂stdP) ≤
      ∫⁻ ω, Y ω ^ p ∂stdP := by
    refine lintegral_mono_ae ?_
    filter_upwards [hsq] with ω hω
    calc (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ^ (p / 2) ≤ (Y ω ^ 2) ^ (p / 2) :=
          ENNReal.rpow_le_rpow hω (by positivity)
      _ = Y ω ^ p := by
          rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
          congr 1
          ring
  have hYb : (∫⁻ ω, Y ω ^ p ∂stdP) ≤ ENNReal.ofReal (C' * S.ξ γ ^ (p / 24)) :=
    hYp.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  calc ENNReal.ofReal cp *
        (∫⁻ ω, (∑' j, ENNReal.ofReal (coordDeriv F j ω ^ 2)) ^ (p / 2) ∂stdP) ^ (1 / p)
      ≤ ENNReal.ofReal cp * (ENNReal.ofReal (C' * S.ξ γ ^ (p / 24))) ^ (1 / p) := by
        gcongr
        exact hint2.trans hYb
    _ = ENNReal.ofReal (cp * C' ^ (1 / p) * S.ξ γ ^ (1 / 24 : ℝ)) := by
        have hexp : p / 24 * (1 / p) = 1 / 24 := by
          field_simp
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← ENNReal.ofReal_mul hcp0, Real.mul_rpow hC'0 (by positivity),
          ← Real.rpow_mul hξ.le, hexp]
        congr 1
        rw [hcp]
        ring

/-! ## Corollary `cor:fixed-pair` -/

/-- `ξ_γ → 0` with `ξ_γ > 0` as `γ ↓ 0` (Lemma `lem:exponents`). -/
theorem tendsto_xi_nhdsGT : Tendsto S.ξ (𝓝[>] 0) (𝓝[>] 0) := by
  obtain ⟨⟨γe, C₁, hγe, hγe2, hb⟩, -, -⟩ := S.exponents
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), γ ∈ Ioc (0 : ℝ) γe := Ioc_mem_nhdsGT hγe
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ?_ ?_
    · filter_upwards [hev] with γ hγ
      have h := (hb γ hγ).1
      have h0 := hγ.1
      exact le_trans (by positivity) h
    · filter_upwards [hev] with γ hγ
      exact (hb γ hγ).2.1
  · filter_upwards [hev] with γ hγ
    exact S.ξ_pos γ hγ.1 (by linarith [hγ.2])

/-- `C ξ_γ^a → 0` as `γ ↓ 0`, for `a > 0`. -/
theorem tendsto_mul_xi_rpow (C : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun γ => C * S.ξ γ ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun γ => S.ξ γ ^ a) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto).comp
      (tendsto_nhdsWithin_iff.1 S.tendsto_xi_nhdsGT).1
    rwa [Real.zero_rpow ha.ne'] at h
  have h2 := h1.const_mul C
  rwa [mul_zero] at h2

/-- `C ξ_γ^a → 0` as `γ ↓ 0`, for `a > 0`, in `[0, ∞]`. -/
theorem tendsto_ofReal_mul_xi_rpow (C : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun γ => ENNReal.ofReal (C * S.ξ γ ^ a)) (𝓝[>] 0) (𝓝 0) := by
  have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp (S.tendsto_mul_xi_rpow C ha)
  rwa [ENNReal.ofReal_zero] at h3

/-- **Blueprint Corollary `cor:fixed-pair`** (source (5.5)), assuming Lemma `lem:energy-approx`:
`(log D^γ(0, 1) - b_γ) / ξ_γ → H(0, 0)` in probability as `γ ↓ 0`. Proof: Proposition
`prop:first-order` with `K` the unit square, `δ = 1`, `z = 0`, `w = 1`, `p = 1`; here
`log |z - w| = 0` and `λ_{0,1} = λ_{i·0, 1+i·0}`. -/
theorem fixedPairConv (hY : S.EnergyApprox) : S.FixedPairConv := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨γs, C, hγs, hC⟩ := S.firstOrder hY hK one_pos (le_refl (1 : ℝ))
  have h0 : (0 : ℂ) ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
    simp [Complex.mem_reProdIm]
  have h1 : (1 : ℂ) ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1 := by
    simp [Complex.mem_reProdIm]
  have hn : (1 : ℝ) ≤ ‖(0 : ℂ) - 1‖ := by simp
  unfold FixedPairConv
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := ENNReal.ofReal 1) (by simp)
    (fun γ => (((S.measurable_log_D γ 0 1).sub_const _).div_const _).aestronglyMeasurable)
    (S.measurable_H 0 0).aestronglyMeasurable ?_
  have heq : ∀ γ, (fun ω => (Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) / S.ξ γ) - S.H 0 0 =
      fun ω => (Real.log ((S.D γ ω).1 (0, 1)) - S.b γ -
        S.ξ γ * Q γ * Real.log ‖(0 : ℂ) - 1‖) / S.ξ γ - pairing S.e (segMeasure 0 1) ω := by
    intro γ
    funext ω
    simp only [Pi.sub_apply, S.H_zero_zero, zero_sub, norm_neg, norm_one, Real.log_one,
      mul_zero, sub_zero]
  simp_rw [heq]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (S.tendsto_ofReal_mul_xi_rpow C (by norm_num : (0 : ℝ) < 1 / 24))
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioc_mem_nhdsGT hγs] with γ hγ
  exact hC γ hγ 0 h0 1 h1 hn

end Setup

end GaussianLQG

import GaussianLQG.Core.Setup
import GaussianLQG.LQG.Scaling.Measurability
import GaussianLQG.Metric.Weyl
import GaussianLQG.Probability.GaussianLp.CoordDeriv

/-!
# Cameron–Martin derivatives of `log D(z, w)` (blueprint Lemma `lem:derivative`)

Let `S : Setup`, `0 < γ < 2`, `ξ = S.ξ γ`, `z ≠ w`, and `F(ω) = log D^γ(ω)(z, w)`. Blueprint Lemma
`lem:derivative` (source Lemma 3.1):

* (a) `Setup.abs_logD_shiftBy_sub_le`, `Setup.exists_logD_shiftLipschitz`: on the full-measure set
  `Ω_γ` of (S2)–(S3) (`Setup.good`), for every base point `ω` and all finitely supported `v, v'`,
  `|F(ω + v) - F(ω + v')| ≤ ∑_j ξ ‖e_j‖_∞ |v_j - v'_j|`. This is hypothesis (H) of the Gaussian
  `L^p` inequality (`GaussianLQG.gaussian_Lp_inequality`) with `L_j = ξ ‖e_j‖_∞`
  (`‖e_j‖_∞ = Setup.supE S j`).
* (b) `Setup.ae_hasDerivAt_logD`: almost surely, for every `j`, `t ↦ F(ω + t δ_j)` is
  differentiable at `0`, and for every constant-speed `D^γ(ω)`-geodesic `η` from `z` to `w` its
  derivative there is `ξ ∫ e_j dν_η`. Equivalently (`Setup.ae_coordDeriv_logD_eq`),
  `∂_j F(ω) = ξ ∫ e_j dν_η`.

Proofs (blueprint). (a) By (S3) at `ω`, `F(ω + v) = log (e^{ξ f_v}·D(ω))(z, w)`; apply
`abs_log_weylScale_sub_le` and `sup |f_v - f_{v'}| ≤ ∑_j ‖e_j‖_∞ |v_j - v'_j|`.
(b) By (a), `ae_differentiableAt_coord` gives the derivatives a.s. Along a geodesic `η`, the
comparison `weylScale_le_of_isGeod01`, `log x ≤ x - 1` and `e^y ≤ 1 + y + y²` (`|y| ≤ 1`) give
`F(ω + t δ_j) - F(ω) ≤ ξ t ∫ e_j dν_η + (ξ ‖e_j‖_∞)² t²` for small `|t|`
(`Setup.logD_shiftBy_single_le`). Hence `t ↦ F(ω + t δ_j) - ξ t ∫ e_j dν_η - (ξ ‖e_j‖_∞)² t²` has a
local maximum at `t = 0`, and its derivative there vanishes. (The blueprint divides by `t > 0` and
`t < 0` separately; the local-maximum form packages both one-sided limits.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-! ## Frame functions -/

/-- `f_v = ∑_{j ∈ s} v_j e_j` for every finite set `s` containing the support of `v`. -/
theorem frameFun_eq_sum (e : ℕ → ℂ → ℝ) {v : ℕ →₀ ℝ} {s : Finset ℕ} (hs : v.support ⊆ s)
    (x : ℂ) : frameFun e v x = ∑ j ∈ s, v j * e j x := by
  unfold frameFun
  exact Finsupp.sum_of_support_subset v hs (fun j c => c * e j x) (fun j _ => zero_mul _)

/-- The bundled `f_v` evaluates to `f_v`. -/
theorem frameFunC_apply (e : ℕ → ℂ → ℝ) (he : ∀ j, Continuous (e j)) (v : ℕ →₀ ℝ) (x : ℂ) :
    frameFunC e he v x = frameFun e v x := rfl

/-- `f_{t δ_j} = t e_j`. -/
theorem frameFun_single (e : ℕ → ℂ → ℝ) (j : ℕ) (t : ℝ) (x : ℂ) :
    frameFun e (Finsupp.single j t) x = t * e j x := by
  unfold frameFun
  exact Finsupp.sum_single_index (zero_mul _)

/-- The length-measure integral of a continuous function is the time integral along the path. -/
theorem integral_lengthMeasure (η : C(unitInterval, ℂ)) {f : ℂ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(lengthMeasure η) = ∫ t in (0 : ℝ)..1, f (η (projIcc 0 1 zero_le_one t)) := by
  unfold lengthMeasure
  rw [integral_map (continuous_comp_projIcc η).aemeasurable hf.aestronglyMeasurable,
    intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

namespace Setup

variable (S : Setup)

/-! ## The sup norms of the frame -/

/-- `‖e_j‖_∞ = sup_x |e_j(x)|` (finite, since the frame functions are bounded). -/
def supE (j : ℕ) : ℝ := ⨆ x, |S.e j x|

theorem bddAbove_abs_e (j : ℕ) : BddAbove (range fun x => |S.e j x|) := by
  obtain ⟨C, hC⟩ := S.frame.2.1 j
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hC x

theorem abs_e_le_supE (j : ℕ) (x : ℂ) : |S.e j x| ≤ S.supE j :=
  le_ciSup (S.bddAbove_abs_e j) x

theorem supE_nonneg (j : ℕ) : 0 ≤ S.supE j :=
  (abs_nonneg _).trans (S.abs_e_le_supE j 0)

/-- `|f_v(x) - f_{v'}(x)| ≤ ∑_j ‖e_j‖_∞ |v_j - v'_j|`. -/
theorem abs_frameFun_sub_le (v v' : ℕ →₀ ℝ) (x : ℂ) :
    |frameFun S.e v x - frameFun S.e v' x| ≤
      ∑ j ∈ v.support ∪ v'.support, S.supE j * |v j - v' j| := by
  rw [frameFun_eq_sum S.e Finset.subset_union_left x,
    frameFun_eq_sum S.e Finset.subset_union_right x, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← sub_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (S.abs_e_le_supE j x) (abs_nonneg _)

/-- `f_v` is bounded. -/
theorem exists_abs_frameFun_le (v : ℕ →₀ ℝ) : ∃ M, ∀ x, |frameFun S.e v x| ≤ M := by
  refine ⟨∑ j ∈ v.support, S.supE j * |v j|, fun x => ?_⟩
  rw [frameFun_eq_sum S.e (Finset.Subset.refl _) x]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (S.abs_e_le_supE j x) (abs_nonneg _)

/-! ## Part (a): Lipschitz property along shifts -/

/-- At a base point where (S3) holds, `D^γ(ω + v)(z, w)` is the Weyl-scaled distance
`(e^{ξ f_v}·D^γ(ω))(z, w)`. -/
theorem D_shiftBy_eq_toReal {γ : ℝ} {ω : Coord}
    (hweyl : ∀ (v : ℕ →₀ ℝ) (z w : ℂ), ENNReal.ofReal ((S.D γ (shiftBy ω v)).1 (z, w)) =
      weylScale (S.ξ γ) (frameFunC S.e S.frame.1 v) (S.D γ ω) z w)
    (v : ℕ →₀ ℝ) (z w : ℂ) :
    (S.D γ (shiftBy ω v)).1 (z, w) =
      (weylScale (S.ξ γ) (frameFunC S.e S.frame.1 v) (S.D γ ω) z w).toReal := by
  rw [← hweyl v z w, ENNReal.toReal_ofReal (ContMetric.nonneg _ z w)]

/-- **Blueprint Lemma `lem:derivative` (a)**, deterministic form: at a base point `ω` where
`D^γ(ω)` is a length metric and (S3) holds, for `z ≠ w` and all finitely supported `v, v'`,
`|F(ω + v) - F(ω + v')| ≤ ∑_j ξ ‖e_j‖_∞ |v_j - v'_j|` with `F = log D^γ(·)(z, w)`. -/
theorem abs_logD_shiftBy_sub_le {γ : ℝ} (hξ : 0 ≤ S.ξ γ) {ω : Coord}
    (hlen : (S.D γ ω).IsLength)
    (hweyl : ∀ (v : ℕ →₀ ℝ) (z w : ℂ), ENNReal.ofReal ((S.D γ (shiftBy ω v)).1 (z, w)) =
      weylScale (S.ξ γ) (frameFunC S.e S.frame.1 v) (S.D γ ω) z w)
    {z w : ℂ} (hzw : z ≠ w) (v v' : ℕ →₀ ℝ) :
    |Real.log ((S.D γ (shiftBy ω v)).1 (z, w)) - Real.log ((S.D γ (shiftBy ω v')).1 (z, w))| ≤
      ∑ j ∈ v.support ∪ v'.support, S.ξ γ * S.supE j * |v j - v' j| := by
  rw [S.D_shiftBy_eq_toReal hweyl v z w, S.D_shiftBy_eq_toReal hweyl v' z w]
  refine (abs_log_weylScale_sub_le hlen hξ (S.exists_abs_frameFun_le v)
    (S.exists_abs_frameFun_le v') hzw).trans ?_
  have hsup : (⨆ x, |frameFunC S.e S.frame.1 v x - frameFunC S.e S.frame.1 v' x|) ≤
      ∑ j ∈ v.support ∪ v'.support, S.supE j * |v j - v' j| :=
    ciSup_le fun x => S.abs_frameFun_sub_le v v' x
  calc S.ξ γ * ⨆ x, |frameFunC S.e S.frame.1 v x - frameFunC S.e S.frame.1 v' x|
      ≤ S.ξ γ * ∑ j ∈ v.support ∪ v'.support, S.supE j * |v j - v' j| :=
        mul_le_mul_of_nonneg_left hsup hξ
    _ = ∑ j ∈ v.support ∪ v'.support, S.ξ γ * S.supE j * |v j - v' j| := by
        rw [Finset.mul_sum]
        simp only [mul_assoc]

/-- **Blueprint Lemma `lem:derivative` (a).** For `0 < γ < 2` there is a measurable set `Ω` of full
`stdP`-measure (the set `Ω_γ` of (S2)–(S3) from `Setup.good`) such that for every base point
`ω ∈ Ω`, all `z ≠ w` and all finitely supported `v, v'`,
`|log D^γ(ω + v)(z, w) - log D^γ(ω + v')(z, w)| ≤ ∑_j ξ ‖e_j‖_∞ |v_j - v'_j|`.
This is hypothesis (H) of `gaussian_Lp_inequality` with `L_j = ξ ‖e_j‖_∞`. -/
theorem exists_logD_shiftLipschitz {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ Ω : Set Coord, MeasurableSet Ω ∧ stdP Ωᶜ = 0 ∧ ∀ ω ∈ Ω, ∀ z w : ℂ, z ≠ w →
      ∀ v v' : ℕ →₀ ℝ,
        |Real.log ((S.D γ (shiftBy ω v)).1 (z, w)) -
            Real.log ((S.D γ (shiftBy ω v')).1 (z, w))| ≤
          ∑ j ∈ v.support ∪ v'.support, S.ξ γ * S.supE j * |v j - v' j| := by
  obtain ⟨Ω, hΩm, hΩc, hΩ⟩ := S.good γ hγ hγ2
  exact ⟨Ω, hΩm, hΩc, fun ω hω z w hzw v v' =>
    S.abs_logD_shiftBy_sub_le (S.ξ_pos γ hγ hγ2).le (hΩ ω hω).1 (hΩ ω hω).2 hzw v v'⟩

/-! ## Part (b): the derivative along geodesics -/

/-- The competitor bound along a geodesic (blueprint proof of Lemma `lem:derivative` (b)): at a
base point `ω` where (S3) holds, for `z ≠ w`, a constant-speed geodesic `η` from `z` to `w` and
`|ξ t| ‖e_j‖_∞ ≤ 1`,
`F(ω + t δ_j) ≤ F(ω) + ξ t ∫ e_j dν_η + (ξ t ‖e_j‖_∞)²`. -/
theorem logD_shiftBy_single_le {γ : ℝ} {ω : Coord}
    (hweyl : ∀ (v : ℕ →₀ ℝ) (z w : ℂ), ENNReal.ofReal ((S.D γ (shiftBy ω v)).1 (z, w)) =
      weylScale (S.ξ γ) (frameFunC S.e S.frame.1 v) (S.D γ ω) z w)
    {z w : ℂ} (hzw : z ≠ w) (j : ℕ) {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 (S.D γ ω) z w η) {t : ℝ} (ht : |S.ξ γ * t| * S.supE j ≤ 1) :
    Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w)) ≤
      Real.log ((S.D γ ω).1 (z, w)) + S.ξ γ * t * ∫ x, S.e j x ∂(lengthMeasure η) +
        (S.ξ γ * t * S.supE j) ^ 2 := by
  set ξ := S.ξ γ with hξdef
  set M := S.supE j with hMdef
  set φ : ℝ → ℝ := fun s => S.e j (η (projIcc 0 1 zero_le_one s)) with hφdef
  have hφc : Continuous φ := (S.frame.1 j).comp (continuous_comp_projIcc η)
  have hφM : ∀ s, |φ s| ≤ M := fun s => S.abs_e_le_supE j _
  set J := ∫ s in (0 : ℝ)..1, Real.exp (ξ * (t * φ s)) with hJdef
  have hexpc : Continuous fun s => Real.exp (ξ * (t * φ s)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul hφc))
  have hLpos : 0 < (S.D γ ω).1 (z, w) :=
    lt_of_le_of_ne (ContMetric.nonneg _ z w) fun h =>
      hzw ((S.D γ ω).2.eq_of_eq_zero z w h.symm)
  have hDpos : 0 < (S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w) :=
    lt_of_le_of_ne (ContMetric.nonneg _ z w) fun h =>
      hzw ((S.D γ (shiftBy ω (Finsupp.single j t))).2.eq_of_eq_zero z w h.symm)
  have hJpos : 0 < J := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hexpc.intervalIntegrable 0 1) (fun s _ => Real.exp_pos _) zero_lt_one
  -- the Weyl comparison along `η` (blueprint `lem:weyl-compare` (c))
  have h1 : (S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w) ≤ (S.D γ ω).1 (z, w) * J := by
    have hW := weylScale_le_of_isGeod01 hη ξ (frameFunC S.e S.frame.1 (Finsupp.single j t))
    rw [← hweyl] at hW
    have hint : (∫ s in (0 : ℝ)..1, Real.exp (ξ * frameFunC S.e S.frame.1 (Finsupp.single j t)
        (η (projIcc 0 1 zero_le_one s)))) = J := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [frameFunC_apply, frameFun_single]
    rw [hint] at hW
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hLpos.le hJpos.le)).1 hW
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
  have hI : ∫ x, S.e j x ∂(lengthMeasure η) = ∫ s in (0 : ℝ)..1, φ s :=
    integral_lengthMeasure η (S.frame.1 j)
  rw [hI]
  calc Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w))
      ≤ Real.log ((S.D γ ω).1 (z, w) * J) := Real.log_le_log hDpos h1
    _ = Real.log ((S.D γ ω).1 (z, w)) + Real.log J := Real.log_mul hLpos.ne' hJpos.ne'
    _ ≤ Real.log ((S.D γ ω).1 (z, w)) + (J - 1) := by
        linarith [Real.log_le_sub_one_of_pos hJpos]
    _ ≤ _ := by linarith

/-- **Blueprint Lemma `lem:derivative` (b)**, deterministic form: at a base point `ω` where (S3)
holds, if `t ↦ F(ω + t δ_j)` is differentiable at `0` (`F = log D^γ(·)(z, w)`, `z ≠ w`), then
for every constant-speed `D^γ(ω)`-geodesic `η` from `z` to `w` its derivative at `0` is
`ξ ∫ e_j dν_η`. -/
theorem hasDerivAt_logD_of_isGeod01 {γ : ℝ} {ω : Coord}
    (hweyl : ∀ (v : ℕ →₀ ℝ) (z w : ℂ), ENNReal.ofReal ((S.D γ (shiftBy ω v)).1 (z, w)) =
      weylScale (S.ξ γ) (frameFunC S.e S.frame.1 v) (S.D γ ω) z w)
    {z w : ℂ} (hzw : z ≠ w) {j : ℕ}
    (hdiff : DifferentiableAt ℝ
      (fun t : ℝ => Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w))) 0)
    {η : C(unitInterval, ℂ)} (hη : IsGeod01 (S.D γ ω) z w η) :
    HasDerivAt (fun t : ℝ => Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w)))
      (S.ξ γ * ∫ x, S.e j x ∂(lengthMeasure η)) 0 := by
  set g : ℝ → ℝ := fun t => Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w))
    with hg
  set a := S.ξ γ * ∫ x, S.e j x ∂(lengthMeasure η) with ha
  set c := (S.ξ γ * S.supE j) ^ 2 with hc
  have hg0 : g 0 = Real.log ((S.D γ ω).1 (z, w)) := by
    simp only [hg, GaussLp.shiftBy_single_zero]
  have hM := S.supE_nonneg j
  have hden : 0 < |S.ξ γ| * S.supE j + 1 := by positivity
  -- `t ↦ g t - a t - c t²` has a local maximum at `0`
  have hmax : IsLocalMax (fun t => g t - a * t - c * t ^ 2) 0 := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) (one_div_pos.2 hden))
      fun t ht => ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have ht' : |S.ξ γ * t| * S.supE j ≤ 1 := by
      rw [abs_mul]
      calc |S.ξ γ| * |t| * S.supE j = (|S.ξ γ| * S.supE j) * |t| := by ring
        _ ≤ (|S.ξ γ| * S.supE j + 1) * |t| :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (abs_nonneg t)
        _ ≤ (|S.ξ γ| * S.supE j + 1) * (1 / (|S.ξ γ| * S.supE j + 1)) :=
            mul_le_mul_of_nonneg_left ht.le hden.le
        _ = 1 := by field_simp
    have hle := S.logD_shiftBy_single_le hweyl hzw j hη ht'
    have hct : (S.ξ γ * t * S.supE j) ^ 2 = c * t ^ 2 := by rw [hc]; ring
    have hat : S.ξ γ * t * ∫ x, S.e j x ∂(lengthMeasure η) = a * t := by rw [ha]; ring
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
  have hd : deriv g 0 = a := by linarith
  rw [← hd]
  exact hdiff.hasDerivAt

/-- **Blueprint Lemma `lem:derivative` (b).** For `0 < γ < 2` and `z ≠ w`, almost surely: for every
`j`, `t ↦ log D^γ(ω + t δ_j)(z, w)` is differentiable at `0`, and for every constant-speed
`D^γ(ω)`-geodesic `η` from `z` to `w` its derivative at `0` is `ξ ∫ e_j dν_η`. -/
theorem ae_hasDerivAt_logD {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {z w : ℂ} (hzw : z ≠ w) :
    ∀ᵐ ω ∂stdP, ∀ j : ℕ,
      DifferentiableAt ℝ
          (fun t : ℝ => Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w))) 0 ∧
        ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η →
          HasDerivAt (fun t : ℝ => Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w)))
            (S.ξ γ * ∫ x, S.e j x ∂(lengthMeasure η)) 0 := by
  obtain ⟨Ω, hΩm, hΩc, hΩ⟩ := S.good γ hγ hγ2
  have hH : ∀ ω ∈ Ω, ∀ v v' : ℕ →₀ ℝ,
      |Real.log ((S.D γ (shiftBy ω v)).1 (z, w)) - Real.log ((S.D γ (shiftBy ω v')).1 (z, w))| ≤
        ∑ j ∈ v.support ∪ v'.support, S.ξ γ * S.supE j * |v j - v' j| := fun ω hω v v' =>
    S.abs_logD_shiftBy_sub_le (S.ξ_pos γ hγ hγ2).le (hΩ ω hω).1 (hΩ ω hω).2 hzw v v'
  have hdiff : ∀ j : ℕ, ∀ᵐ ω ∂stdP, DifferentiableAt ℝ
      (fun t : ℝ => Real.log ((S.D γ (shiftBy ω (Finsupp.single j t))).1 (z, w))) 0 :=
    fun j => ae_differentiableAt_coord (F := fun ω => Real.log ((S.D γ ω).1 (z, w)))
      (S.measurable_log_D γ z w) hΩm hΩc hH j
  have hΩae : ∀ᵐ ω ∂stdP, ω ∈ Ω := mem_ae_iff.2 hΩc
  filter_upwards [ae_all_iff.2 hdiff, hΩae] with ω hdω hω j
  exact ⟨hdω j, fun η hη => S.hasDerivAt_logD_of_isGeod01 (hΩ ω hω).2 hzw (hdω j) hη⟩

/-- **Blueprint (eq:derivative).** For `0 < γ < 2` and `z ≠ w`, almost surely, for every `j` and every
constant-speed `D^γ(ω)`-geodesic `η` from `z` to `w`, `∂_j F(ω) = ξ ∫ e_j dν_η`, where
`F = log D^γ(·)(z, w)` and `∂_j` is `coordDeriv`. -/
theorem ae_coordDeriv_logD_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {z w : ℂ} (hzw : z ≠ w) :
    ∀ᵐ ω ∂stdP, ∀ j : ℕ, ∀ η : C(unitInterval, ℂ), IsGeod01 (S.D γ ω) z w η →
      coordDeriv (fun ω => Real.log ((S.D γ ω).1 (z, w))) j ω =
        S.ξ γ * ∫ x, S.e j x ∂(lengthMeasure η) := by
  filter_upwards [S.ae_hasDerivAt_logD hγ hγ2 hzw] with ω hω j η hη
  exact ((hω j).2 η hη).deriv

/-! ## Compatibility names (cleanup W15) -/

alias measurable_logD := measurable_log_D

end Setup

end GaussianLQG

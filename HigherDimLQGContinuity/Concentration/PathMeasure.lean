import HigherDimLQGMetric.Select.GeodRel
import HigherDimLQGMetric.Metric.WeylCompose
import LQGMetric.Metric.Geodesic

/-!
# Path measures of constant-speed geodesics on `ℝ^d` (packet N4)

Blueprint Part C, Definition `c:def-pathmeasure` and the deterministic tools behind Lemmas `c:lem-confine`,
`c:lem-shiftlip`, `c:lem-deriv` (NA4 A1 Steps 2–4). These are the `ℝ^d` ports of GaussianLQG's planar tools
(`GaussianLQG.lengthMeasure`, `lengthMeasure_ball_le_of_isGeod01`, `weylScale_le_of_isGeod01` in
`Metric/Geodesic.lean`, `abs_log_weylScale_sub_le` in `Metric/Weyl.lean`), for HDLM's continuous metrics
`ContMetric d` and constant-speed geodesics `IsConstSpeedGeod` (`HigherDimLQGMetric.Select.GeodRel`).

* `pathMeasure η = η_* Leb|_{[0,1]}` is a probability measure carried by the range of `η`
  (`isProbabilityMeasure_pathMeasure`, `pathMeasure_compl_range`), and `∫ f dν_η = ∫_0^1 f(η t) dt` for continuous
  `f` (`integral_pathMeasure`).
* First/last visits: for a constant-speed geodesic `η` from `z` to `w` with `L = D(z, w) > 0` and a closed `F`
  meeting `η([0,1])`, `ν_η(F) ≤ tmax - tmin = D(η tmin, η tmax)/L` (`exists_pathMeasure_le_of_isConstSpeedGeod`);
  consequently, under a `σ`-Hölder bound `D(x, y) ≤ H |x - y|^σ` (`|x - y| ≤ 1`) on a set containing the range,
  `ν_η(B̄_r(u)) ≤ H (2r)^σ / L` for `0 < r ≤ 1/2` (`pathMeasure_closedBall_le_of_isConstSpeedGeod`).
* Weyl scaling along a geodesic: `(e^{ξ f}·D)(z, w) ≤ L ∫_0^1 e^{ξ f(η t)} dt` (`weylScale_le_of_isConstSpeedGeod`).
* Log-Lipschitz comparison of Weyl distances (`abs_log_weylScale_sub_le_of_isLength`): for a length metric and
  bounded continuous `f, g` with `|f - g| ≤ c`, `|log (e^{ξ f}·D)(z,w) - log (e^{ξ g}·D)(z,w)| ≤ ξ c` (`z ≠ w`).

Proofs as in GaussianLQG (blueprint `lem:geodesic-props`, `lem:weyl-compare`): first and last visit times exist by
compactness; the reparametrization `τ ↦ η(τ/L)` is admissible in the definition of `weylScale`; ratio bounds come
from HDLM's `weylScale_le_exp_mul`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ## The path measure -/

/-- The path measure `ν_η = η_* Leb|_{[0,1]}` of a path `η : [0,1] → ℝ^d` (blueprint `c:def-pathmeasure`). -/
def pathMeasure (η : C(unitInterval, Rd d)) : Measure (Rd d) :=
  (volume.restrict (Icc (0 : ℝ) 1)).map fun t => η (projIcc 0 1 zero_le_one t)

/-- The parametrization `t ↦ η(projIcc t)` of a path on `ℝ` is continuous. -/
theorem continuous_pathParam (η : C(unitInterval, Rd d)) :
    Continuous fun t : ℝ => η (projIcc 0 1 zero_le_one t) :=
  η.continuous.comp continuous_projIcc

/-- The path measure is a probability measure. -/
instance isProbabilityMeasure_pathMeasure (η : C(unitInterval, Rd d)) :
    IsProbabilityMeasure (pathMeasure η) := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩
  unfold pathMeasure
  infer_instance

/-- `ν_η(F) = Leb{t ∈ [0,1] : η t ∈ F}` for measurable `F`. -/
theorem pathMeasure_apply (η : C(unitInterval, Rd d)) {F : Set (Rd d)} (hF : MeasurableSet F) :
    pathMeasure η F = volume ((fun t : ℝ => η (projIcc 0 1 zero_le_one t)) ⁻¹' F ∩ Icc 0 1) := by
  unfold pathMeasure
  rw [Measure.map_apply (continuous_pathParam η).measurable hF,
    Measure.restrict_apply (hF.preimage (continuous_pathParam η).measurable)]

/-- The path measure is carried by the range of the path. -/
theorem pathMeasure_compl_range (η : C(unitInterval, Rd d)) : pathMeasure η (range η)ᶜ = 0 := by
  rw [pathMeasure_apply η (isCompact_range η.continuous).isClosed.measurableSet.compl]
  have : (fun t : ℝ => η (projIcc 0 1 zero_le_one t)) ⁻¹' (range η)ᶜ = ∅ := by
    ext t
    simp only [mem_preimage, mem_compl_iff, mem_range, not_exists, mem_empty_iff_false, iff_false,
      not_forall, not_not]
    exact ⟨_, rfl⟩
  rw [this, empty_inter, measure_empty]

/-- If the range of `η` lies in `K`, then `ν_η(Kᶜ) = 0`. -/
theorem pathMeasure_compl_eq_zero (η : C(unitInterval, Rd d)) {K : Set (Rd d)} (hK : range η ⊆ K) :
    pathMeasure η Kᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 hK) (pathMeasure_compl_range η)

/-- `∫ f dν_η = ∫_0^1 f(η t) dt` for continuous `f`. -/
theorem integral_pathMeasure (η : C(unitInterval, Rd d)) {f : Rd d → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(pathMeasure η) = ∫ t in (0 : ℝ)..1, f (η (projIcc 0 1 zero_le_one t)) := by
  unfold pathMeasure
  rw [integral_map (continuous_pathParam η).aemeasurable hf.aestronglyMeasurable,
    intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-! ## Constant-speed geodesics -/

variable {D : ContMetric d} {z w : Rd d} {η : C(unitInterval, Rd d)}

/-- The reparametrization `τ ↦ η(τ / L)` of a constant-speed geodesic by `D`-length satisfies
`D(P σ, P τ) = |σ - τ|` on `[0, L]`. -/
theorem edist_reparam_of_isConstSpeedGeod (hη : IsConstSpeedGeod D z w η) (hL : 0 < D.1 (z, w)) :
    ∀ s ∈ Icc 0 (D.1 (z, w)), ∀ t ∈ Icc 0 (D.1 (z, w)),
      edist (D.pt (η (projIcc 0 1 zero_le_one (s / D.1 (z, w)))))
        (D.pt (η (projIcc 0 1 zero_le_one (t / D.1 (z, w))))) = edist s t := by
  intro s hs t ht
  set L := D.1 (z, w)
  have hsm : s / L ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hs.1 hL.le, (div_le_one hL).2 hs.2⟩
  have htm : t / L ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1 hL.le, (div_le_one hL).2 ht.2⟩
  rw [projIcc_of_mem _ hsm, projIcc_of_mem _ htm, ContMetric.edist_pt, hη.2.2, edist_dist,
    Real.dist_eq]
  congr 1
  rw [show s / L - t / L = (s - t) / L by ring, abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne']

/-- The reparametrization of a constant-speed geodesic by `D`-length is a unit-speed geodesic curve
on `[0, L]`. -/
theorem isGeodesicCurve_reparam_of_isConstSpeedGeod (hη : IsConstSpeedGeod D z w η)
    (hL : 0 < D.1 (z, w)) :
    IsGeodesicCurve (D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one (τ / D.1 (z, w)))) 0 (D.1 (z, w)) ∧
      HasUnitSpeedOn (D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one (τ / D.1 (z, w))))
        (Icc 0 (D.1 (z, w))) :=
  isGeodesicCurve_of_edist_eq hL.le (edist_reparam_of_isConstSpeedGeod hη hL)

/-- A constant-speed geodesic from `z` to `w` satisfies `D(η s, η t) ≤ D(z, w)`. -/
theorem apply_le_of_isConstSpeedGeod (hη : IsConstSpeedGeod D z w η) (s t : unitInterval) :
    D.1 (η s, η t) ≤ D.1 (z, w) := by
  rw [hη.2.2]
  have habs : |(s : ℝ) - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [s.2.1, s.2.2, t.2.1, t.2.2]
  calc |(s : ℝ) - t| * D.1 (z, w) ≤ 1 * D.1 (z, w) :=
        mul_le_mul_of_nonneg_right habs (ContMetric.nonneg D z w)
    _ = D.1 (z, w) := one_mul _

/-! ## First and last visits; balls -/

/-- **First/last visits** (blueprint `lem:geodesic-props` (b)): if `tmin` and `tmax` are the first and last times
at which the constant-speed geodesic `η` visits the closed set `F`, then
`ν_η(F) ≤ tmax - tmin = D(η tmin, η tmax) / L`. -/
theorem pathMeasure_le_of_isConstSpeedGeod (hη : IsConstSpeedGeod D z w η) (hL : 0 < D.1 (z, w))
    {F : Set (Rd d)} (hF : IsClosed F) {tmin tmax : unitInterval} (hmin : IsLeast (η ⁻¹' F) tmin)
    (hmax : IsGreatest (η ⁻¹' F) tmax) :
    (pathMeasure η F).toReal ≤ (tmax : ℝ) - tmin ∧
      (tmax : ℝ) - tmin = D.1 (η tmin, η tmax) / D.1 (z, w) := by
  have hle : (tmin : ℝ) ≤ tmax := hmin.2 hmax.1
  refine ⟨ENNReal.toReal_le_of_le_ofReal (sub_nonneg.2 hle) ?_, ?_⟩
  · rw [pathMeasure_apply η hF.measurableSet, ← Real.volume_Icc]
    refine measure_mono fun t ht => ?_
    obtain ⟨htF, ht01⟩ := ht
    have hmem : (⟨t, ht01⟩ : unitInterval) ∈ η ⁻¹' F := by
      simpa only [mem_preimage, projIcc_of_mem _ ht01] using htF
    exact ⟨Subtype.coe_le_coe.2 (hmin.2 hmem), Subtype.coe_le_coe.2 (hmax.2 hmem)⟩
  · rw [hη.2.2, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle), mul_div_cancel_right₀ _ hL.ne']

/-- First and last visiting times of a closed set exist. -/
theorem exists_isLeast_isGreatest_preimage_path (η : C(unitInterval, Rd d)) {F : Set (Rd d)}
    (hF : IsClosed F) (hFη : (F ∩ range η).Nonempty) :
    ∃ tmin tmax : unitInterval, IsLeast (η ⁻¹' F) tmin ∧ IsGreatest (η ⁻¹' F) tmax := by
  have hc : IsCompact (η ⁻¹' F) := (hF.preimage η.continuous).isCompact
  have hne : (η ⁻¹' F).Nonempty := by
    obtain ⟨x, hxF, t, rfl⟩ := hFη
    exact ⟨t, hxF⟩
  obtain ⟨tmin, hmin⟩ := hc.exists_isLeast hne
  obtain ⟨tmax, hmax⟩ := hc.exists_isGreatest hne
  exact ⟨tmin, tmax, hmin, hmax⟩

/-- **First/last visits**, existence form: for a closed set `F` meeting `η([0,1])`, the first and last visiting
times exist and `ν_η(F) ≤ tmax - tmin = D(η tmin, η tmax) / L`. -/
theorem exists_pathMeasure_le_of_isConstSpeedGeod (hη : IsConstSpeedGeod D z w η)
    (hL : 0 < D.1 (z, w)) {F : Set (Rd d)} (hF : IsClosed F) (hFη : (F ∩ range η).Nonempty) :
    ∃ tmin tmax : unitInterval, IsLeast (η ⁻¹' F) tmin ∧ IsGreatest (η ⁻¹' F) tmax ∧
      (pathMeasure η F).toReal ≤ (tmax : ℝ) - tmin ∧
      (tmax : ℝ) - tmin = D.1 (η tmin, η tmax) / D.1 (z, w) := by
  obtain ⟨tmin, tmax, hmin, hmax⟩ := exists_isLeast_isGreatest_preimage_path η hF hFη
  exact ⟨tmin, tmax, hmin, hmax, pathMeasure_le_of_isConstSpeedGeod hη hL hF hmin hmax⟩

/-- **Ball bound along a geodesic** (the `ℝ^d` port of GaussianLQG's `lengthMeasure_ball_le_of_isGeod01`, with a
`σ`-Hölder hypothesis on a set `K` containing the range): if `D(x, y) ≤ H |x - y|^σ` for `x, y ∈ K` with
`|x - y| ≤ 1`, then `ν_η(B̄_r(u)) ≤ H (2r)^σ / L` for `0 < r ≤ 1/2`. -/
theorem pathMeasure_closedBall_le_of_isConstSpeedGeod (hη : IsConstSpeedGeod D z w η)
    (hL : 0 < D.1 (z, w)) {K : Set (Rd d)} (hηK : range η ⊆ K) {H σ : ℝ} (hH : 0 ≤ H) (hσ : 0 ≤ σ)
    (hHol : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ 1 → D.1 (x, y) ≤ H * ‖x - y‖ ^ σ) (u : Rd d) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 1 / 2) :
    (pathMeasure η (Metric.closedBall u r)).toReal ≤ H * (2 * r) ^ σ / D.1 (z, w) := by
  have hRHS : 0 ≤ H * (2 * r) ^ σ / D.1 (z, w) := by positivity
  by_cases hne : (Metric.closedBall u r ∩ range η).Nonempty
  · obtain ⟨tmin, tmax, hmin, hmax, hle, heq⟩ :=
      exists_pathMeasure_le_of_isConstSpeedGeod hη hL Metric.isClosed_closedBall hne
    have hdist : ‖η tmin - η tmax‖ ≤ 2 * r := by
      have h1 : dist (η tmin) u ≤ r := hmin.1
      have h2 : dist (η tmax) u ≤ r := hmax.1
      rw [← dist_eq_norm]
      linarith [dist_triangle_right (η tmin) (η tmax) u]
    have hH' := hHol _ (hηK (mem_range_self tmin)) _ (hηK (mem_range_self tmax))
      (hdist.trans (by linarith))
    calc (pathMeasure η (Metric.closedBall u r)).toReal
        ≤ (tmax : ℝ) - tmin := hle
      _ = D.1 (η tmin, η tmax) / D.1 (z, w) := heq
      _ ≤ H * ‖η tmin - η tmax‖ ^ σ / D.1 (z, w) := div_le_div_of_nonneg_right hH' hL.le
      _ ≤ H * (2 * r) ^ σ / D.1 (z, w) := by gcongr
  · have h0 : pathMeasure η (Metric.closedBall u r) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (pathMeasure_compl_range η)
      exact fun hxr => hne ⟨x, hx, hxr⟩
    rw [h0, ENNReal.toReal_zero]
    exact hRHS

/-! ## Weyl scaling along a geodesic -/

/-- **Weyl scaling along a geodesic** (the `ℝ^d` port of GaussianLQG's `weylScale_le_of_isGeod01`; blueprint
`lem:geodesic-props` (d)): `(e^{ξ f}·D)(z, w) ≤ L ∫_0^1 e^{ξ f(η t)} dt`. -/
theorem weylScale_le_of_isConstSpeedGeod (hη : IsConstSpeedGeod D z w η) (ξ : ℝ) (f : C(Rd d, ℝ)) :
    weylScale ξ f D z w ≤ ENNReal.ofReal (D.1 (z, w) *
      ∫ t in (0 : ℝ)..1, Real.exp (ξ * f (η (projIcc 0 1 zero_le_one t)))) := by
  rcases (ContMetric.nonneg D z w).eq_or_lt with hL0 | hL
  · have hzw : z = w := D.eq_of_apply_eq_zero hL0.symm
    subst hzw
    rw [weylScale_self]
    exact bot_le
  obtain ⟨hgeo, hu⟩ := isGeodesicCurve_reparam_of_isConstSpeedGeod hη hL
  have hP0 : η (projIcc 0 1 zero_le_one (0 / D.1 (z, w))) = z := by
    rw [zero_div, projIcc_left]
    exact hη.1
  have hP1 : η (projIcc 0 1 zero_le_one (D.1 (z, w) / D.1 (z, w))) = w := by
    rw [div_self hL.ne', projIcc_right]
    exact hη.2.1
  set G : ℝ → ℝ := fun t => Real.exp (ξ * f (η (projIcc 0 1 zero_le_one t))) with hG
  have hGc : Continuous G := by
    simp only [hG]
    exact Real.continuous_exp.comp
      (continuous_const.mul (f.continuous.comp (continuous_pathParam η)))
  -- the admissible path `τ ↦ η(τ / L)` bounds the Weyl infimum
  have h1 : weylScale ξ f D z w ≤
      ∫⁻ τ in Icc 0 (D.1 (z, w)), ENNReal.ofReal (G (τ / D.1 (z, w))) :=
    weylScale_le hL.le hgeo.2.1 hu hP0 hP1
  -- change of variables `τ = L t`
  have h2 : ∫⁻ τ in Icc 0 (D.1 (z, w)), ENNReal.ofReal (G (τ / D.1 (z, w))) =
      ENNReal.ofReal (D.1 (z, w)) * ∫⁻ t in Icc 0 1, ENNReal.ofReal (G t) := by
    have himg : (fun x => D.1 (z, w) * x) '' Icc 0 1 = Icc 0 (D.1 (z, w)) := by
      rw [image_mul_left_Icc hL.le zero_le_one, mul_zero, mul_one]
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc
      (f' := fun _ => D.1 (z, w))
      (fun x _ => by simpa using ((hasDerivAt_id x).const_mul (D.1 (z, w))).hasDerivWithinAt)
      (fun x _ y _ hxy => mul_left_cancel₀ hL.ne' hxy), abs_of_pos hL,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [mul_div_cancel_left₀ t hL.ne']
  -- the Lebesgue integral of `e^{ξ f(η)}` is the interval integral
  have h3 : ∫⁻ t in Icc 0 1, ENNReal.ofReal (G t) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, G t) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal (hGc.integrableOn_Icc)
        (ae_of_all _ fun t => (Real.exp_pos _).le)]
  rw [h2, h3, ← ENNReal.ofReal_mul hL.le] at h1
  exact h1

/-! ## Log-Lipschitz comparison of Weyl distances -/

/-- One-sided log comparison of Weyl distances: if `ξ f ≤ ξ g + c` everywhere and both Weyl distances are the
positive reals `a`, `b`, then `log a ≤ c + log b`. -/
theorem log_le_add_log_of_weylScale {ξ : ℝ} {f g : C(Rd d, ℝ)} {c a b : ℝ}
    (hfg : ∀ x, ξ * f x ≤ ξ * g x + c) (ha : 0 < a) (hb : 0 < b)
    (hfa : weylScale ξ f D z w = ENNReal.ofReal a) (hgb : weylScale ξ g D z w = ENNReal.ofReal b) :
    Real.log a ≤ c + Real.log b := by
  have hle := weylScale_le_exp_mul (D := D) (z := z) (w := w) hfg
  rw [hfa, hgb, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le hb.le)] at hle
  calc Real.log a ≤ Real.log (Real.exp c * b) := Real.log_le_log ha hle
    _ = c + Real.log b := by rw [Real.log_mul (Real.exp_pos _).ne' hb.ne', Real.log_exp]

/-- **Log-Lipschitz comparison** (the `ℝ^d` port of GaussianLQG's `abs_log_weylScale_sub_le`, blueprint
`lem:weyl-compare` (b), with an explicit bound `c` for `sup |f - g|`): for a continuous length metric `D`,
`ξ ≥ 0`, continuous `f, g` with `|f - g| ≤ c` and `z ≠ w`,
`|log (e^{ξ f}·D)(z, w) - log (e^{ξ g}·D)(z, w)| ≤ ξ c`. -/
theorem abs_log_weylScale_sub_le_of_isLength (hD : D.IsLength) {ξ : ℝ} (hξ : 0 ≤ ξ)
    {f g : C(Rd d, ℝ)} (hf : ∃ M, ∀ x, |f x| ≤ M) (hg : ∃ M, ∀ x, |g x| ≤ M) {c : ℝ}
    (hc : ∀ x, |f x - g x| ≤ c) (hzw : z ≠ w) :
    |Real.log (weylScale ξ f D z w).toReal - Real.log (weylScale ξ g D z w).toReal| ≤ ξ * c := by
  have hpos : ∀ {h : C(Rd d, ℝ)}, (∃ M, ∀ x, |h x| ≤ M) → 0 < (weylScale ξ h D z w).toReal := by
    intro h hh
    obtain ⟨M, hM⟩ := hh
    have hlow := (weylScale_mem_Icc_of_isLength (ξ := ξ) (f := h) (z := z) (w := w) hD
      (a := -(|ξ| * M)) (b := |ξ| * M)
      (fun x => by
        have := abs_le.1 ((abs_mul ξ (h x)).trans_le
          (mul_le_mul_of_nonneg_left (hM x) (abs_nonneg ξ)))
        linarith [this.1])
      (fun x => by
        have := abs_le.1 ((abs_mul ξ (h x)).trans_le
          (mul_le_mul_of_nonneg_left (hM x) (abs_nonneg ξ)))
        linarith [this.2])).1
    have hp : 0 < ENNReal.ofReal (Real.exp (-(|ξ| * M)) * D.1 (z, w)) :=
      ENNReal.ofReal_pos.2 (mul_pos (Real.exp_pos _) (D.apply_pos hzw))
    exact ENNReal.toReal_pos (lt_of_lt_of_le hp hlow).ne' (weylScale_ne_top hD z w)
  have hfpos := hpos hf
  have hgpos := hpos hg
  have h1 : Real.log (weylScale ξ f D z w).toReal ≤ ξ * c + Real.log (weylScale ξ g D z w).toReal :=
    log_le_add_log_of_weylScale (fun x => by
      have := (le_abs_self _).trans (hc x)
      nlinarith) hfpos hgpos (ENNReal.ofReal_toReal (weylScale_ne_top hD z w)).symm
      (ENNReal.ofReal_toReal (weylScale_ne_top hD z w)).symm
  have h2 : Real.log (weylScale ξ g D z w).toReal ≤ ξ * c + Real.log (weylScale ξ f D z w).toReal :=
    log_le_add_log_of_weylScale (fun x => by
      have := (neg_le_abs _).trans (hc x)
      nlinarith) hgpos hfpos (ENNReal.ofReal_toReal (weylScale_ne_top hD z w)).symm
      (ENNReal.ofReal_toReal (weylScale_ne_top hD z w)).symm
  rw [abs_sub_le_iff]
  constructor <;> linarith

end HigherDimLQGContinuity

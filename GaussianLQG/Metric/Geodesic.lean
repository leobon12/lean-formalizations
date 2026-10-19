import GaussianLQG.Core.Defs
import LQGMetric.Metric.WeylCont
import LQGMetric.Metric.InternalLimitC

/-!
# Constant-speed geodesics (blueprint Lemma `lem:geodesic-props`)

Let `D` be a continuous metric on `ℂ` (`LQGMetric.ContMetric`) and let `η : [0,1] → ℂ` be a
constant-speed `D`-geodesic from `z` to `w` (`LQGMetric.Blueprint.IsGeod01 D z w η`:
`D(η s, η t) = |t - s| L` with `L = D(z, w)`). Blueprint Lemma `lem:geodesic-props`:

* (a) the length measure `ν_η = η_* Leb|_{[0,1]}` (`GaussianLQG.lengthMeasure`) is a probability
  measure supported on `η([0,1])` (`isProbabilityMeasure_lengthMeasure`,
  `lengthMeasure_compl_range`); along `η`, `len_D(η|_{[s,t]}) = (t - s) L`
  (`curveLength_eq_of_isGeod01`), and `η|_{[s,t]}` is a constant-speed geodesic between its
  endpoints (`isGeod01_restrictPath`);
* (b) for a closed set `F` meeting `η([0,1])`, with `tmin = min η⁻¹(F)` and `tmax = max η⁻¹(F)`,
  `ν_η(F) ≤ tmax - tmin = D(η tmin, η tmax) / L` (`lengthMeasure_le_of_isGeod01`,
  `exists_lengthMeasure_le_of_isGeod01`); consequently
  `ν_η(B_r(u)) ≤ A(K) (2r)^{1/2} / L` whenever `η([0,1]) ⊆ K` and the Hölder constant
  `A(K) = holderConst D K` is finite (`lengthMeasure_ball_le_of_isGeod01`);
* (c) annulus crossing: if `|z| ≤ R` and `η([0,1]) ⊄ B_{2R}(0)` then
  `L ≥ D(∂B_R(0), ∂B_{2R}(0))` (`exists_crossing_of_isGeod01`, `setDist_sphere_le_of_isGeod01`,
  `sInf_crossing_le_of_isGeod01`);
* (d) `(e^{ξ f}·D)(z, w) ≤ L ∫_0^1 e^{ξ f(η s)} ds` for continuous `f`
  (`weylScale_le_of_isGeod01`), where `e^{ξ f}·D` is `LQGMetric.weylScale`.

The proofs follow the blueprint: (b) `η⁻¹(F) ⊆ [tmin, tmax]`; (c) the intermediate value theorem;
(d) the reparametrization `τ ↦ η(τ / L)` of `η` by `D`-length is an admissible path in the
definition of `weylScale`, and the change of variables `τ = L t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GaussianLQG

open LQGMetric LQGMetric.MetricGeometry LQGMetric.Blueprint

variable {D : ContMetric} {z w : ℂ} {η : C(unitInterval, ℂ)}

/-- The parametrization `t ↦ η(projIcc t)` of `η` on `ℝ` (constant outside `[0,1]`) is
continuous. -/
theorem continuous_comp_projIcc (η : C(unitInterval, ℂ)) :
    Continuous fun t : ℝ => η (projIcc 0 1 zero_le_one t) :=
  η.continuous.comp continuous_projIcc

/-! ## (a) The length measure -/

/-- The length measure of a path is a probability measure (blueprint `lem:geodesic-props` (a)). -/
instance isProbabilityMeasure_lengthMeasure (η : C(unitInterval, ℂ)) :
    IsProbabilityMeasure (lengthMeasure η) := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩
  unfold lengthMeasure
  infer_instance

/-- `ν_η(F) = Leb{t ∈ [0,1] : η t ∈ F}` for measurable `F`. -/
theorem lengthMeasure_apply (η : C(unitInterval, ℂ)) {F : Set ℂ} (hF : MeasurableSet F) :
    lengthMeasure η F =
      volume ((fun t : ℝ => η (projIcc 0 1 zero_le_one t)) ⁻¹' F ∩ Icc 0 1) := by
  unfold lengthMeasure
  rw [Measure.map_apply (continuous_comp_projIcc η).measurable hF,
    Measure.restrict_apply (hF.preimage (continuous_comp_projIcc η).measurable)]

/-- The length measure is supported on the range of the path (blueprint `lem:geodesic-props`
(a)). -/
theorem lengthMeasure_compl_range (η : C(unitInterval, ℂ)) : lengthMeasure η (range η)ᶜ = 0 := by
  rw [lengthMeasure_apply η (isCompact_range η.continuous).isClosed.measurableSet.compl]
  have : (fun t : ℝ => η (projIcc 0 1 zero_le_one t)) ⁻¹' (range η)ᶜ = ∅ := by
    ext t
    simp only [mem_preimage, mem_compl_iff, mem_range, not_exists, mem_empty_iff_false,
      iff_false, not_forall, not_not]
    exact ⟨_, rfl⟩
  rw [this, empty_inter, measure_empty]

/-! ## Constant-speed geodesics -/

/-- The reparametrization `τ ↦ η(τ / L)` of a constant-speed geodesic by `D`-length satisfies
`D(P σ, P τ) = |σ - τ|` on `[0, L]`. -/
theorem edist_reparam_of_isGeod01 (hη : IsGeod01 D z w η) (hL : 0 < D.1 (z, w)) :
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
  rw [show t / L - s / L = (t - s) / L by ring, abs_div, abs_of_pos hL,
    div_mul_cancel₀ _ hL.ne', abs_sub_comm]

/-- The reparametrization of a constant-speed geodesic by `D`-length is a unit-speed geodesic
curve on `[0, L]` from `z` to `w`. -/
theorem isGeodesicCurve_reparam_of_isGeod01 (hη : IsGeod01 D z w η) (hL : 0 < D.1 (z, w)) :
    IsGeodesicCurve (D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one (τ / D.1 (z, w)))) 0 (D.1 (z, w)) ∧
      HasUnitSpeedOn (D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one (τ / D.1 (z, w))))
        (Icc 0 (D.1 (z, w))) :=
  isGeodesicCurve_of_edist_eq hL.le (edist_reparam_of_isGeod01 hη hL)

/-- Along a constant-speed geodesic, `len_D(η|_{[s,t]}) = (t - s) L` (blueprint
`lem:geodesic-props` (a)). -/
theorem curveLength_eq_of_isGeod01 (hη : IsGeod01 D z w η) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1) :
    curveLength (D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one τ)) s t =
      ENNReal.ofReal ((t - s) * D.1 (z, w)) := by
  rcases (ContMetric.nonneg D z w).eq_or_lt with hL0 | hL
  · -- `L = 0`: the path is constant
    have hconst : ∀ τ ∈ Icc s t, (D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one τ)) τ = D.pt z := by
      intro τ _
      have h1 := hη.2.2 0 (projIcc 0 1 zero_le_one τ)
      rw [hη.1, ← hL0, mul_zero] at h1
      exact (D.2.eq_of_eq_zero _ _ h1).symm
    rw [← hL0, mul_zero, ENNReal.ofReal_zero]
    exact eVariationOn.constant_on (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hconst a ha, hconst b hb])
  · obtain ⟨-, hu⟩ := isGeodesicCurve_reparam_of_isGeod01 hη hL
    have hmono : MonotoneOn (fun τ : ℝ => D.1 (z, w) * τ) (Icc s t) :=
      fun a _ b _ hab => mul_le_mul_of_nonneg_left hab hL.le
    have h1 := curveLength_comp_of_continuousOn_monotoneOn
      (D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one (τ / D.1 (z, w)))) hst (by fun_prop) hmono
    have hcomp : ((D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one (τ / D.1 (z, w)))) ∘
        fun τ : ℝ => D.1 (z, w) * τ) = D.pt ∘ fun τ => η (projIcc 0 1 zero_le_one τ) := by
      funext τ
      simp only [Function.comp_apply]
      rw [mul_div_cancel_left₀ τ hL.ne']
    rw [hcomp] at h1
    rw [h1, curveLength_of_hasUnitSpeedOn hu ⟨by positivity, by nlinarith⟩
      ⟨by nlinarith, by nlinarith⟩]
    congr 1
    ring

/-- The restriction of a path `η` to `[s, t]`, reparametrized linearly on `[0, 1]`. -/
def restrictPath (η : C(unitInterval, ℂ)) (s t : unitInterval) : C(unitInterval, ℂ) :=
  ⟨fun u => η (projIcc 0 1 zero_le_one ((s : ℝ) + (u : ℝ) * ((t : ℝ) - s))),
    η.continuous.comp (continuous_projIcc.comp (continuous_const.add
      (continuous_subtype_val.mul continuous_const)))⟩

/-- Restrictions of a constant-speed geodesic are constant-speed geodesics between their
endpoints (blueprint `lem:geodesic-props` (a)). -/
theorem isGeod01_restrictPath (hη : IsGeod01 D z w η) {s t : unitInterval} (hst : (s : ℝ) ≤ t) :
    IsGeod01 D (η s) (η t) (restrictPath η s t) := by
  have hmem : ∀ u : unitInterval, (s : ℝ) + u * ((t : ℝ) - s) ∈ Icc (0 : ℝ) 1 := fun u =>
    ⟨by nlinarith [s.2.1, u.2.1, u.2.2], by nlinarith [t.2.2, u.2.1, u.2.2]⟩
  refine ⟨?_, ?_, fun u v => ?_⟩
  · show η (projIcc 0 1 zero_le_one ((s : ℝ) + ((0 : unitInterval) : ℝ) * ((t : ℝ) - s))) = η s
    rw [Set.Icc.coe_zero, zero_mul, add_zero, projIcc_val]
  · show η (projIcc 0 1 zero_le_one ((s : ℝ) + ((1 : unitInterval) : ℝ) * ((t : ℝ) - s))) = η t
    rw [Set.Icc.coe_one, one_mul, add_sub_cancel, projIcc_val]
  · show D.1 (η (projIcc 0 1 zero_le_one ((s : ℝ) + (u : ℝ) * ((t : ℝ) - s))),
      η (projIcc 0 1 zero_le_one ((s : ℝ) + (v : ℝ) * ((t : ℝ) - s)))) = _
    rw [projIcc_of_mem _ (hmem u), projIcc_of_mem _ (hmem v), hη.2.2, hη.2.2 s t]
    have e : (s : ℝ) + v * ((t : ℝ) - s) - (s + u * ((t : ℝ) - s)) =
        ((v : ℝ) - u) * ((t : ℝ) - s) := by ring
    rw [e, abs_mul, abs_of_nonneg (sub_nonneg.2 hst)]
    ring

/-! ## (b) Mass of closed sets and of balls -/

/-- **Blueprint `lem:geodesic-props` (b).** If `tmin` and `tmax` are the first and last times at
which the constant-speed geodesic `η` visits the closed set `F`, then
`ν_η(F) ≤ tmax - tmin = D(η tmin, η tmax) / L`. -/
theorem lengthMeasure_le_of_isGeod01 (hη : IsGeod01 D z w η) (hL : 0 < D.1 (z, w)) {F : Set ℂ}
    (hF : IsClosed F) {tmin tmax : unitInterval} (hmin : IsLeast (η ⁻¹' F) tmin)
    (hmax : IsGreatest (η ⁻¹' F) tmax) :
    (lengthMeasure η F).toReal ≤ (tmax : ℝ) - tmin ∧
      (tmax : ℝ) - tmin = D.1 (η tmin, η tmax) / D.1 (z, w) := by
  have hle : (tmin : ℝ) ≤ tmax := hmin.2 hmax.1
  refine ⟨ENNReal.toReal_le_of_le_ofReal (sub_nonneg.2 hle) ?_, ?_⟩
  · rw [lengthMeasure_apply η hF.measurableSet, ← Real.volume_Icc]
    refine measure_mono fun t ht => ?_
    obtain ⟨htF, ht01⟩ := ht
    have hmem : (⟨t, ht01⟩ : unitInterval) ∈ η ⁻¹' F := by
      simpa only [mem_preimage, projIcc_of_mem _ ht01] using htF
    exact ⟨Subtype.coe_le_coe.2 (hmin.2 hmem), Subtype.coe_le_coe.2 (hmax.2 hmem)⟩
  · rw [hη.2.2, abs_of_nonneg (sub_nonneg.2 hle), mul_div_cancel_right₀ _ hL.ne']

/-- First and last visiting times of a closed set exist. -/
theorem exists_isLeast_isGreatest_preimage (η : C(unitInterval, ℂ)) {F : Set ℂ}
    (hF : IsClosed F) (hFη : (F ∩ range η).Nonempty) :
    ∃ tmin tmax : unitInterval, IsLeast (η ⁻¹' F) tmin ∧ IsGreatest (η ⁻¹' F) tmax := by
  have hc : IsCompact (η ⁻¹' F) := (hF.preimage η.continuous).isCompact
  have hne : (η ⁻¹' F).Nonempty := by
    obtain ⟨x, hxF, t, rfl⟩ := hFη
    exact ⟨t, hxF⟩
  obtain ⟨tmin, hmin⟩ := hc.exists_isLeast hne
  obtain ⟨tmax, hmax⟩ := hc.exists_isGreatest hne
  exact ⟨tmin, tmax, hmin, hmax⟩

/-- **Blueprint `lem:geodesic-props` (b)**, existence form: for a closed set `F` meeting
`η([0,1])`, `tmin = min η⁻¹(F)` and `tmax = max η⁻¹(F)` exist and
`ν_η(F) ≤ tmax - tmin = D(η tmin, η tmax) / L`. -/
theorem exists_lengthMeasure_le_of_isGeod01 (hη : IsGeod01 D z w η) (hL : 0 < D.1 (z, w))
    {F : Set ℂ} (hF : IsClosed F) (hFη : (F ∩ range η).Nonempty) :
    ∃ tmin tmax : unitInterval, IsLeast (η ⁻¹' F) tmin ∧ IsGreatest (η ⁻¹' F) tmax ∧
      (lengthMeasure η F).toReal ≤ (tmax : ℝ) - tmin ∧
      (tmax : ℝ) - tmin = D.1 (η tmin, η tmax) / D.1 (z, w) := by
  obtain ⟨tmin, tmax, hmin, hmax⟩ := exists_isLeast_isGreatest_preimage η hF hFη
  exact ⟨tmin, tmax, hmin, hmax, lengthMeasure_le_of_isGeod01 hη hL hF hmin hmax⟩

/-- The Hölder bound `D(x, y) ≤ A(K) |x - y|^{1/2}` on `K`, when `A(K) = holderConst D K` is
finite (blueprint (1.10)). -/
theorem dist_le_holderConst_mul (D : ContMetric) {K : Set ℂ} (hK : holderConst D.1 K ≠ ⊤)
    {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) :
    D.1 (x, y) ≤ (holderConst D.1 K).toReal * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [D.2.self_eq_zero, sub_self, norm_zero, Real.zero_rpow (by norm_num), mul_zero]
  have hpos : 0 < ‖x - y‖ ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) _
  have h1 : ENNReal.ofReal (D.1 (x, y) / ‖x - y‖ ^ (1 / 2 : ℝ)) ≤ holderConst D.1 K := by
    unfold holderConst
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  rw [ENNReal.ofReal_le_iff_le_toReal hK, div_le_iff₀ hpos] at h1
  exact h1

/-- **Consequence of blueprint `lem:geodesic-props` (b)**: if `η([0,1]) ⊆ K` and the Hölder
constant `A(K)` is finite, then `ν_η(B_r(u)) ≤ A(K) (2r)^{1/2} / L` for every `u` and `r > 0`. -/
theorem lengthMeasure_ball_le_of_isGeod01 (hη : IsGeod01 D z w η) (hL : 0 < D.1 (z, w))
    {K : Set ℂ} (hηK : range η ⊆ K) (hK : holderConst D.1 K ≠ ⊤) (u : ℂ) {r : ℝ}
    (hr : 0 < r) :
    (lengthMeasure η (Metric.ball u r)).toReal ≤
      (holderConst D.1 K).toReal * (2 * r) ^ (1 / 2 : ℝ) / D.1 (z, w) := by
  have hRHS : 0 ≤ (holderConst D.1 K).toReal * (2 * r) ^ (1 / 2 : ℝ) / D.1 (z, w) := by
    positivity
  have hmono : (lengthMeasure η (Metric.ball u r)).toReal ≤
      (lengthMeasure η (Metric.closedBall u r)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Metric.ball_subset_closedBall)
  by_cases hne : (Metric.closedBall u r ∩ range η).Nonempty
  · obtain ⟨tmin, tmax, hmin, hmax, hle, heq⟩ :=
      exists_lengthMeasure_le_of_isGeod01 hη hL Metric.isClosed_closedBall hne
    have hdist : ‖η tmin - η tmax‖ ≤ 2 * r := by
      have h1 : dist (η tmin) u ≤ r := hmin.1
      have h2 : dist (η tmax) u ≤ r := hmax.1
      rw [← Complex.dist_eq]
      linarith [dist_triangle_right (η tmin) (η tmax) u]
    have hH := dist_le_holderConst_mul D hK (hηK (mem_range_self tmin)) (hηK (mem_range_self tmax))
    calc (lengthMeasure η (Metric.ball u r)).toReal
        ≤ (lengthMeasure η (Metric.closedBall u r)).toReal := hmono
      _ ≤ (tmax : ℝ) - tmin := hle
      _ = D.1 (η tmin, η tmax) / D.1 (z, w) := heq
      _ ≤ (holderConst D.1 K).toReal * ‖η tmin - η tmax‖ ^ (1 / 2 : ℝ) / D.1 (z, w) :=
          div_le_div_of_nonneg_right hH hL.le
      _ ≤ (holderConst D.1 K).toReal * (2 * r) ^ (1 / 2 : ℝ) / D.1 (z, w) := by
          gcongr
  · have h0 : lengthMeasure η (Metric.closedBall u r) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (lengthMeasure_compl_range η)
      exact fun hxr => hne ⟨x, hx, hxr⟩
    rw [h0, ENNReal.toReal_zero] at hmono
    exact hmono.trans hRHS

/-! ## (c) Annulus crossing -/

/-- **Blueprint `lem:geodesic-props` (c)**: if `|z| ≤ R` and the geodesic leaves `B_{2R}(0)`,
then there are `x, y` with `|x| = R`, `|y| = 2R` and `D(x, y) ≤ L`. -/
theorem exists_crossing_of_isGeod01 (hη : IsGeod01 D z w η) {R : ℝ} (hz : ‖z‖ ≤ R)
    (hout : ¬ range η ⊆ Metric.ball 0 (2 * R)) :
    ∃ x y : ℂ, ‖x‖ = R ∧ ‖y‖ = 2 * R ∧ D.1 (x, y) ≤ D.1 (z, w) := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : unitInterval, 2 * R ≤ ‖η t₁‖ := by
    by_contra hcon
    push Not at hcon
    exact hout fun x ⟨t, ht⟩ => by
      rw [← ht, mem_ball_zero_iff]
      exact hcon t
  have hg : Continuous fun t : unitInterval => ‖η t‖ := continuous_norm.comp η.continuous
  have hIVT := intermediate_value_univ 0 t₁ hg
  have h0 : ‖η 0‖ = ‖z‖ := by rw [hη.1]
  obtain ⟨s, hs⟩ := hIVT ⟨by simp only [h0]; exact hz, by linarith⟩
  obtain ⟨t, ht⟩ := hIVT ⟨by simp only [h0]; linarith, ht₁⟩
  refine ⟨η s, η t, hs, ht, ?_⟩
  rw [hη.2.2]
  have habs : |(t : ℝ) - s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [s.2.1, s.2.2, t.2.1, t.2.2]
  calc |(t : ℝ) - s| * D.1 (z, w) ≤ 1 * D.1 (z, w) :=
        mul_le_mul_of_nonneg_right habs (ContMetric.nonneg D z w)
    _ = D.1 (z, w) := one_mul _

/-- **Blueprint `lem:geodesic-props` (c)**, with GM's set distance `D(A, B)`:
`D(∂B_R(0), ∂B_{2R}(0)) ≤ L`. -/
theorem setDist_sphere_le_of_isGeod01 (hη : IsGeod01 D z w η) {R : ℝ} (hz : ‖z‖ ≤ R)
    (hout : ¬ range η ⊆ Metric.ball 0 (2 * R)) :
    setDist D (Metric.sphere 0 R) (Metric.sphere 0 (2 * R)) ≤ ENNReal.ofReal (D.1 (z, w)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_crossing_of_isGeod01 hη hz hout
  refine (setEDist_le_edist (mem_image_of_mem D.pt (mem_sphere_zero_iff_norm.2 hx))
    (mem_image_of_mem D.pt (mem_sphere_zero_iff_norm.2 hy))).trans ?_
  rw [ContMetric.edist_pt]
  exact ENNReal.ofReal_le_ofReal hxy

/-- **Blueprint `lem:geodesic-props` (c)**, real infimum form:
`inf {D(x, y) : |x| = R, |y| = 2R} ≤ L`. -/
theorem sInf_crossing_le_of_isGeod01 (hη : IsGeod01 D z w η) {R : ℝ} (hz : ‖z‖ ≤ R)
    (hout : ¬ range η ⊆ Metric.ball 0 (2 * R)) :
    sInf {d : ℝ | ∃ x y : ℂ, ‖x‖ = R ∧ ‖y‖ = 2 * R ∧ D.1 (x, y) = d} ≤ D.1 (z, w) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_crossing_of_isGeod01 hη hz hout
  have hbdd : BddBelow {d : ℝ | ∃ x y : ℂ, ‖x‖ = R ∧ ‖y‖ = 2 * R ∧ D.1 (x, y) = d} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨a, b, -, -, rfl⟩
    exact ContMetric.nonneg D a b
  exact (csInf_le hbdd ⟨x, y, hx, hy, rfl⟩).trans hxy

/-! ## (d) Weyl scaling along a geodesic -/

/-- **Blueprint `lem:geodesic-props` (d)** (and `lem:weyl-compare` (c)): along a constant-speed
geodesic, `(e^{ξ f}·D)(z, w) ≤ L ∫_0^1 e^{ξ f(η s)} ds`. -/
theorem weylScale_le_of_isGeod01 (hη : IsGeod01 D z w η) (ξ : ℝ) (f : C(ℂ, ℝ)) :
    weylScale ξ f D z w ≤ ENNReal.ofReal (D.1 (z, w) *
      ∫ t in (0 : ℝ)..1, Real.exp (ξ * f (η (projIcc 0 1 zero_le_one t)))) := by
  rcases (ContMetric.nonneg D z w).eq_or_lt with hL0 | hL
  · have hzw : z = w := D.2.eq_of_eq_zero z w hL0.symm
    subst hzw
    rw [weylScale_self]
    exact bot_le
  obtain ⟨hgeo, hu⟩ := isGeodesicCurve_reparam_of_isGeod01 hη hL
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
      (continuous_const.mul (f.continuous.comp (continuous_comp_projIcc η)))
  -- the admissible path `τ ↦ η(τ / L)` bounds the Weyl infimum
  have h1 : weylScale ξ f D z w ≤
      ∫⁻ τ in Icc 0 (D.1 (z, w)), ENNReal.ofReal (G (τ / D.1 (z, w))) := by
    rw [← weylScaleOn_univ]
    exact weylScaleOn_le hL.le hgeo.2.1 hu hP0 hP1 fun _ _ => mem_univ _
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

end GaussianLQG

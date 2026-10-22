import HigherDimLQGMetric.Config.Family
import HigherDimLQGMetric.Coord.UniformRealization

/-!
# Internal coordinates of a length metric

The real internal distance on a connected open domain is a genuine metric
which induces the original topology. This is the deterministic fact used for
the original configurations of MA1 A4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem config_internalC_isMetricFun (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsMetricFun (internalC D hD hU hUc) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change (D.internal U x.1 x.1).toReal = 0
    rw [D.internal_self x.2, ENNReal.toReal_zero]
  · intro x y hzero
    apply Subtype.ext
    apply D.eq_of_apply_eq_zero
    have hle := D.ofReal_le_internal U x.1 y.1
    have hfin := D.internal_ne_top_of_isPreconnected hD hU hUc x.2 y.2
    have hle' : D.1 (x.1, y.1) ≤ (D.internal U x.1 y.1).toReal := by
      simpa only [ENNReal.toReal_ofReal (D.nonneg x.1 y.1)] using
        (ENNReal.toReal_mono hfin hle)
    change (D.internal U x.1 y.1).toReal = 0 at hzero
    exact le_antisymm (hle'.trans_eq hzero) (D.nonneg _ _)
  · intro x y
    change (D.internal U x.1 y.1).toReal = (D.internal U y.1 x.1).toReal
    rw [D.internal_comm]
  · intro x y z
    exact internalC_triangle D hD hU hUc x y z

theorem config_internalC_pt_continuous (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    Continuous (MetricFunSpace.pt (internalC D hD hU hUc)
      (config_internalC_isMetricFun D hD hU hUc)) := by
  let ρ := internalC D hD hU hUc
  let hρ := config_internalC_isMetricFun D hD hU hUc
  refine Metric.continuous_iff.2 fun x ε hε => ?_
  have hc : Continuous fun y : U => ρ (y, x) :=
    ρ.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc x ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h' := h y hy
  rw [show ρ (x, x) = 0 from hρ.self_eq_zero x, Real.dist_eq, sub_zero] at h'
  change ρ (y, x) < ε
  exact (le_abs_self _).trans_lt h'

theorem config_internalC_val_continuous (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    Continuous (LQGMetric.metricFunSpaceVal (internalC D hD hU hUc)
      (config_internalC_isMetricFun D hD hU hUc)) := by
  let ρ := internalC D hD hU hUc
  let hρ := config_internalC_isMetricFun D hD hU hUc
  have hle (x y : U) : D.1 (x.1, y.1) ≤ ρ (x, y) := by
    have hfin := D.internal_ne_top_of_isPreconnected hD hU hUc x.2 y.2
    have h := ENNReal.toReal_mono hfin (D.ofReal_le_internal U x.1 y.1)
    change D.1 (x.1, y.1) ≤ (D.internal U x.1 y.1).toReal
    simpa only [ENNReal.toReal_ofReal (D.nonneg x.1 y.1)] using h
  have hLip : LipschitzWith 1
      (fun x : MetricFunSpace ρ hρ => D.pt (x : U).1) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    change D.1 ((x : U).1, (y : U).1) ≤ 1 * ρ ((x : U), (y : U))
    simpa only [one_mul] using hle (x : U) (y : U)
  have hval : Continuous (fun x : MetricFunSpace ρ hρ => ((x : U).1 : Rd d)) :=
    D.continuous_unpt.comp hLip.continuous
  exact hval.subtype_mk _

theorem config_internalC_isCoordinate (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsCoordinate (internalC D hD hU hUc) :=
  ⟨config_internalC_isMetricFun D hD hU hUc,
    config_internalC_pt_continuous D hD hU hUc,
    config_internalC_val_continuous D hD hU hUc⟩

theorem config_internalC_intrinsic_eq (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) (u v : U) :
    D.internal U u.1 v.1 =
      internalEDist Set.univ
        (MetricFunSpace.pt (internalC D hD hU hUc)
          (config_internalC_isMetricFun D hD hU hUc) u)
        (MetricFunSpace.pt (internalC D hD hU hUc)
          (config_internalC_isMetricFun D hD hU hUc) v) := by
  apply internal_eq_of_tendsto_internal_on (fun _ : ℕ => D) D
    (fun _ => hD) ?_ hU (internalC D hD hU hUc)
    (config_internalC_isMetricFun D hD hU hUc)
    (config_internalC_pt_continuous D hD hU hUc)
    (config_internalC_val_continuous D hD hU hUc) ?_ u v
  · intro R _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with n p hp
    simpa using hε
  · intro a b
    exact tendsto_const_nhds

theorem config_internalC_isLengthCoordinate (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsLengthCoordinate (internalC D hD hU hUc) := by
  let E := internalC D hD hU hUc
  let hE := config_internalC_isMetricFun D hD hU hUc
  have hlen : IsLengthMetricFun E hE := by
    have hIntrinsic : ∀ x y : MetricFunSpace E hE,
        internalEDist Set.univ x y = edist x y := by
      intro x y
      let u : U := x
      let v : U := y
      have hEq := config_internalC_intrinsic_eq D hD hU hUc u v
      have hfin := D.internal_ne_top_of_isPreconnected hD hU hUc u.2 v.2
      have hed : edist x y = D.internal U u.1 v.1 := by
        rw [edist_dist]
        change ENNReal.ofReal ((D.internal U u.1 v.1).toReal) = _
        exact ENNReal.ofReal_toReal hfin
      exact hEq.symm.trans hed.symm
    intro x y ε hε
    have hlt : internalEDist Set.univ x y < edist x y + ENNReal.ofReal ε := by
      rw [hIntrinsic x y]
      exact ENNReal.lt_add_right (edist_ne_top _ _) (by simpa using hε)
    unfold internalEDist at hlt
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hlt
    exact ⟨γ.1, hγ.le⟩
  exact ⟨hE, config_internalC_pt_continuous D hD hU hUc,
    config_internalC_val_continuous D hD hU hUc, hlen⟩

theorem configOriginal_outer_length (hd : 2 ≤ d) (c C : ℝ)
    {q : ConfigC d} (hq : q ∈ configOriginal hd c C) :
    IsLengthCoordinate q.1 := by
  obtain ⟨D, Dt, hD, hDt, -, rfl⟩ := hq
  exact config_internalC_isLengthCoordinate
    (configScaledMetric D (s := 1) (r := 1) (by norm_num) (by norm_num) 0)
    (configScaledMetric_isLength D hD (by norm_num) (by norm_num) 0)
    configOuter_isOpen (configOuter_isPreconnected hd)

theorem configOriginal_outer_tilde_length (hd : 2 ≤ d) (c C : ℝ)
    {q : ConfigC d} (hq : q ∈ configOriginal hd c C) :
    IsLengthCoordinate q.2.1 := by
  obtain ⟨D, Dt, hD, hDt, -, rfl⟩ := hq
  exact config_internalC_isLengthCoordinate
    (configScaledMetric Dt (s := 1) (r := 1) (by norm_num) (by norm_num) 0)
    (configScaledMetric_isLength Dt hDt (by norm_num) (by norm_num) 0)
    configOuter_isOpen (configOuter_isPreconnected hd)

theorem configOriginal_inner_length (hd : 2 ≤ d) (c C : ℝ)
    {q : ConfigC d} (hq : q ∈ configOriginal hd c C) :
    IsLengthCoordinate q.2.2.1 := by
  obtain ⟨D, Dt, hD, hDt, -, rfl⟩ := hq
  exact config_internalC_isLengthCoordinate
    (configScaledMetric D (s := 1) (r := 1) (by norm_num) (by norm_num) 0)
    (configScaledMetric_isLength D hD (by norm_num) (by norm_num) 0)
    configInner_isOpen (configInner_isPreconnected hd)

theorem configOriginal_inner_tilde_length (hd : 2 ≤ d) (c C : ℝ)
    {q : ConfigC d} (hq : q ∈ configOriginal hd c C) :
    IsLengthCoordinate q.2.2.2 := by
  obtain ⟨D, Dt, hD, hDt, -, rfl⟩ := hq
  exact config_internalC_isLengthCoordinate
    (configScaledMetric Dt (s := 1) (r := 1) (by norm_num) (by norm_num) 0)
    (configScaledMetric_isLength Dt hDt (by norm_num) (by norm_num) 0)
    configInner_isOpen (configInner_isPreconnected hd)

end HigherDimLQGMetric

import HigherDimLQGMetric.Limits.JointInternalMeas
import HigherDimLQGMetric.Weak.DetInternalTight

/-! Deterministic consistency of a joint ambient/internal subsequential limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The internal metric limit dominates the ambient metric on the domain. -/
theorem l6c_internal_limit_ge_ambient
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hamb : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (E : C(U × U, ℝ))
    (hdom : Tendsto (fun n => internalC (Dn n) (hDn n) hU hUc)
      atTop (𝓝 E)) (a b : U) :
    D.1 (a.1,b.1) ≤ E (a,b) := by
  have hambpt : Tendsto (fun n => (Dn n).1 (a.1,b.1)) atTop
      (𝓝 (D.1 (a.1,b.1))) :=
    (continuous_eval_const (a.1,b.1)).continuousAt.tendsto.comp hamb
  have hdompt : Tendsto (fun n => internalC (Dn n) (hDn n) hU hUc (a,b))
      atTop (𝓝 (E (a,b))) :=
    (continuous_eval_const (a,b)).continuousAt.tendsto.comp hdom
  apply le_of_tendsto_of_tendsto' hambpt hdompt
  intro n
  change (Dn n).1 (a.1,b.1) ≤ ((Dn n).internal U a.1 b.1).toReal
  have hfin := (Dn n).internal_ne_top_of_isPreconnected (hDn n) hU hUc a.2 b.2
  have hle := (Dn n).ofReal_le_internal U a.1 b.1
  have ht := (ENNReal.toReal_mono hfin hle)
  simpa only [ENNReal.toReal_ofReal ((Dn n).nonneg a.1 b.1)] using ht

/-- Pointwise limits of connected-domain internal metrics retain all metric
axioms when their ambient limit is a genuine continuous metric. -/
theorem l6c_internal_limit_isMetricFun
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hamb : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (E : C(U × U, ℝ))
    (hdom : Tendsto (fun n => internalC (Dn n) (hDn n) hU hUc)
      atTop (𝓝 E)) :
    LQGMetric.MetricGeometry.IsMetricFun E := by
  have hval (a b : U) :
      Tendsto (fun n => internalC (Dn n) (hDn n) hU hUc (a,b))
        atTop (𝓝 (E (a,b))) :=
    (continuous_eval_const (a,b)).continuousAt.tendsto.comp hdom
  refine { self_eq_zero := ?_, eq_of_eq_zero := ?_, symm := ?_, triangle := ?_ }
  · intro a
    have hz (n : ℕ) : internalC (Dn n) (hDn n) hU hUc (a,a) = 0 := by
      change ((Dn n).internal U a.1 a.1).toReal = 0
      rw [(Dn n).internal_self a.2]
      rfl
    have ht : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (E (a,a))) :=
      (hval a a).congr' (Filter.Eventually.of_forall hz)
    exact (tendsto_nhds_unique tendsto_const_nhds ht).symm
  · intro a b hzero
    have hle := l6c_internal_limit_ge_ambient Dn D hDn hamb hU hUc E hdom a b
    rw [hzero] at hle
    have h0 := D.nonneg a.1 b.1
    have heq := D.2.eq_of_eq_zero a.1 b.1 (le_antisymm hle h0)
    exact Subtype.ext heq
  · intro a b
    have hsym (n : ℕ) : internalC (Dn n) (hDn n) hU hUc (a,b) =
        internalC (Dn n) (hDn n) hU hUc (b,a) := by
      change ((Dn n).internal U a.1 b.1).toReal =
        ((Dn n).internal U b.1 a.1).toReal
      rw [(Dn n).internal_comm]
    exact tendsto_nhds_unique (hval a b)
      ((hval b a).congr' (Filter.Eventually.of_forall fun n => (hsym n).symm))
  · intro a b c
    exact le_of_tendsto_of_tendsto' (hval a c)
      ((hval a b).add (hval b c)) fun n =>
        internalC_triangle (Dn n) (hDn n) hU hUc a b c

/-- A continuous real-valued metric function induces a topology no finer than
the existing topology on the domain. -/
theorem l6c_continuous_pt_internal_limit
    {U : Set (Rd d)} (E : C(U × U, ℝ))
    (hE : LQGMetric.MetricGeometry.IsMetricFun E) :
    Continuous (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE) := by
  rw [Metric.continuous_iff']
  intro a ε hε
  have ht : Tendsto (fun x : U => E (x,a)) (𝓝 a) (𝓝 (E (a,a))) :=
    (E.continuous.comp (continuous_id.prodMk continuous_const)).tendsto a
  rw [hE.self_eq_zero] at ht
  exact ht.eventually (gt_mem_nhds hε)

/-- Domination by an ambient continuous metric makes the inverse identity
continuous too, so the domain metric has precisely its original topology. -/
theorem l6c_continuous_val_internal_limit
    (D : ContMetric d) {U : Set (Rd d)}
    (E : C(U × U, ℝ))
    (hE : LQGMetric.MetricGeometry.IsMetricFun E)
    (hdom : ∀ a b : U, D.1 (a.1,b.1) ≤ E (a,b)) :
    Continuous (metricFunSpaceValU E hE) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  obtain ⟨δ, hδ, hsmall⟩ := D.2.euclidean_of_small (a : U).1 ε hε
  refine ⟨δ, hδ, fun b hb => ?_⟩
  have hEb : E ((a : U), (b : U)) < δ := by
    change E ((b : U), (a : U)) < δ at hb
    rw [hE.symm (a : U) (b : U)]
    exact hb
  have hDb := hdom (a : U) (b : U)
  have hclose := hsmall (b : U).1 (lt_of_le_of_lt hDb hEb)
  let a' : U := metricFunSpaceValU E hE a
  let b' : U := metricFunSpaceValU E hE b
  change dist b' a' < ε
  rw [Subtype.dist_eq]
  have ha' : a'.1 = (a : U).1 := rfl
  have hb' : b'.1 = (b : U).1 := rfl
  rw [ha', hb']
  simpa only [dist_eq_norm, norm_sub_rev] using hclose

/-- Every joint compact-open limit of ambient length metrics and their
connected-domain internal metrics has the intrinsic consistency asserted in
[1] Lemma 3.1(2). -/
theorem l6c_internal_limit_consistent
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hamb : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (E : C(U × U, ℝ))
    (hdom : Tendsto (fun n => internalC (Dn n) (hDn n) hU hUc)
      atTop (𝓝 E)) :
    ∃ hE : LQGMetric.MetricGeometry.IsMetricFun E,
      Continuous (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE) ∧
      Continuous (metricFunSpaceValU E hE) ∧
      ∀ u v : U, D.internal U u.1 v.1 =
        LQGMetric.MetricGeometry.internalEDist Set.univ
          (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE u)
          (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE v) := by
  let hE := l6c_internal_limit_isMetricFun Dn D hDn hamb hU hUc E hdom
  have hEpt := l6c_continuous_pt_internal_limit E hE
  have hEval := l6c_continuous_val_internal_limit D E hE
    (l6c_internal_limit_ge_ambient Dn D hDn hamb hU hUc E hdom)
  refine ⟨hE, hEpt, hEval, ?_⟩
  have hconv : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    intro R _
    have hK : IsCompact
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) :=
      (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hamb) _ hK
  have hlim (a b : U) :
      Tendsto (fun n => ((Dn n).internal U a.1 b.1).toReal)
        atTop (𝓝 (E (a,b))) :=
    (continuous_eval_const (a,b)).continuousAt.tendsto.comp hdom
  intro u v
  exact internal_eq_of_tendsto_internal_on Dn D hDn hconv hU E hE
    hEpt hEval hlim u v

end HigherDimLQGMetric

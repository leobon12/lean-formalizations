import HigherDimLQGMetric.Locality.SecondTrunc
import HigherDimLQGMetric.Limits.JointInternalConsistent
import HigherDimLQGMetric.Locality.ConvergenceC

/-! The joint limits of the truncated internal arrays are the intrinsic
metrics of the two Weyl-related ambient limits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_second_internal_consistency
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)))
    {E : Type} [MeasurableSpace E] (Q : Measure E)
    (Z : ℕ → E → L7aJointState S T W W')
    (Zlim : E → L7aJointState S T W W')
    (hZc : ∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e)))
    (hgood : ∀ᵐ e ∂Q, IsContLengthFn (Zlim e).1.2 ∧
      IsProperFn (Zlim e).1.2)
    (hgraph₁ : ∀ᵐ e ∂Q, ∀ n,
      (Z n e).2.1 =
        l7a_stageArray hd κ hκ ξ (hεs n) S W hWc
          (l7a_markedField₁ (Z n e).1))
    (hgraph₂ : ∀ᵐ e ∂Q, ∀ n,
      (Z n e).2.2 =
        l7a_stageArray hd κ hκ ξ (hεs n) T W' hW'c
          (l7a_markedField₂ (Z n e).1))
    (τ : ℕ → ℕ) (hτ : StrictMono τ)
    (hballs₁ : ∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun k (p : Rd d × Rd d) =>
          (aEps κ ξ (εs (τ k)))⁻¹ *
            fieldLfpp ξ (truncMollify κ (εs (τ k))
              (l7a_markedField₁ (Z (τ k) e).1)) p)
        (fun p => (weylScale ξ
          (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1))
          (l7a_metricLift (Zlim e).1.2) p.1 p.2).toReal) atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    (hballs₂ : ∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun k (p : Rd d × Rd d) =>
          (aEps κ ξ (εs (τ k)))⁻¹ *
            fieldLfpp ξ (truncMollify κ (εs (τ k))
              (l7a_markedField₂ (Z (τ k) e).1)) p)
        (fun p => (weylScale ξ
          (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1) -
            (Zlim e).1.1.2.2)
          (l7a_metricLift (Zlim e).1.2) p.1 p.2).toReal) atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) :
    ∀ᵐ e ∂Q,
      (l7a_metricLift (Zlim e).1.2).IsLength ∧
      (l7a_normalizedMarkedMetric ξ (Zlim e).1).IsLength ∧
      (∀ i : S, ∃ hJ : LQGMetric.MetricGeometry.IsMetricFun ((Zlim e).2.1 i),
        ∀ u v : (W i.1 : Set (Rd d)),
          (l7a_normalizedMarkedMetric ξ (Zlim e).1).internal
            (W i.1 : Set (Rd d)) u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt
              ((Zlim e).2.1 i) hJ u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt
              ((Zlim e).2.1 i) hJ v)) ∧
      (∀ j : T, ∃ hJ : LQGMetric.MetricGeometry.IsMetricFun ((Zlim e).2.2 j),
        ∀ u v : (W' j.1 : Set (Rd d)),
          (l7a_perturbedMarkedMetric ξ (Zlim e).1).internal
            (W' j.1 : Set (Rd d)) u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt
              ((Zlim e).2.2 j) hJ u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt
              ((Zlim e).2.2 j) hJ v)) := by
  filter_upwards [hgood, hgraph₁, hgraph₂, hballs₁, hballs₂] with
    e hge hge₁ hge₂ hb₁ hb₂
  let D : ContMetric d := l7a_metricLift (Zlim e).1.2
  have hD : D.IsLength := l7a_metricLift_isLength hge.1
  let D₁ : ContMetric d := l7a_normalizedMarkedMetric ξ (Zlim e).1
  let D₂ : ContMetric d := l7a_perturbedMarkedMetric ξ (Zlim e).1
  have hD₁ : D₁.IsLength := by
    rw [show D₁ = weylMetric ξ
      (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1)) D hD from
      l7a_normalizedMarkedMetric_eq_weyl ξ (Zlim e).1 hD]
    exact weylMetric_isLength hD
  have hD₂ : D₂.IsLength := by
    rw [show D₂ = weylMetric ξ
      (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1) -
        (Zlim e).1.1.2.2) D hD from
      l7a_perturbedMarkedMetric_eq_weyl ξ (Zlim e).1 hD]
    exact weylMetric_isLength hD
  refine ⟨hD, hD₁, ?_, ?_⟩
  · intro i
    let Dn : ℕ → ContMetric d := fun k =>
      l7a_truncScaledMetric hd κ hκ ξ (hεs (τ k))
        (l7a_markedField₁ (Z (τ k) e).1)
    have hDn (k : ℕ) : (Dn k).IsLength :=
      l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (τ k)) _
    have htarget (p : Rd d × Rd d) :
        D₁.1 p =
        (weylScale ξ (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1))
          D p.1 p.2).toReal := by
      rw [show D₁ = weylMetric ξ
        (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1)) D hD from
        l7a_normalizedMarkedMetric_eq_weyl ξ (Zlim e).1 hD]
      exact weylMetric_apply hD p
    have hb : ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (τ k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (τ k))
                (l7a_markedField₁ (Z (τ k) e).1)) p)
          ⇑D₁.1 atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
      intro R hR
      convert hb₁ R hR using 1
      ext p
      exact htarget p
    have hamb : Tendsto (fun k => (Dn k).1) atTop (𝓝 D₁.1) :=
      l7a_tendsto_truncScaledMetric_of_balls hd κ hκ ξ
        (fun k => εs (τ k)) (fun k => hεs (τ k))
        (fun k => l7a_markedField₁ (Z (τ k) e).1) D₁ hb
    have hJt : Tendsto (fun k => (Z (τ k) e).2.1 i) atTop
        (𝓝 ((Zlim e).2.1 i)) := by
      have hc : Continuous (fun q : L7aJointState S T W W' => q.2.1 i) := by fun_prop
      exact (hc.tendsto (Zlim e)).comp ((hZc e).comp hτ.tendsto_atTop)
    have hint : Tendsto
        (fun k => internalC (Dn k) (hDn k) (W i.1).isOpen
          (hWc i.1 i.2)) atTop (𝓝 ((Zlim e).2.1 i)) := by
      apply hJt.congr'
      filter_upwards with k
      exact (congrArg (fun a : L7aFiniteArray S W => a i)
        (hge₁ (τ k)))
    obtain ⟨hJ, _, _, hcons⟩ :=
      l6c_internal_limit_consistent Dn D₁ hDn hamb
        (W i.1).isOpen (hWc i.1 i.2)
        ((Zlim e).2.1 i) hint
    exact ⟨hJ, hcons⟩
  · intro j
    let Dn : ℕ → ContMetric d := fun k =>
      l7a_truncScaledMetric hd κ hκ ξ (hεs (τ k))
        (l7a_markedField₂ (Z (τ k) e).1)
    have hDn (k : ℕ) : (Dn k).IsLength :=
      l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs (τ k)) _
    have htarget (p : Rd d × Rd d) :
        D₂.1 p =
        (weylScale ξ
          (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1) -
            (Zlim e).1.1.2.2) D p.1 p.2).toReal := by
      rw [show D₂ = weylMetric ξ
        (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1) -
          (Zlim e).1.1.2.2) D hD from
        l7a_perturbedMarkedMetric_eq_weyl ξ (Zlim e).1 hD]
      exact weylMetric_apply hD p
    have hb : ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (τ k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (τ k))
                (l7a_markedField₂ (Z (τ k) e).1)) p)
          ⇑D₂.1 atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
      intro R hR
      convert hb₂ R hR using 1
      ext p
      exact htarget p
    have hamb : Tendsto (fun k => (Dn k).1) atTop (𝓝 D₂.1) :=
      l7a_tendsto_truncScaledMetric_of_balls hd κ hκ ξ
        (fun k => εs (τ k)) (fun k => hεs (τ k))
        (fun k => l7a_markedField₂ (Z (τ k) e).1) D₂ hb
    have hJt : Tendsto (fun k => (Z (τ k) e).2.2 j) atTop
        (𝓝 ((Zlim e).2.2 j)) := by
      have hc : Continuous (fun q : L7aJointState S T W W' => q.2.2 j) := by fun_prop
      exact (hc.tendsto (Zlim e)).comp ((hZc e).comp hτ.tendsto_atTop)
    have hint : Tendsto
        (fun k => internalC (Dn k) (hDn k) (W' j.1).isOpen
          (hW'c j.1 j.2)) atTop (𝓝 ((Zlim e).2.2 j)) := by
      apply hJt.congr'
      filter_upwards with k
      exact (congrArg (fun a : L7aFiniteArray T W' => a j)
        (hge₂ (τ k)))
    obtain ⟨hJ, _, _, hcons⟩ :=
      l6c_internal_limit_consistent Dn D₂ hDn hamb
        (W' j.1).isOpen (hW'c j.1 j.2)
        ((Zlim e).2.2 j) hint
    exact ⟨hJ, hcons⟩

end HigherDimLQGMetric

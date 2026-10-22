import HigherDimLQGMetric.Coord.LocalRealization
import LQGMetric.Metric.InternalLimit

/-!
# Agreement of lengths on a common open domain

This is the generic common-carrier form of MA1 A3(iii).  In the intended use,
the carrier is the subtype of `U₁`; the first family is the restriction of
the `U`-coordinate, and the second is the `U₁`-coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- Restricting a metric function to a subtype preserves its metric axioms. -/
theorem IsMetricFun.restrictTo {X : Type*} {ρ : X × X → ℝ}
    (hρ : IsMetricFun ρ) (S : Set X) :
    IsMetricFun (fun p : S × S => ρ (p.1.1, p.2.1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x; exact hρ.self_eq_zero x.1
  · intro x y hzero; exact Subtype.ext (hρ.eq_of_eq_zero x.1 y.1 hzero)
  · intro x y; exact hρ.symm x.1 y.1
  · intro x y z; exact hρ.triangle x.1 y.1 z.1

/-- If every curve has the same length in two coordinates and `τ` is a length
coordinate, the direct distance in `ρ` is at most the direct distance in `τ`. -/
theorem coordinate_le_internal_coordinate
    {X : Type*} [MetricSpace X] {ρ : X × X → ℝ} {τ : X × X → ℝ}
    (hρ : IsMetricFun ρ) (hτ : IsLengthCoordinate τ)
    (hlen : ∀ P : I →ᵇ X,
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
        (Set.IccExtend zero_le_one P) 0 1 =
      curveLengthWith (fun u v => ENNReal.ofReal (τ (u, v)))
        (Set.IccExtend zero_le_one P) 0 1)
    (x y : X) : ρ (x, y) ≤ τ (x, y) := by
  have hρnonneg : 0 ≤ ρ (x, y) := by
    change 0 ≤ dist (MetricFunSpace.pt ρ hρ x)
      (MetricFunSpace.pt ρ hρ y)
    exact dist_nonneg
  have hτnonneg : 0 ≤ τ (x, y) := by
    change 0 ≤ dist (MetricFunSpace.pt τ hτ.metric x)
      (MetricFunSpace.pt τ hτ.metric y)
    exact dist_nonneg
  have hbound : ∀ ε : ℝ, 0 < ε →
      ENNReal.ofReal (ρ (x, y)) ≤ ENNReal.ofReal (τ (x, y)) + ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨γ, hγ⟩ := hτ.length (MetricFunSpace.pt τ hτ.metric x)
      (MetricFunSpace.pt τ hτ.metric y) ε hε
    let P : I →ᵇ X := mkOfCompact (γ.map hτ.val_continuous).toContinuousMap
    have hP0 : P 0 = x := by
      change LQGMetric.metricFunSpaceVal τ hτ.metric (γ 0) = x
      rw [γ.source]
      rfl
    have hP1 : P 1 = y := by
      change LQGMetric.metricFunSpaceVal τ hτ.metric (γ 1) = y
      rw [γ.target]
      rfl
    have hdist : ENNReal.ofReal (ρ (x, y)) ≤
        curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
          (Set.IccExtend zero_le_one P) 0 1 := by
      have h := le_curveLengthWith (δ := fun u v => ENNReal.ofReal (ρ (u, v)))
        (P := Set.IccExtend zero_le_one P) zero_le_one
      simpa [Set.IccExtend_of_mem, hP0, hP1] using h
    have hτlen : curveLengthWith (fun u v => ENNReal.ofReal (τ (u, v)))
        (Set.IccExtend zero_le_one P) 0 1 = pathLength γ := by
      convert pathLength_eq_coordinateLength hτ.metric γ using 1
      rfl
    calc ENNReal.ofReal (ρ (x, y))
        ≤ curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
            (Set.IccExtend zero_le_one P) 0 1 := hdist
      _ = pathLength γ := (hlen P).trans hτlen
      _ ≤ ENNReal.ofReal (τ (x, y)) + ENNReal.ofReal ε := by
        simpa only [edist_dist, MetricFunSpace.dist_pt] using hγ
  have hle : ENNReal.ofReal (ρ (x, y)) ≤ ENNReal.ofReal (τ (x, y)) :=
    ENNReal.le_of_forall_pos_le_add (fun ε hε _ => by
      simpa only [ENNReal.ofReal_coe_nnreal] using
        hbound (ε : ℝ) (by exact_mod_cast hε))
  exact (ENNReal.ofReal_le_ofReal_iff hτnonneg).1 hle

/-- Short distance equality when the first coordinate realizes its distance by
a curve on which the two coordinates assign the same length. -/
theorem coordinate_eq_of_local_realization
    {X : Type*} [MetricSpace X] {ρ : X × X → ℝ} {τ : X × X → ℝ}
    (hρ : IsMetricFun ρ) (hτ : IsLengthCoordinate τ)
    (hlen : ∀ P : I →ᵇ X,
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
        (Set.IccExtend zero_le_one P) 0 1 =
      curveLengthWith (fun u v => ENNReal.ofReal (τ (u, v)))
        (Set.IccExtend zero_le_one P) 0 1)
    {x y : X}
    (hrealize : ∃ P : I →ᵇ X, P 0 = x ∧ P 1 = y ∧
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
        (Set.IccExtend zero_le_one P) 0 1 = ENNReal.ofReal (ρ (x, y))) :
    ρ (x, y) = τ (x, y) := by
  have hle : ρ (x, y) ≤ τ (x, y) := coordinate_le_internal_coordinate hρ hτ hlen x y
  obtain ⟨P, hP0, hP1, hPlen⟩ := hrealize
  have hτdist : ENNReal.ofReal (τ (x, y)) ≤
      curveLengthWith (fun u v => ENNReal.ofReal (τ (u, v)))
        (Set.IccExtend zero_le_one P) 0 1 := by
    have h := le_curveLengthWith (δ := fun u v => ENNReal.ofReal (τ (u, v)))
      (P := Set.IccExtend zero_le_one P) zero_le_one
    simpa [Set.IccExtend_of_mem, hP0, hP1] using h
  have hρnonneg : 0 ≤ ρ (x, y) := by
    change 0 ≤ dist (MetricFunSpace.pt ρ hρ x)
      (MetricFunSpace.pt ρ hρ y)
    exact dist_nonneg
  have hτleρ : τ (x, y) ≤ ρ (x, y) :=
    (ENNReal.ofReal_le_ofReal_iff hρnonneg).1
      (hτdist.trans ((hlen P).symm.trans hPlen).le)
  exact le_antisymm hle hτleρ

/-- The limiting coordinates agree on a neighborhood of every point if short
distances in the first family are uniformly realized by paths in the common domain. -/
theorem coordinate_limits_locally_eq
    {X : Type*} [MetricSpace X]
    (ρ τ : ℕ → X × X → ℝ) (ρlim τlim : X × X → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n))
    (hτ : ∀ n, IsLengthCoordinate (τ n))
    (hρlim : IsCoordinate ρlim)
    (hρconv : TendstoLocallyUniformly ρ ρlim atTop)
    (hτconv : TendstoLocallyUniformly τ τlim atTop)
    (hlen : ∀ n, ∀ P : I →ᵇ X,
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
        (Set.IccExtend zero_le_one P) 0 1 =
      curveLengthWith (fun u v => ENNReal.ofReal (τ n (u, v)))
        (Set.IccExtend zero_le_one P) 0 1)
    (hlocal : ∀ z : X, ∃ N : Set X, N ∈ 𝓝 z ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ N, ∀ v ∈ N,
        ρ n (u, v) < δ →
          ∃ P : I →ᵇ X, P 0 = u ∧ P 1 = v ∧
            curveLengthWith (fun p q => ENNReal.ofReal (ρ n (p, q)))
              (Set.IccExtend zero_le_one P) 0 1 = ENNReal.ofReal (ρ n (u, v))) :
    ∀ z : X, ∃ N : Set X, N ∈ 𝓝 z ∧
      ∀ u ∈ N, ∀ v ∈ N, ρlim (u, v) = τlim (u, v) := by
  intro z
  obtain ⟨N, hNz, δ, hδ, hP2⟩ := hlocal z
  have hρz : Tendsto (fun u => ρlim (z, u)) (𝓝 z) (𝓝 (0 : ℝ)) := by
    have hpair : Continuous (fun u : X => (z, u)) :=
      continuous_const.prodMk continuous_id
    have ht := (hρlim.continuous.comp hpair).tendsto z
    simpa [Function.comp_def, hρlim.metric.self_eq_zero] using ht
  let N' : Set X := N ∩ {u | ρlim (z, u) < δ / 4}
  have hN'z : N' ∈ 𝓝 z := inter_mem hNz (hρz.eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 4)))
  refine ⟨N', hN'z, ?_⟩
  intro u hu v hv
  have huN : u ∈ N := hu.1
  have hvN : v ∈ N := hv.1
  have huδ : ρlim (z, u) < δ / 4 := hu.2
  have hvδ : ρlim (z, v) < δ / 4 := hv.2
  have hρsmall : ρlim (u, v) < δ := by
    have htri := hρlim.metric.triangle u z v
    rw [hρlim.metric.symm u z] at htri
    linarith
  have hptρ : Tendsto (fun n => ρ n (u, v)) atTop (𝓝 (ρlim (u, v))) :=
    hρconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (u, v))
  have hptτ : Tendsto (fun n => τ n (u, v)) atTop (𝓝 (τlim (u, v))) :=
    hτconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (u, v))
  have heq : (fun n => ρ n (u, v)) =ᶠ[atTop] (fun n => τ n (u, v)) := by
    filter_upwards [hptρ.eventually (gt_mem_nhds hρsmall)] with n hsmall
    exact coordinate_eq_of_local_realization (hρ n).metric (hτ n) (hlen n)
      (hP2 n u huN v hvN hsmall)
  exact tendsto_nhds_unique (hptρ.congr' heq) hptτ

/-- Local equality of two coordinate metrics gives equality of the length of
every curve.  This is the metric-function-space form of local isometry. -/
theorem coordinate_curveLength_eq_of_locally_eq
    {X : Type*} [MetricSpace X] {ρ : X × X → ℝ} {τ : X × X → ℝ}
    (hρ : IsCoordinate ρ) (hτ : IsCoordinate τ)
    (hloc : ∀ z : X, ∃ N : Set X, N ∈ 𝓝 z ∧
      ∀ u ∈ N, ∀ v ∈ N, ρ (u, v) = τ (u, v))
    (P : I →ᵇ X) :
    curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 =
    curveLengthWith (fun u v => ENNReal.ofReal (τ (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 := by
  let Qρ : Path (MetricFunSpace.pt ρ hρ.metric (P 0))
      (MetricFunSpace.pt ρ hρ.metric (P 1)) :=
    { toFun := fun t => MetricFunSpace.pt ρ hρ.metric (P t)
      continuous_toFun := hρ.pt_continuous.comp P.continuous
      source' := rfl
      target' := rfl }
  let Qτ : Path (MetricFunSpace.pt τ hτ.metric (P 0))
      (MetricFunSpace.pt τ hτ.metric (P 1)) :=
    { toFun := fun t => MetricFunSpace.pt τ hτ.metric (P t)
      continuous_toFun := hτ.pt_continuous.comp P.continuous
      source' := rfl
      target' := rfl }
  let f : MetricFunSpace ρ hρ.metric → MetricFunSpace τ hτ.metric := id
  have hlocalTime : ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ ε > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
        dist s t < ε → dist s' t < ε →
          edist (f (Qρ.extend s)) (f (Qρ.extend s')) =
          edist (Qρ.extend s) (Qρ.extend s') := by
    intro t ht
    obtain ⟨N, hNmem, hNloc⟩ := hloc
      (LQGMetric.metricFunSpaceVal ρ hρ.metric (Qρ.extend t))
    have hcont : Continuous (fun s : ℝ =>
        LQGMetric.metricFunSpaceVal ρ hρ.metric (Qρ.extend s)) :=
      hρ.val_continuous.comp Qρ.continuous_extend
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (hcont.continuousAt.preimage_mem_nhds hNmem)
    refine ⟨ε, hε, ?_⟩
    intro s hs s' hs' hst hs't
    have hsN : LQGMetric.metricFunSpaceVal ρ hρ.metric (Qρ.extend s) ∈ N :=
      hball (by simpa [Metric.mem_ball] using hst)
    have hs'N : LQGMetric.metricFunSpaceVal ρ hρ.metric (Qρ.extend s') ∈ N :=
      hball (by simpa [Metric.mem_ball] using hs't)
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal
        (τ (LQGMetric.metricFunSpaceVal ρ hρ.metric (Qρ.extend s),
            LQGMetric.metricFunSpaceVal ρ hρ.metric (Qρ.extend s'))) =
      ENNReal.ofReal
        (ρ (LQGMetric.metricFunSpaceVal ρ hρ.metric (Qρ.extend s),
            LQGMetric.metricFunSpaceVal ρ hρ.metric (Qρ.extend s')))
    rw [hNloc _ hsN _ hs'N]
  have hEq := curveLength_comp_eq_of_locally (f := f) (P := Qρ.extend) hlocalTime
  have hρlen : curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 = pathLength Qρ := by
    convert pathLength_eq_coordinateLength hρ.metric Qρ using 1
    rfl
  have hτlen : curveLengthWith (fun u v => ENNReal.ofReal (τ (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 = pathLength Qτ := by
    convert pathLength_eq_coordinateLength hτ.metric Qτ using 1
    rfl
  rw [hρlen, hτlen]
  exact hEq.symm

/-- Lemma 2.2′(iii), in the common-domain form supplied by P1–P2. -/
theorem lemma22iii
    {X : Type*} [MetricSpace X]
    (ρ τ : ℕ → X × X → ℝ) (ρlim τlim : X × X → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n))
    (hτ : ∀ n, IsLengthCoordinate (τ n))
    (hρlim : IsCoordinate ρlim) (hτlim : IsCoordinate τlim)
    (hρconv : TendstoLocallyUniformly ρ ρlim atTop)
    (hτconv : TendstoLocallyUniformly τ τlim atTop)
    (hlen : ∀ n, ∀ P : I →ᵇ X,
      curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
        (Set.IccExtend zero_le_one P) 0 1 =
      curveLengthWith (fun u v => ENNReal.ofReal (τ n (u, v)))
        (Set.IccExtend zero_le_one P) 0 1)
    (hlocal : ∀ z : X, ∃ N : Set X, N ∈ 𝓝 z ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ N, ∀ v ∈ N,
        ρ n (u, v) < δ →
          ∃ P : I →ᵇ X, P 0 = u ∧ P 1 = v ∧
            curveLengthWith (fun p q => ENNReal.ofReal (ρ n (p, q)))
              (Set.IccExtend zero_le_one P) 0 1 = ENNReal.ofReal (ρ n (u, v)))
    (P : I →ᵇ X) :
    curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 =
    curveLengthWith (fun u v => ENNReal.ofReal (τlim (u, v)))
      (Set.IccExtend zero_le_one P) 0 1 :=
  coordinate_curveLength_eq_of_locally_eq hρlim hτlim
    (coordinate_limits_locally_eq ρ τ ρlim τlim hρ hτ hρlim hρconv hτconv hlen hlocal) P

end HigherDimLQGMetric

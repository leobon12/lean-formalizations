import HigherDimLQGMetric.Weak.DetInternal
import LQGMetric.Metric.LengthLimit
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Deterministic compactness of internal metric families

The internal metric on an open connected domain is a real continuous function
on pairs of points of that domain. This is the function space used in MA5 A10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Real-valued internal metric of a continuous length metric on a connected open domain. -/
def internalC (D : ContMetric d) (hD : D.IsLength) {U : Set (Rd d)}
    (hU : IsOpen U) (hUc : IsPreconnected U) : C(U × U, ℝ) := by
  let J : U × U → ℝ≥0∞ := fun p => D.internal U p.1.1 p.2.1
  have hJ : Continuous J := by
    have hpair : Continuous (fun p : U × U => ((p.1 : Rd d), (p.2 : Rd d))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact (D.continuousOn_internal hD hU).comp_continuous hpair
      (fun p => ⟨p.1.2,p.2.2⟩)
  have hfin (p : U × U) : J p ≠ ∞ :=
    D.internal_ne_top_of_isPreconnected hD hU hUc p.1.2 p.2.2
  exact ⟨fun p => (J p).toReal, continuous_iff_continuousAt.2 fun p =>
    (ENNReal.continuousAt_toReal (hfin p)).comp hJ.continuousAt⟩

/-- The real internal distance obeys the triangle inequality on a connected domain. -/
theorem internalC_triangle (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (a b c : U) : internalC D hD hU hUc (a,c) ≤
      internalC D hD hU hUc (a,b) + internalC D hD hU hUc (b,c) := by
  change (D.internal U a.1 c.1).toReal ≤
    (D.internal U a.1 b.1).toReal + (D.internal U b.1 c.1).toReal
  exact ENNReal.toReal_le_add (D.internal_triangle U a.1 b.1 c.1)
    (D.internal_ne_top_of_isPreconnected hD hU hUc a.2 b.2)
    (D.internal_ne_top_of_isPreconnected hD hU hUc b.2 c.2)

/-- The internal distance function is controlled by moving its two endpoints. -/
theorem internalC_dist_le (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (p q : U × U) :
    dist (internalC D hD hU hUc p) (internalC D hD hU hUc q) ≤
      internalC D hD hU hUc (p.1,q.1) +
      internalC D hD hU hUc (p.2,q.2) := by
  have h₁ := internalC_triangle D hD hU hUc p.1 q.1 p.2
  have h₂ := internalC_triangle D hD hU hUc q.1 q.2 p.2
  have h₃ := internalC_triangle D hD hU hUc q.1 p.1 q.2
  have h₄ := internalC_triangle D hD hU hUc p.1 p.2 q.2
  have hs₁ : internalC D hD hU hUc (q.1,p.1) =
      internalC D hD hU hUc (p.1,q.1) := by
    change (D.internal U q.1.1 p.1.1).toReal =
      (D.internal U p.1.1 q.1.1).toReal
    rw [D.internal_comm]
  have hs₂ : internalC D hD hU hUc (q.2,p.2) =
      internalC D hD hU hUc (p.2,q.2) := by
    change (D.internal U q.2.1 p.2.1).toReal =
      (D.internal U p.2.1 q.2.1).toReal
    rw [D.internal_comm]
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith [h₁, h₂, h₃, h₄]

/-- Near a fixed endpoint, all sufficiently late internal metrics are uniformly small. -/
theorem eventually_internalC_small_near
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (a : U) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ 𝓝 a, ∀ᶠ n : ℕ in atTop, ∀ u ∈ V,
      internalC (Dn n) (hDn n) hU hUc (a,u) < ε := by
  obtain ⟨r₀, hr₀, -, hlocal⟩ :=
    eventually_internal_eq_on_small_ball Dn D hDn hconv hU a.2
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuous_iff.mp D.continuous_pt a.1 (ε / 2)
    (by positivity)
  let r : ℝ := min (r₀ / 2) (δ / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hr₀' : r < r₀ := by dsimp [r]; linarith [min_le_left (r₀ / 2) (δ / 2)]
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_right (r₀ / 2) (δ / 2)]
  let S : ℝ := ‖(a : Rd d)‖ + r₀ + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hK : Metric.closedBall (a : Rd d) r₀ ⊆ Metric.closedBall (0 : Rd d) S := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm := norm_add_le (y - (a : Rd d)) (a : Rd d)
    have heq : y - (a : Rd d) + (a : Rd d) = y := by abel
    rw [heq] at hnorm
    have hay : ‖y - (a : Rd d)‖ ≤ r₀ := by simpa [dist_eq_norm, norm_sub_rev] using hy
    dsimp [S]
    linarith
  refine ⟨Metric.ball a r, Metric.ball_mem_nhds a hr, ?_⟩
  filter_upwards [hlocal, eventually_dist_lt_on_closedBall
    (fun n => (Dn n).1) D.1 hconv S (ε / 2) hS (by positivity)] with n hn hclose u hu
  have hua : dist (u : Rd d) (a : Rd d) < r := by simpa [Subtype.dist_eq] using hu
  have hu₀ : (u : Rd d) ∈ Metric.ball a.1 r₀ := by
    exact Metric.mem_ball.mpr (hua.trans hr₀')
  have ha₀ : (a : Rd d) ∈ Metric.ball a.1 r₀ := Metric.mem_ball_self hr₀
  have huK : (u : Rd d) ∈ Metric.closedBall (0 : Rd d) S :=
    hK (Metric.ball_subset_closedBall hu₀)
  have haK : (a : Rd d) ∈ Metric.closedBall (0 : Rd d) S :=
    hK (Metric.ball_subset_closedBall ha₀)
  have hDsmall : D.1 (a.1,u.1) < ε / 2 := by
    have h := hsmall u.1 (hua.trans hrδ)
    simpa only [D.dist_pt, D.apply_comm u.1 a.1] using h
  change ((Dn n).internal U a.1 u.1).toReal < ε
  rw [hn a.1 ha₀ u.1 hu₀, ENNReal.toReal_ofReal ((Dn n).nonneg a.1 u.1)]
  have hclose' := abs_lt.mp (hclose a.1 haK u.1 huK)
  linarith

/-- Local uniform convergence of global length metrics gives an equicontinuous family of
internal distance functions on every open connected domain. -/
theorem equicontinuous_internalC
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    Equicontinuous (fun n => ⇑(internalC (Dn n) (hDn n) hU hUc)) := by
  intro p
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨Va, hVa, hea⟩ := eventually_internalC_small_near Dn D hDn hconv hU hUc p.1
    (by linarith : 0 < ε / 2)
  obtain ⟨Vb, hVb, heb⟩ := eventually_internalC_small_near Dn D hDn hconv hU hUc p.2
    (by linarith : 0 < ε / 2)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hea.and heb)
  have hEarly : ∀ᶠ q in 𝓝 p, ∀ n ∈ Finset.range N,
      dist (internalC (Dn n) (hDn n) hU hUc p)
        (internalC (Dn n) (hDn n) hU hUc q) < ε := by
    apply (Finset.eventually_all (Finset.range N)).2
    intro n _
    have hc : ContinuousAt (internalC (Dn n) (hDn n) hU hUc) p :=
      (internalC (Dn n) (hDn n) hU hUc).continuous.continuousAt
    filter_upwards [hc (Metric.ball_mem_nhds _ hε)] with q hq
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_comm] using hq
  filter_upwards [hEarly, prod_mem_nhds hVa hVb] with q hq hqV n
  by_cases hn : n < N
  · exact hq n (Finset.mem_range.mpr hn)
  · have hna := (hN n (Nat.le_of_not_lt hn)).1 q.1 hqV.1
    have hnb := (hN n (Nat.le_of_not_lt hn)).2 q.2 hqV.2
    have hdist := internalC_dist_le (Dn n) (hDn n) hU hUc p q
    linarith

/-- Each pointwise internal-distance sequence is bounded, including its finite initial part. -/
theorem bounded_internalC_pointwise
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (p : U × U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, internalC (Dn n) (hDn n) hU hUc p ≤ B := by
  obtain ⟨B, hB, hevent⟩ := eventually_internal_bounded_of_isPreconnected Dn D
    hDn hconv hU hUc p.1.2 p.2.2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let f : ℕ → ℝ := fun n => internalC (Dn n) (hDn n) hU hUc p
  have hnonneg (n : ℕ) : 0 ≤ f n := by
    change 0 ≤ ((Dn n).internal U p.1.1 p.2.1).toReal
    exact ENNReal.toReal_nonneg
  refine ⟨B + ∑ n ∈ Finset.range N, f n, ?_, ?_⟩
  · exact add_nonneg hB (Finset.sum_nonneg fun n _ => hnonneg n)
  · intro n
    by_cases hn : n < N
    · have hsum : f n ≤ ∑ k ∈ Finset.range N, f k :=
        Finset.single_le_sum (fun k _ => hnonneg k)
          (Finset.mem_range.mpr hn)
      have hB' : 0 ≤ B := hB
      change f n ≤ B + ∑ k ∈ Finset.range N, f k
      linarith
    · have hle := ENNReal.toReal_le_of_le_ofReal hB (hN n (Nat.le_of_not_lt hn))
      change f n ≤ B at hle
      have hsum : 0 ≤ ∑ k ∈ Finset.range N, f k :=
        Finset.sum_nonneg fun k _ => hnonneg k
      change f n ≤ B + ∑ k ∈ Finset.range N, f k
      linarith

/-- Internal metrics on an open connected domain form a relatively compact family whenever
the ambient length metrics converge locally uniformly. This is the deterministic compactness
step in MA5 A10; the compact-open topology is used on `C(U × U, ℝ)`. -/
theorem isCompact_closure_range_internalC
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsCompact (closure (Set.range (fun n => internalC (Dn n) (hDn n) hU hUc))) := by
  let f : ℕ → C(U × U, ℝ) := fun n => internalC (Dn n) (hDn n) hU hUc
  let S : Set C(U × U, ℝ) := Set.range f
  have hEq : Equicontinuous ((↑) : S → U × U → ℝ) := by
    have hfamily : Equicontinuous (fun n => ⇑(f n)) :=
      equicontinuous_internalC Dn D hDn hconv hU hUc
    intro p V hV
    filter_upwards [hfamily p V hV] with q hq i
    obtain ⟨n, hn⟩ := i.2
    change f n = i.1 at hn
    rw [← hn]
    exact hq n
  have hEmb : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set (U × U) | IsCompact K} ∘
        (fun g : C(U × U, ℝ) => (g : U × U → ℝ))) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    change IsClosed (Set.range (ContinuousMap.toUniformOnFunIsCompact :
      C(U × U, ℝ) → UniformOnFun (U × U) ℝ {K | IsCompact K}))
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
  change IsCompact (closure S)
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖_compact := fun K hK => hK) hEmb
  · intro K _
    exact hEq.equicontinuousOn K
  · intro K _ p _
    obtain ⟨B, hB, hbound⟩ := bounded_internalC_pointwise Dn D hDn hconv hU hUc p
    refine ⟨Set.Icc 0 B, isCompact_Icc, ?_⟩
    intro g hg
    obtain ⟨n, rfl⟩ := hg
    exact ⟨ENNReal.toReal_nonneg, hbound n⟩

/-- Forget the changed metric on a domain while retaining its original topology. -/
def metricFunSpaceValU {U : Set (Rd d)} (E : U × U → ℝ)
    (hE : LQGMetric.MetricGeometry.IsMetricFun E) :
    LQGMetric.MetricGeometry.MetricFunSpace E hE → U := id

/-- Local agreement on a domain identifies the two intrinsic metrics. -/
theorem internal_eq_of_locally_eq_on
    (D : ContMetric d) {U : Set (Rd d)}
    (E : C(U × U, ℝ)) (hE : LQGMetric.MetricGeometry.IsMetricFun E)
    (hEpt : Continuous (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE))
    (hEval : Continuous (metricFunSpaceValU E hE))
    (hloc : ∀ x : U, ∃ r : ℝ, 0 < r ∧ ∀ a b : U,
      a.1 ∈ Metric.ball x.1 r → b.1 ∈ Metric.ball x.1 r →
        E (a,b) = D.1 (a.1,b.1))
    (u v : U) : D.internal U u.1 v.1 =
      LQGMetric.MetricGeometry.internalEDist Set.univ
        (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE u)
        (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE v) := by
  let Y₁ : Set D.Space := D.pt '' U
  let Y₂ : Set (LQGMetric.MetricGeometry.MetricFunSpace E hE) := Set.univ
  have hY₁ (z : Y₁) : D.unpt z.1 ∈ U := by
    obtain ⟨x,hx,hx'⟩ := z.2
    simpa [← hx'] using hx
  let e : Y₁ ≃ₜ Y₂ :=
    { toFun := fun z => ⟨LQGMetric.MetricGeometry.MetricFunSpace.pt E hE
          ⟨D.unpt z.1, hY₁ z⟩, Set.mem_univ _⟩
      invFun := fun z => ⟨D.pt (z.1 : U).1, ⟨(z.1 : U).1, (z.1 : U).2, rfl⟩⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl
      continuous_toFun :=
        (hEpt.comp ((D.continuous_unpt.comp continuous_subtype_val).subtype_mk hY₁)).subtype_mk _
      continuous_invFun := by
        have hVal : Continuous (fun z : Y₂ => metricFunSpaceValU E hE z.1) :=
          hEval.comp continuous_subtype_val
        have hVal' : Continuous (fun z : Y₂ => ((z.1 : U).1 : Rd d)) :=
          (show Continuous (fun x : U => (x : Rd d)) from continuous_subtype_val).comp hVal
        exact (D.continuous_pt.comp hVal').subtype_mk _ }
  have he : LQGMetric.MetricGeometry.IsLocalIsometryOn e := by
    intro z
    obtain ⟨r,hr,hEq⟩ := hloc ⟨D.unpt z.1, hY₁ z⟩
    refine ⟨{q : Y₁ | D.unpt q.1 ∈ Metric.ball (D.unpt z.1) r},
      (D.continuous_unpt.comp continuous_subtype_val).continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hr), ?_⟩
    intro a ha b hb
    rw [edist_dist, edist_dist]
    congr 1
    change E (⟨D.unpt a.1, hY₁ a⟩, ⟨D.unpt b.1, hY₁ b⟩) =
      D.1 (D.unpt a.1, D.unpt b.1)
    exact hEq ⟨D.unpt a.1, hY₁ a⟩ ⟨D.unpt b.1, hY₁ b⟩ ha hb
  have h := LQGMetric.MetricGeometry.internalEDist_eq_of_isLocalIsometryOn he
    (⟨D.pt u.1, ⟨u.1,u.2,rfl⟩⟩ : Y₁) (⟨D.pt v.1, ⟨v.1,v.2,rfl⟩⟩ : Y₁)
  change LQGMetric.MetricGeometry.internalEDist Set.univ
    (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE u)
    (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE v) = D.internal U u.1 v.1 at h
  exact h.symm

/-- Domain-valued form of Lemma 3.5: the intrinsic metric of the pointwise limit of the
internal metrics agrees with the intrinsic metric of the ambient limit. The candidate metric
must induce the original topology on the domain. -/
theorem internal_eq_of_tendsto_internal_on
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U)
    (E : C(U × U, ℝ)) (hE : LQGMetric.MetricGeometry.IsMetricFun E)
    (hEpt : Continuous (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE))
    (hEval : Continuous (metricFunSpaceValU E hE))
    (hlim : ∀ a b : U,
      Tendsto (fun n => ((Dn n).internal U a.1 b.1).toReal) atTop (𝓝 (E (a,b))))
    (u v : U) : D.internal U u.1 v.1 =
      LQGMetric.MetricGeometry.internalEDist Set.univ
        (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE u)
        (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE v) := by
  apply internal_eq_of_locally_eq_on D E hE hEpt hEval ?_ u v
  intro x
  obtain ⟨r, hr, hball, hevent⟩ :=
    eventually_internal_eq_on_small_ball Dn D hDn hconv hU x.2
  refine ⟨r, hr, fun a b ha hb => ?_⟩
  let S : ℝ := ‖a.1‖ + ‖b.1‖ + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have haS : a.1 ∈ Metric.closedBall (0 : Rd d) S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [S]; linarith [norm_nonneg b.1]
  have hbS : b.1 ∈ Metric.closedBall (0 : Rd d) S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [S]; linarith [norm_nonneg a.1]
  have hDab : Tendsto (fun n => (Dn n).1 (a.1,b.1)) atTop (𝓝 (D.1 (a.1,b.1))) :=
    (hconv S hS).tendsto_at ⟨haS,hbS⟩
  have heq : (fun n => ((Dn n).internal U a.1 b.1).toReal) =ᶠ[atTop]
      (fun n => (Dn n).1 (a.1,b.1)) := by
    filter_upwards [hevent] with n hn
    rw [hn a.1 ha b.1 hb, ENNReal.toReal_ofReal ((Dn n).nonneg a.1 b.1)]
  exact (tendsto_nhds_unique (hDab.congr' heq.symm) (hlim a b)).symm

end HigherDimLQGMetric

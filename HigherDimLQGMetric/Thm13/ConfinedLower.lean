import HigherDimLQGMetric.Thm13.FineChains
import HigherDimLQGMetric.Coord.ConfinedLower

/-!
# Confined lower semicontinuity for local metric edges

The lower bound for a local edge uses compactness of paths confined to a
Euclidean ball.  The generic coordinate path compactness theorem is applied
to the ordinary lengths of a sequence of continuous metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- On a compact set, a convergent sequence of continuous metrics has one
inverse modulus of continuity, including the finite initial segment. -/
theorem l8_common_inverse_modulus
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hconv : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    {K : Set (Rd d)} (hK : IsCompact K) {χ : ℝ} (hχ : 0 < χ) :
    ∃ b : ℝ, 0 < b ∧ ∀ n, ∀ u ∈ K, ∀ v ∈ K,
      (Dn n).1 (u,v) < b → dist u v < χ := by
  let S : Set (Rd d × Rd d) :=
    (K ×ˢ K) ∩ {p | χ ≤ dist p.1 p.2}
  have hS : IsCompact S :=
    (hK.prod hK).inter_right
      (isClosed_le continuous_const ((continuous_fst).dist continuous_snd))
  let F : Set C(Rd d × Rd d, ℝ) := insert D.1 (Set.range fun n => (Dn n).1)
  have hF : IsCompact F := hconv.isCompact_insert_range
  have hc : Continuous (fun q : C(Rd d × Rd d, ℝ) × (Rd d × Rd d) => q.1 q.2) :=
    continuous_eval
  have hpos : ∀ q ∈ F ×ˢ S, 0 < q.1 q.2 := by
    intro q hq
    have hne : q.2.1 ≠ q.2.2 := by
      intro heq
      have hs : χ ≤ dist q.2.1 q.2.2 := hq.2.2
      rw [heq, dist_self] at hs
      exact (not_le_of_gt hχ) hs
    rcases hq.1 with h | ⟨n, hn⟩
    · simpa [h] using D.apply_pos hne
    · simpa [← hn] using (Dn n).apply_pos hne
  obtain ⟨b, hb, hmin⟩ := (hF.prod hS).exists_forall_le' hc.continuousOn hpos
  refine ⟨b, hb, ?_⟩
  intro n u hu v hv hsmall
  by_contra hnot
  have hs : (u,v) ∈ S := ⟨⟨hu,hv⟩, le_of_not_gt hnot⟩
  have hbound : b ≤ (Dn n).1 (u,v) :=
    hmin ((Dn n).1, (u,v)) ⟨Or.inr ⟨n,rfl⟩, hs⟩
  exact (not_lt_of_ge hbound) hsmall

/-- Constant unit weight leaves the length measured by an arbitrary distance
function unchanged. -/
theorem l8_weightedLengthWith_one {X : Type*} (δ : X → X → ℝ≥0∞)
    (P : ℝ → X) {a b : ℝ} (hab : a ≤ b) :
    weightedLengthWith δ (fun _ => 1) P a b = curveLengthWith δ P a b := by
  have hlow := ofReal_mul_curveLengthWith_le_weightedLengthWith
    (δ := δ) (w := fun _ : X => 1) (P := P) hab (fun _ _ => le_rfl)
  have hupp := weightedLengthWith_le_ofReal_mul_curveLengthWith
    (δ := δ) (w := fun _ : X => 1) (P := P) (a := a) (b := b)
    (fun _ _ => le_rfl)
  simpa only [ENNReal.ofReal_one, one_mul] using le_antisymm hupp hlow

/-- The coordinate length associated to a continuous metric is its usual
curve length. -/
theorem l8_curveLengthWith_metric (D : ContMetric d) (P : ℝ → Rd d) (a b : ℝ) :
    curveLengthWith (fun u v => ENNReal.ofReal (D.1 (u,v))) P a b =
      D.len P a b := by
  have h := curveLengthWith_edist (D.pt ∘ P) a b
  convert h using 1
  · unfold curveLengthWith
    congr 1
    funext u v
    exact (D.edist_pt (P u) (P v)).symm
  · rfl

/-- Unit-weight confined coordinate distance is the ordinary internal
distance of a continuous metric. -/
theorem l8_weylDistOnWith_one (D : ContMetric d) (U : Set (Rd d)) (u v : Rd d) :
    weylDistOnWith (fun x y => ENNReal.ofReal (D.1 (x,y))) (fun _ => 1) U u v =
      D.internal U u v := by
  rw [D.internal_eq_iInf_len]
  unfold weylDistOnWith
  refine iInf_congr fun P => iInf_congr fun hc => iInf_congr fun h0 =>
    iInf_congr fun h1 => iInf_congr fun hU => ?_
  rw [l8_weightedLengthWith_one _ _ zero_le_one, l8_curveLengthWith_metric]

/-- A liminf of distances confined to a unit ball dominates the limiting
distance confined to the larger ball. This is the lower semicontinuity used
for the unbounded continuous perturbations in A21(4). -/
theorem l8_internal_liminf_ge_enlarged
    (Dn : ℕ → ContMetric d) (D : ContMetric d) (hD : D.IsLength)
    (hconv : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    (u v : Rd d) (hv : v ∈ Metric.ball u 1) :
    D.internal (Metric.ball u 2) u v ≤
      liminf (fun n => (Dn n).internal (Metric.ball u 1) u v) atTop := by
  let K : Set (Rd d) := Metric.closedBall u 1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hK12 : K ⊆ Metric.ball u 2 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hKfin : D.internal K u v ≠ ∞ := by
    have hfin := D.internal_ne_top_of_isPreconnected
      hD Metric.isOpen_ball (convex_ball u 1).isPreconnected
      (Metric.mem_ball_self (by norm_num)) hv
    exact ne_top_of_le_ne_top hfin
      (D.internal_anti Metric.ball_subset_closedBall u v)
  have hρ (n : ℕ) : IsCoordinate (fun p : Rd d × Rd d => (Dn n).1 p) := by
    exact ⟨⟨(Dn n).2.self_eq_zero, (Dn n).2.eq_of_eq_zero,
      (Dn n).2.symm, (Dn n).2.triangle⟩,
      (Dn n).continuous_pt, (Dn n).continuous_unpt⟩
  have huni : TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop (K ×ˢ K) :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv) _
      (hK.prod hK)
  have hmod : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      ∀ n, ∀ x ∈ K, ∀ y ∈ K, (Dn n).1 (x,y) < b → dist x y < χ :=
    fun χ hχ => l8_common_inverse_modulus Dn D hconv hK hχ
  have hWfin : weylDistOnWith
      (fun x y => ENNReal.ofReal (D.1 (x,y))) (fun _ => 1) K u v ≠ ∞ := by
    rw [l8_weylDistOnWith_one]
    exact hKfin
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop,
        D.internal (Metric.ball u 2) u v ≤
          (Dn n).internal (Metric.ball u 1) u v + ENNReal.ofReal ε := by
    have hevent := lemma25_moving_lower hK
      (fun n p => (Dn n).1 p) D.1 hρ huni hmod
      (fun _ => 1) continuous_const.continuousOn (fun _ _ => one_pos)
      (fun _ => u) (fun _ => v) u v tendsto_const_nhds tendsto_const_nhds
      hWfin hε
    filter_upwards [hevent] with n hn
    calc
      D.internal (Metric.ball u 2) u v ≤ D.internal K u v :=
        D.internal_anti hK12 u v
      _ = weylDistOnWith (fun x y => ENNReal.ofReal (D.1 (x,y)))
          (fun _ => 1) K u v := (l8_weylDistOnWith_one D K u v).symm
      _ ≤ weylDistOnWith (fun x y => ENNReal.ofReal ((Dn n).1 (x,y)))
          (fun _ => 1) K u v + ENNReal.ofReal ε := hn
      _ = (Dn n).internal K u v + ENNReal.ofReal ε := by
        rw [l8_weylDistOnWith_one]
      _ ≤ (Dn n).internal (Metric.ball u 1) u v + ENNReal.ofReal ε :=
        add_le_add ((Dn n).internal_anti Metric.ball_subset_closedBall u v) le_rfl
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hlim : D.internal (Metric.ball u 2) u v ≤
      liminf (fun n => (Dn n).internal (Metric.ball u 1) u v + ENNReal.ofReal (ε : ℝ)) atTop :=
    Filter.le_liminf_of_le (hf := by isBoundedDefault) (hbound ε hε)
  rw [liminf_add_const atTop
    (fun n => (Dn n).internal (Metric.ball u 1) u v) (ENNReal.ofReal (ε : ℝ))
    (by isBoundedDefault) (by isBoundedDefault)] at hlim
  simpa only [ENNReal.ofReal_coe_nnreal] using hlim

/-- Locality transfers the confined lower bound from a bounded perturbation
to an arbitrary continuous perturbation agreeing with it near this edge. -/
theorem l8_localEdge_ge_internal_of_local_bounded_limit
    {κ : Rd d → ℝ} (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (g : DistRd d) (f f' : C(Rd d, ℝ))
    (u v : Rd d) (hv : v ∈ Metric.ball u 1)
    (hff' : EqOn (⇑f) (⇑f') (Metric.ball u 2))
    (D : ContMetric d) (hD : D.IsLength)
    (hconv : Tendsto
      (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f')).1)
      atTop (𝓝 D.1)) :
    D.internal (Metric.ball u 2) u v ≤
      l8_localEdge hd hκ ξ εs hεs (addFun g f) u v := by
  rw [l8_localEdge_addFun_congr hd hκ ξ εs hεs hεt g f f' u v hff']
  exact l8_internal_liminf_ge_enlarged
    (fun n => l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f'))
    D hD hconv u v hv

end HigherDimLQGMetric

import HigherDimLQGMetric.Trap.Base

/-!
# Coordinates and their metric spaces

Packet S3. A coordinate `ρ` on a metric space `X` (M2a's `IsCoordinate`: a metric inducing the
topology of `X`) turns the type synonym `MetricFunSpace ρ _` into a metric space homeomorphic to
`X` by the identity. S1c's collapse and shortcut lemmas are stated for the distance of a metric
space; M2a's coordinate lemmas for a coordinate function on `X`. This file transports between the
two forms:

* `IsCoordinate.trapHomeomorph`: the identity homeomorphism `X ≃ₜ MetricFunSpace ρ _`;
* images of sets under `pt` (closure, frontier, openness, compactness);
* `trap_weylDistOnWith_eq`: `(w·ρ)_S(x, y)` computed in `X` equals the weighted distance of the
  metric space of `ρ`;
* the coordinate confinement sets `coordTrapSet` (`Y_r` measured with `ρ`) and their properties.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

section Transport

variable {X : Type*} [MetricSpace X] {ρ : X × X → ℝ}

/-- The identity homeomorphism from `X` to the metric space of a coordinate. -/
def IsCoordinate.trapHomeomorph (hρ : IsCoordinate ρ) : X ≃ₜ MetricFunSpace ρ hρ.metric where
  toFun := MetricFunSpace.pt ρ hρ.metric
  invFun := LQGMetric.metricFunSpaceVal ρ hρ.metric
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := hρ.pt_continuous
  continuous_invFun := hρ.val_continuous

theorem IsCoordinate.trapHomeomorph_apply (hρ : IsCoordinate ρ) (x : X) :
    hρ.trapHomeomorph x = MetricFunSpace.pt ρ hρ.metric x := rfl

omit [MetricSpace X] in
theorem trap_pt_image_eq_preimage (hρ : IsMetricFun ρ) (S : Set X) :
    MetricFunSpace.pt ρ hρ '' S = LQGMetric.metricFunSpaceVal ρ hρ ⁻¹' S :=
  congrFun (Set.image_eq_preimage_of_inverse (f := MetricFunSpace.pt ρ hρ)
    (g := LQGMetric.metricFunSpaceVal ρ hρ) (fun _ => rfl) (fun _ => rfl)) S

theorem IsCoordinate.trap_image_closure (hρ : IsCoordinate ρ) (S : Set X) :
    MetricFunSpace.pt ρ hρ.metric '' closure S = closure (MetricFunSpace.pt ρ hρ.metric '' S) :=
  hρ.trapHomeomorph.image_closure S

theorem IsCoordinate.trap_image_frontier (hρ : IsCoordinate ρ) (S : Set X) :
    MetricFunSpace.pt ρ hρ.metric '' frontier S = frontier (MetricFunSpace.pt ρ hρ.metric '' S) :=
  hρ.trapHomeomorph.image_frontier S

theorem IsCoordinate.trap_isOpen_image (hρ : IsCoordinate ρ) {S : Set X} (hS : IsOpen S) :
    IsOpen (MetricFunSpace.pt ρ hρ.metric '' S) :=
  hρ.trapHomeomorph.isOpen_image.2 hS

theorem IsCoordinate.trap_isCompact_image (hρ : IsCoordinate ρ) {S : Set X} (hS : IsCompact S) :
    IsCompact (MetricFunSpace.pt ρ hρ.metric '' S) :=
  hS.image hρ.pt_continuous

theorem IsCoordinate.trap_continuousOn_pt (hρ : IsCoordinate ρ) {P : ℝ → X} {s : Set ℝ}
    (hP : ContinuousOn P s) : ContinuousOn (MetricFunSpace.pt ρ hρ.metric ∘ P) s :=
  hρ.pt_continuous.comp_continuousOn hP

theorem IsCoordinate.trap_continuousOn_val (hρ : IsCoordinate ρ)
    {P : ℝ → MetricFunSpace ρ hρ.metric} {s : Set ℝ} (hP : ContinuousOn P s) :
    ContinuousOn (LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ P) s :=
  hρ.val_continuous.comp_continuousOn hP

omit [MetricSpace X] in
theorem trap_dist_pt (hρ : IsMetricFun ρ) (x y : X) :
    dist (MetricFunSpace.pt ρ hρ x) (MetricFunSpace.pt ρ hρ y) = ρ (x, y) := rfl

omit [MetricSpace X] in
theorem trap_edist_pt (hρ : IsMetricFun ρ) (x y : X) :
    edist (MetricFunSpace.pt ρ hρ x) (MetricFunSpace.pt ρ hρ y) = ENNReal.ofReal (ρ (x, y)) :=
  edist_dist _ _

omit [MetricSpace X] in
theorem IsMetricFun.trap_nonneg (hρ : IsMetricFun ρ) (x y : X) : 0 ≤ ρ (x, y) := by
  rw [← trap_dist_pt hρ]
  exact dist_nonneg

/-- **Weighted distances in the two forms agree.** -/
theorem trap_weylDistOnWith_eq (hρ : IsCoordinate ρ) (w : X → ℝ) (S : Set X) (x y : X) :
    weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w S x y =
      weylDistOn (w ∘ LQGMetric.metricFunSpaceVal ρ hρ.metric)
        (LQGMetric.metricFunSpaceVal ρ hρ.metric ⁻¹' S)
        (MetricFunSpace.pt ρ hρ.metric x) (MetricFunSpace.pt ρ hρ.metric y) := by
  apply le_antisymm
  · refine le_weylDistOn fun P hc h0 h1 hS => ?_
    have hc' : ContinuousOn (LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ P) (Icc 0 1) :=
      hρ.trap_continuousOn_val hc
    calc weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w S x y
        ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w
            (LQGMetric.metricFunSpaceVal ρ hρ.metric ∘ P) 0 1 :=
          weylDistOnWith_le hc' (by simp [h0]; rfl) (by simp [h1]; rfl) hS
      _ = weightedLength (w ∘ LQGMetric.metricFunSpaceVal ρ hρ.metric) P 0 1 := by
          rw [weightedLengthWith_metricFunSpace hρ.metric]
          rfl
  · simp only [weylDistOnWith, le_iInf_iff]
    intro P hc h0 h1 hS
    calc weylDistOn (w ∘ LQGMetric.metricFunSpaceVal ρ hρ.metric)
          (LQGMetric.metricFunSpaceVal ρ hρ.metric ⁻¹' S)
          (MetricFunSpace.pt ρ hρ.metric x) (MetricFunSpace.pt ρ hρ.metric y)
        ≤ weightedLength (w ∘ LQGMetric.metricFunSpaceVal ρ hρ.metric)
            (MetricFunSpace.pt ρ hρ.metric ∘ P) 0 1 :=
          weylDistOn_le (hρ.trap_continuousOn_pt hc) (by simp [h0]) (by simp [h1])
            (fun t ht => hS ht)
      _ = weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w P 0 1 :=
          (weightedLengthWith_metricFunSpace hρ.metric w P 0 1).symm

end Transport

section CoordSets

variable {X : Type*} [MetricSpace X] {ρ : X × X → ℝ}

/-- `Y_r` measured with the coordinate `ρ`: points of `closure A` within `ρ`-distance `r` of
`closure V`. -/
def coordTrapSet (hρ : IsMetricFun ρ) (A V : Set X) (r : ℝ) : Set X :=
  closure A ∩ {p | Metric.infDist (MetricFunSpace.pt ρ hρ p)
    (MetricFunSpace.pt ρ hρ '' closure V) ≤ r}

/-- `{p ∈ A : ρ-dist(p, closure V) < r}`. -/
def coordTrapOpen (hρ : IsMetricFun ρ) (A V : Set X) (r : ℝ) : Set X :=
  A ∩ {p | Metric.infDist (MetricFunSpace.pt ρ hρ p) (MetricFunSpace.pt ρ hρ '' closure V) < r}

variable {A V : Set X} {r r' : ℝ}

theorem IsCoordinate.isClosed_coordTrapSet (hρ : IsCoordinate ρ) :
    IsClosed (coordTrapSet hρ.metric A V r) :=
  isClosed_closure.inter (isClosed_le
    ((Metric.continuous_infDist_pt _).comp hρ.pt_continuous) continuous_const)

theorem IsCoordinate.isCompact_coordTrapSet (hρ : IsCoordinate ρ) (hAc : IsCompact (closure A)) :
    IsCompact (coordTrapSet hρ.metric A V r) :=
  hAc.of_isClosed_subset hρ.isClosed_coordTrapSet inter_subset_left

theorem IsCoordinate.isOpen_coordTrapOpen (hρ : IsCoordinate ρ) (hA : IsOpen A) :
    IsOpen (coordTrapOpen hρ.metric A V r) :=
  hA.inter (isOpen_lt ((Metric.continuous_infDist_pt _).comp hρ.pt_continuous) continuous_const)

theorem coordTrapSet_mono (hρ : IsMetricFun ρ) (h : r ≤ r') :
    coordTrapSet hρ A V r ⊆ coordTrapSet hρ A V r' :=
  fun _ hp => ⟨hp.1, hp.2.trans h⟩

theorem IsCoordinate.closure_coordTrapOpen_subset (hρ : IsCoordinate ρ) :
    closure (coordTrapOpen hρ.metric A V r) ⊆ coordTrapSet hρ.metric A V r :=
  closure_minimal (fun _ hp => ⟨subset_closure hp.1,
    show _ ≤ r from (show Metric.infDist _ _ < r from hp.2).le⟩) hρ.isClosed_coordTrapSet

theorem closure_subset_coordTrapSet (hρ : IsMetricFun ρ) (hVA : closure V ⊆ A) (hr : 0 ≤ r) :
    closure V ⊆ coordTrapSet hρ A V r := fun p hp =>
  ⟨subset_closure (hVA hp), show Metric.infDist _ _ ≤ r by
    rw [Metric.infDist_zero_of_mem (mem_image_of_mem _ hp)]; exact hr⟩

/-- A point within `ρ`-distance `r` of a point of `closure V`. -/
theorem infDist_pt_le (hρ : IsMetricFun ρ) {p q : X} (hq : q ∈ closure V) :
    Metric.infDist (MetricFunSpace.pt ρ hρ p) (MetricFunSpace.pt ρ hρ '' closure V) ≤ ρ (p, q) :=
  Metric.infDist_le_dist_of_mem (mem_image_of_mem _ hq)

theorem coordTrapSet_subset (hρ : IsMetricFun ρ) (hA : IsOpen A) (hVne : (closure V).Nonempty)
    {κ : ℝ} (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, κ ≤ ρ (x, y)) (hr : r < κ) :
    coordTrapSet hρ A V r ⊆ A := by
  intro p hp
  by_contra hpA
  have hfr : p ∈ frontier A := by
    rw [hA.frontier_eq]
    exact ⟨hp.1, hpA⟩
  have hle : κ ≤ Metric.infDist (MetricFunSpace.pt ρ hρ p) (MetricFunSpace.pt ρ hρ '' closure V) := by
    refine (Metric.le_infDist (hVne.image _)).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [trap_dist_pt, hρ.symm]
    exact hcol y hy p hfr
  exact absurd (hp.2.trans_lt hr) (not_lt.2 hle)

theorem coordTrapSet_subset_coordTrapOpen (hρ : IsMetricFun ρ) (hA : IsOpen A)
    (hVne : (closure V).Nonempty) {κ : ℝ} (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, κ ≤ ρ (x, y))
    (hr : r < κ) (hrr' : r < r') :
    coordTrapSet hρ A V r ⊆ coordTrapOpen hρ A V r' :=
  fun _ hp => ⟨coordTrapSet_subset hρ hA hVne hcol hr hp, hp.2.trans_lt hrr'⟩

/-- The coordinate confinement sets are the metric confinement sets of the coordinate's metric
space, read through the identity. -/
theorem IsCoordinate.pt_image_coordTrapSet (hρ : IsCoordinate ρ) (A V : Set X) (r : ℝ) :
    MetricFunSpace.pt ρ hρ.metric '' coordTrapSet hρ.metric A V r =
      trapSet (MetricFunSpace.pt ρ hρ.metric '' A) (MetricFunSpace.pt ρ hρ.metric '' V) r := by
  rw [trapSet, ← hρ.trap_image_closure, ← hρ.trap_image_closure]
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨mem_image_of_mem _ hp.1, hp.2⟩
  · rintro ⟨⟨p, hp, rfl⟩, hq⟩
    exact ⟨p, ⟨hp, hq⟩, rfl⟩

end CoordSets

end HigherDimLQGMetric

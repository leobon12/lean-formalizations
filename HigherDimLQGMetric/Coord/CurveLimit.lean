import HigherDimLQGMetric.Metric.Partition
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Curves under varying coordinate distances

The partition argument behind MA1 Lemma CC.  The distances are allowed to vary with the curve;
the hypothesis is convergence of each distance increment along the curves.  Compact convergence
of coordinates and uniform convergence of curves supply this hypothesis in applications.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

variable {X : Type*} {ι : Type*} {l : Filter ι} [l.NeBot]
  {δ : X → X → ℝ≥0∞} {δi : ι → X → X → ℝ≥0∞}
  {P : ℝ → X} {Pi : ι → ℝ → X} {a b : ℝ}

/-- Lower semicontinuity of length when every increment on a fixed partition converges. -/
theorem curveLengthWith_le_liminf_of_increment_tendsto
    (hinc : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      Tendsto (fun i => δi i (Pi i s) (Pi i t)) l (𝓝 (δ (P s) (P t)))) :
    curveLengthWith δ P a b ≤ liminf (fun i => curveLengthWith (δi i) (Pi i) a b) l := by
  unfold curveLengthWith
  refine partitionSup_le fun p => ?_
  have hsum : Tendsto (fun i => p.sum (fun s t => δi i (Pi i s) (Pi i t))) l
      (𝓝 (p.sum (fun s t => δ (P s) (P t)))) := by
    unfold IccPartition.sum
    apply tendsto_finsetSum
    intro k hk
    have hstep := p.step (Finset.mem_range.mp hk)
    exact hinc (p.t k) (p.t (k + 1)) hstep.1 hstep.2.1 hstep.2.2
  calc
    p.sum (fun s t => δ (P s) (P t)) =
        liminf (fun i => p.sum (fun s t => δi i (Pi i s) (Pi i t))) l :=
      hsum.liminf_eq.symm
    _ ≤ liminf (fun i => partitionSup (fun s t => δi i (Pi i s) (Pi i t)) a b) l :=
      Filter.liminf_le_liminf (Eventually.of_forall fun i => le_partitionSup p)

/-- MA1 Lemma CC's length inequality for a compact set on which the coordinates converge
uniformly.  The convergence of curves itself need only be pointwise for this step. -/
theorem curveLengthWith_le_liminf_of_uniform_coordinates
    {Y : Type*} [TopologicalSpace Y] {L : Set Y}
    {ρ : Y × Y → ℝ} {ρi : ι → Y × Y → ℝ}
    {Q : ℝ → Y} {Qi : ι → ℝ → Y} {u v : ℝ}
    (hρ : ContinuousOn ρ (L ×ˢ L))
    (hρi : TendstoUniformlyOn ρi ρ l (L ×ˢ L))
    (hQ : ∀ t ∈ Icc u v, Tendsto (fun i => Qi i t) l (𝓝 (Q t)))
    (hQL : ∀ t ∈ Icc u v, Q t ∈ L)
    (hQiL : ∀ i t, t ∈ Icc u v → Qi i t ∈ L) :
    curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) Q u v ≤
      liminf (fun i => curveLengthWith (fun x y => ENNReal.ofReal (ρi i (x, y))) (Qi i) u v) l := by
  apply curveLengthWith_le_liminf_of_increment_tendsto
  intro s t hus hst htv
  have hs : s ∈ Icc u v := ⟨hus, hst.trans htv⟩
  have ht : t ∈ Icc u v := ⟨hus.trans hst, htv⟩
  have hq : Tendsto (fun i => (Qi i s, Qi i t)) l (𝓝 (Q s, Q t)) :=
    (hQ s hs).prodMk_nhds (hQ t ht)
  have hq' : Tendsto (fun i => (Qi i s, Qi i t)) l (𝓝[L ×ˢ L] (Q s, Q t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq, Eventually.of_forall fun i =>
      ⟨hQiL i s hs, hQiL i t ht⟩⟩
  exact ENNReal.tendsto_ofReal
    (hρi.tendsto_comp (hρ (Q s, Q t) (⟨hQL s hs, hQL t ht⟩)) hq')

end HigherDimLQGMetric

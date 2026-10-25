import SupercriticalLQGUniqueness.B2.PfeAxioms.RadiusLiminf
import SupercriticalLQGUniqueness.B2.PfeAxioms.InternalRadius
import LQGMetric.Metric.InternalOps
import LQGMetric.Topo.Shortcut

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open LQGMetric.MetricGeometry

 
def FinitePathsEuclideanContinuous (D : LSCMetric) : Prop :=
  ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b → D.len P a b < ∞ →
    ContinuousOn P (Icc a b)

 

theorem finitePathsEuclideanContinuous_of_control (D : LSCMetric)
    (hcontrol : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, D (u, v) < ENNReal.ofReal η → dist u v < δ) :
    FinitePathsEuclideanContinuous D := by
  intro P a b hP _ t ht
  change Tendsto P (𝓝[Icc a b] t) (𝓝 (P t))
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨η, hη, hbound⟩ := hcontrol (P t) δ hδ
  have hmetric : Tendsto (D.pt ∘ P) (𝓝[Icc a b] t) (𝓝 (D.pt (P t))) :=
    hP.2 t ht
  have hev := hmetric.eventually
    (Metric.eball_mem_nhds (D.pt (P t)) (ENNReal.ofReal_pos.mpr hη))
  exact hev.mono fun u hu => hsub (Metric.mem_ball.mpr (by
    have hD : D (P t, P u) < ENNReal.ofReal η := by
      simpa only [Metric.mem_eball, Function.comp_apply, edist_comm,
        D.edist_pt] using hu
    simpa only [dist_comm] using hbound (P u) hD))

 

theorem metric_ball_subset_of_finitePathsEuclideanContinuous
    (D : LSCMetric) (hLen : D.IsLengthSpace)
    (hPath : FinitePathsEuclideanContinuous D)
    {Y : Set ℂ} (hY : IsOpen Y) {x : ℂ} (hx : x ∈ Y)
    {r : ℝ≥0∞} (hr : r < ⨅ b ∈ frontier Y, D (x, b)) :
    Metric.eball (D.pt x) r ⊆ D.pt '' Y := by
  intro y hy
  let v : ℂ := y
  have hxy : D (x, v) < r := by
    change edist (D.pt v) (D.pt x) < r at hy
    rwa [edist_comm, D.edist_pt] at hy
  have hrfin : r < ∞ := lt_of_lt_of_le hr le_top
  have hxyfin : D (x, v) < ∞ := hxy.trans hrfin
  obtain ⟨δ, hδ, hδr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hxy
  obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hLen x v hxyfin (δ : ℝ) (by exact_mod_cast hδ)
  have hlenr : D.len P a b < r := by
    have hlen' : D.len P a b ≤ D (x, v) + (δ : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using hlen
    exact hlen'.trans_lt hδr
  by_contra hv
  have hv' : v ∉ Y := by
    intro hvY
    exact hv ⟨v, hvY, rfl⟩
  have hPc : ContinuousOn P (Icc a b) := hPath P a b hP (hlenr.trans hrfin)
  let γ := LQGMetric.pathOfIcc P hP.1 hPc
  obtain ⟨t, ht⟩ := LQGMetric.MetricGeometry.exists_mem_frontier_of_path
    hY γ (by rw [ha]; exact hx) (by rw [hb]; exact hv')
  obtain ⟨s, hs, hPs⟩ := LQGMetric.range_pathOfIcc_subset P hP.1 hPc (mem_range_self t)
  have hfront : P s ∈ frontier Y := hPs ▸ ht
  have hxs : D (x, P s) ≤ D.len P a b := by
    rw [← ha, ← D.edist_pt]
    exact (edist_le_curveLength (D.pt ∘ P) hs.1).trans
      (curveLength_mono (D.pt ∘ P) le_rfl hs.2)
  have hboundary : (⨅ b ∈ frontier Y, D (x, b)) ≤ D (x, P s) :=
    iInf_le_of_le (P s) (iInf_le_of_le hfront le_rfl)
  exact (not_le_of_gt (hlenr.trans hr)) (hboundary.trans hxs)

 


theorem internal_eq_of_lt_frontier_distance
    (D : LSCMetric) (hLen : D.IsLengthSpace)
    (hPath : FinitePathsEuclideanContinuous D)
    {Y : Set ℂ} (hY : IsOpen Y) {x y : ℂ}
    (hx : x ∈ Y) (hy : y ∈ Y)
    {r : ℝ≥0∞} (hrfin : r < ∞)
    (hrfront : r < ⨅ b ∈ frontier Y, D (x, b))
    (hxy : D (x, y) < r) :
    D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) = D (x, y) :=
  internal_eq_of_metric_ball D hLen hrfin
    (metric_ball_subset_of_finitePathsEuclideanContinuous D hLen hPath hY hx hrfront)
    hxy hx hy

end SupercriticalLQGUniqueness.B2.PfeAxioms

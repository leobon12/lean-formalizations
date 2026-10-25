import SupercriticalLQGUniqueness.B2.PfeLocal.CircleLimit
import SupercriticalLQGUniqueness.B2.PfeLocal.Crossing

 





set_option autoImplicit false
noncomputable section

open Set LQGMetric.MetricGeometry
open Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 

theorem continuousOn_euclidean_of_small_metric (D : LSCMetric)
    (hsmall : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, D.1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (P : ℝ → ℂ) {a b : ℝ} (hP : D.IsCurve P a b) :
    ContinuousOn P (Icc a b) := by
  intro t ht
  change Tendsto P (𝓝[Icc a b] t) (𝓝 (P t))
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨η, hη, hclose⟩ := hsmall (P t) δ hδ
  have hD : Tendsto (fun s => D.1 (P t, P s)) (𝓝[Icc a b] t) (𝓝 0) := by
    have hD' := (tendsto_iff_edist_tendsto_0).mp (hP.2 t ht)
    change Tendsto (fun s => D.1 (P s, P t)) (𝓝[Icc a b] t) (𝓝 0) at hD'
    simpa only [D.isExtMetric.2.2.1] using hD'
  have hev : ∀ᶠ s in 𝓝[Icc a b] t,
      D.1 (P t, P s) < ENNReal.ofReal η :=
    hD.eventually (isOpen_Iio.mem_nhds (ENNReal.ofReal_pos.mpr hη))
  exact hev.mono fun s hs => by simpa only [dist_comm (P t)] using hclose (P s) hs

 



theorem setDistance_spheres_le_len (D : LSCMetric) (P : ℝ → ℂ)
    {a b r : ℝ} {x y : ℂ} (hP : D.IsCurve P a b)
    (hcont : ContinuousOn P (Icc a b))
    (ha : P a = x) (hb : P b = y) (hr : 0 < r)
    (hsep : 3 * r < dist x y) :
    Iface.setDistance D.1 (Metric.sphere x r) (Metric.sphere y r) ≤
      D.len P a b := by
  have hr2 : r < 2 * r := by linarith
  have hstart : dist (P a) x < r := by simpa [ha] using hr
  have hend : 2 * r < dist (P b) x := by
    rw [hb, dist_comm]
    linarith
  obtain ⟨σ, τ, haσ, hστ, hτb, hσx, -, -⟩ :=
    crossing_extract hP.1 hcont hr2 hstart hend
  have hσy : 2 * r < dist (P σ) y := by
    have htri : dist x y ≤ dist x (P σ) + dist (P σ) y := dist_triangle _ _ _
    rw [dist_comm x (P σ), hσx] at htri
    linarith
  have hlast : dist (P b) y < r := by simpa [hb] using hr
  have hcont' : ContinuousOn P (Icc σ b) :=
    hcont.mono (by
      intro t ht
      exact ⟨haσ.trans ht.1, ht.2⟩)
  obtain ⟨σ', τ', hσσ', hσ'τ', hτ'b, -, hτ'y, -⟩ :=
    crossing_extract_reverse (hστ.le.trans hτb) hcont' hr2 hσy hlast
  have hστ' : σ ≤ τ' := hσσ'.trans hσ'τ'.le
  have hlen : D.1 (P σ, P τ') ≤ D.len P a b := by
    calc
      D.1 (P σ, P τ') ≤ D.len P σ τ' := edist_le_len D P hστ'
      _ ≤ D.len P a b :=
        curveLength_mono (D.pt ∘ P) haσ hτ'b
  unfold Iface.setDistance
  exact (iInf_le_of_le (P σ) <|
    iInf_le_of_le (Metric.mem_sphere.mpr hσx) <|
      iInf_le_of_le (P τ') <|
        iInf_le_of_le (Metric.mem_sphere.mpr hτ'y) le_rfl).trans hlen

 

theorem setDistance_spheres_le_edist_of_geodesic (D : LSCMetric)
    (hsmall : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, D.1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo : ∀ u v : ℂ, D.1 (u, v) < ∞ →
      ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧ P a = u ∧ P b = v ∧
        D.len P a b = D.1 (u, v))
    {x y : ℂ} (hxy : D.1 (x, y) < ∞) {r : ℝ}
    (hr : 0 < r) (hsep : 3 * r < dist x y) :
    Iface.setDistance D.1 (Metric.sphere x r) (Metric.sphere y r) ≤
      D.1 (x, y) := by
  obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hgeo x y hxy
  calc
    Iface.setDistance D.1 (Metric.sphere x r) (Metric.sphere y r)
        ≤ D.len P a b := setDistance_spheres_le_len D P hP
          (continuousOn_euclidean_of_small_metric D hsmall P hP) ha hb hr hsep
    _ = D.1 (x, y) := hlen

 


theorem edist_le_of_sphere_distances (D D' : LSCMetric)
    (hsmall' : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, D'.1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo' : ∀ u v : ℂ, D'.1 (u, v) < ∞ →
      ∃ (P : ℝ → ℂ) (a b : ℝ), D'.IsCurve P a b ∧ P a = u ∧ P b = v ∧
        D'.len P a b = D'.1 (u, v))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hshr : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, r n < ε)
    (hcircle : ∀ (n : ℕ) (x y : ℂ),
      Iface.setDistance D.1 (Metric.sphere x (r n)) (Metric.sphere y (r n)) =
        Iface.setDistance D'.1 (Metric.sphere x (r n)) (Metric.sphere y (r n)))
    (x y : ℂ) : D.1 (x, y) ≤ D'.1 (x, y) := by
  by_contra hnot
  have hlt : D'.1 (x, y) < D.1 (x, y) := lt_of_not_ge hnot
  have hfinite : D'.1 (x, y) < ∞ := lt_of_lt_of_le hlt le_top
  have hxy : x ≠ y := by
    intro h
    subst y
    have hz : D.1 (x, x) = 0 := D.isExtMetric.1 x
    have hz' : D'.1 (x, x) = 0 := D'.isExtMetric.1 x
    rw [hz, hz'] at hlt
    exact (lt_irrefl (0 : ℝ≥0∞)) hlt
  have hdxy : 0 < dist x y := dist_pos.mpr hxy
  have hshrink : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        Metric.sphere x (r n) ⊆ Metric.ball x ε ∧
        Metric.sphere y (r n) ⊆ Metric.ball y ε := by
    intro ε hε
    filter_upwards [hshr ε hε] with n hn
    constructor
    · intro u hu
      rw [Metric.mem_sphere] at hu
      rw [Metric.mem_ball]
      rw [hu]
      exact hn
    · intro v hv
      rw [Metric.mem_sphere] at hv
      rw [Metric.mem_ball]
      rw [hv]
      exact hn
  have hlow := eventually_lt_setDistance_of_shrinking D
    (fun n => Metric.sphere x (r n)) (fun n => Metric.sphere y (r n)) x y
    (fun n => isCompact_sphere x (r n)) (fun n => isCompact_sphere y (r n))
    (fun n => NormedSpace.sphere_nonempty.2 (hr n).le)
    (fun n => NormedSpace.sphere_nonempty.2 (hr n).le)
    hshrink hlt
  have hsep : ∀ᶠ n in atTop, 3 * r n < dist x y := by
    filter_upwards [hshr (dist x y / 3) (by positivity)] with n hn
    linarith
  obtain ⟨n, hnlow, hnsep⟩ := (hlow.and hsep).exists
  have hupper := setDistance_spheres_le_edist_of_geodesic D' hsmall' hgeo'
    hfinite (hr n) hnsep
  rw [hcircle n x y] at hnlow
  exact (not_lt_of_ge hupper) hnlow

 

theorem lscMetric_eq_of_sphere_distances (D D' : LSCMetric)
    (hsmall : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, D.1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hsmall' : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, D'.1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo : ∀ u v : ℂ, D.1 (u, v) < ∞ →
      ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧ P a = u ∧ P b = v ∧
        D.len P a b = D.1 (u, v))
    (hgeo' : ∀ u v : ℂ, D'.1 (u, v) < ∞ →
      ∃ (P : ℝ → ℂ) (a b : ℝ), D'.IsCurve P a b ∧ P a = u ∧ P b = v ∧
        D'.len P a b = D'.1 (u, v))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hshr : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, r n < ε)
    (hcircle : ∀ (n : ℕ) (x y : ℂ),
      Iface.setDistance D.1 (Metric.sphere x (r n)) (Metric.sphere y (r n)) =
        Iface.setDistance D'.1 (Metric.sphere x (r n)) (Metric.sphere y (r n))) :
    D = D' := by
  apply Subtype.ext
  funext p
  rcases p with ⟨x, y⟩
  exact le_antisymm
    (edist_le_of_sphere_distances D D' hsmall' hgeo' r hr hshr hcircle x y)
    (edist_le_of_sphere_distances D' D hsmall hgeo r hr hshr
      (fun n u v => (hcircle n u v).symm) x y)

end SupercriticalLQGUniqueness.B2.PfeLocal

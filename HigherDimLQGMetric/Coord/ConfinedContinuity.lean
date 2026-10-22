import HigherDimLQGMetric.Coord.ConfinedLower

/-! # Endpoint continuity of a confined weighted distance -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

theorem confined_endpoint_connector_small
    {X : Type*} [MetricSpace X]
    (ρ : X × X → ℝ) (hρ : IsCoordinate ρ) (w : X → ℝ)
    {K O Y' : Set X} (hOY : closure O ⊆ Y')
    {M δloc : ℝ} (hM : 0 ≤ M) (hδloc : 0 < δloc)
    (hw : ∀ z ∈ closure O, w z ≤ M)
    (hlocal : ∀ a ∈ K, ∀ b ∈ K, ρ (a, b) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = a ∧ R 1 = b ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ (a, b)))
    (zseq : ℕ → X) (z : X) (hzseq : ∀ n, zseq n ∈ K) (hz : z ∈ K)
    (hconv : Tendsto zseq atTop (𝓝 z))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Y'
          (zseq n) z ≤ ENNReal.ofReal ε ∧
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Y'
          z (zseq n) ≤ ENNReal.ofReal ε := by
  have hρconv : Tendsto (fun n => ρ (zseq n, z)) atTop (𝓝 0) := by
    have hpair : Tendsto (fun n => (zseq n, z)) atTop (𝓝 (z, z)) :=
      hconv.prodMk_nhds tendsto_const_nhds
    simpa only [Function.comp_def, hρ.metric.self_eq_zero] using
      (hρ.continuous.tendsto (z, z)).comp hpair
  have hcostlim : Tendsto (fun n => ENNReal.ofReal (M * ρ (zseq n, z)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hρconv)
  have hcost : ∀ᶠ n in atTop,
      ENNReal.ofReal (M * ρ (zseq n, z)) ≤ ENNReal.ofReal ε :=
    (hcostlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).mono
      (fun n hn => hn.le)
  have hshort : ∀ᶠ n in atTop, ρ (zseq n, z) < δloc :=
    hρconv.eventually (gt_mem_nhds hδloc)
  filter_upwards [hcost, hshort] with n hc hs
  have hforward := confined_short_connector_bound ρ w hOY hM hw
    (hlocal (zseq n) (hzseq n) z hz hs)
  have hreverse := confined_short_connector_bound ρ w hOY hM hw
    (hlocal z hz (zseq n) (hzseq n) (by rwa [hρ.metric.symm]))
  refine ⟨hforward.trans hc, ?_⟩
  rw [hρ.metric.symm] at hreverse
  exact hreverse.trans hc

/-- The limiting confined weighted distance is continuous under moving
endpoints in the inner compact set, in the additive `ℝ≥0∞` form. -/
theorem confined_distance_endpoint_continuity
    {X : Type*} [MetricSpace X]
    (ρ : X × X → ℝ) (hρ : IsCoordinate ρ) (w : X → ℝ)
    {K O Y' : Set X} (hOY : closure O ⊆ Y')
    {M δloc : ℝ} (hM : 0 ≤ M) (hδloc : 0 < δloc)
    (hw : ∀ z ∈ closure O, w z ≤ M)
    (hlocal : ∀ a ∈ K, ∀ b ∈ K, ρ (a, b) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = a ∧ R 1 = b ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ (a, b)))
    (xn yn : ℕ → X) (x y : X)
    (hmem : ∀ n, xn n ∈ K ∧ yn n ∈ K) (hx : x ∈ K) (hy : y ∈ K)
    (hxn : Tendsto xn atTop (𝓝 x)) (hyn : Tendsto yn atTop (𝓝 y))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Y'
          (xn n) (yn n) ≤
        weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Y' x y +
          ENNReal.ofReal ε ∧
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Y' x y ≤
        weylDistOnWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Y'
          (xn n) (yn n) + ENNReal.ofReal ε := by
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hxsmall := confined_endpoint_connector_small ρ hρ w hOY hM hδloc hw
    hlocal xn x (fun n => (hmem n).1) hx hxn hη
  have hysmall := confined_endpoint_connector_small ρ hρ w hOY hM hδloc hw
    hlocal yn y (fun n => (hmem n).2) hy hyn hη
  let E : X → X → ℝ≥0∞ := fun u v => ENNReal.ofReal (ρ (u, v))
  let D : X → X → ℝ≥0∞ := weylDistOnWith E w Y'
  have htri := weylDistOnWith_triangle E (ofReal_metric_triangle hρ.metric) w Y'
  have hηsum : ENNReal.ofReal η + ENNReal.ofReal η = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hη.le hη.le]
    congr 1
    dsimp [η]
    ring
  filter_upwards [hxsmall, hysmall] with n hxs hys
  constructor
  · calc
      D (xn n) (yn n) ≤ D (xn n) x + D x (yn n) := htri _ _ _
      _ ≤ D (xn n) x + (D x y + D y (yn n)) :=
        add_le_add le_rfl (htri x y (yn n))
      _ ≤ ENNReal.ofReal η + (D x y + ENNReal.ofReal η) := by
        exact add_le_add hxs.1 (add_le_add le_rfl hys.2)
      _ = D x y + ENNReal.ofReal ε := by
        calc
          _ = D x y + (ENNReal.ofReal η + ENNReal.ofReal η) := by ac_rfl
          _ = _ := by rw [hηsum]
  · calc
      D x y ≤ D x (xn n) + D (xn n) y := htri _ _ _
      _ ≤ D x (xn n) + (D (xn n) (yn n) + D (yn n) y) :=
        add_le_add le_rfl (htri (xn n) (yn n) y)
      _ ≤ ENNReal.ofReal η + (D (xn n) (yn n) + ENNReal.ofReal η) := by
        exact add_le_add hxs.2 (add_le_add le_rfl hys.1)
      _ = D (xn n) (yn n) + ENNReal.ofReal ε := by
        calc
          _ = D (xn n) (yn n) + (ENNReal.ofReal η + ENNReal.ofReal η) := by ac_rfl
          _ = _ := by rw [hηsum]

end HigherDimLQGMetric

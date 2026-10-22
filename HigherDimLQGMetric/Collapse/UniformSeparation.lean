import HigherDimLQGMetric.Collapse.Clamped
import HigherDimLQGMetric.Collapse.UniformIntrinsic

/-! # Uniform separation of times on a collapsing geodesic -/

set_option autoImplicit false

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- A uniformly convergent sequence of curves cannot spend a macroscopic amount of
parameter time with vanishing ambient displacement when its limit is an intrinsic
unit-speed geodesic.  This is the short-excursion alternative to the source's
total off-tube arclength argument. -/
theorem uniform_time_separation {X : Type*} [MetricSpace X]
    {K : Set X} (hK : IsCompact K)
    (hKfin : ∀ p ∈ K, ∀ q ∈ K, internalEDist K p q ≠ ⊤)
    (hKcont : ContinuousOn (fun p : X × X => internalEDist K p.1 p.2) (K ×ˢ K))
    {T ℓ : ℝ} (hT : 0 ≤ T) (Q : Icc (0 : ℝ) T →ᵇ X)
    (hQK : ∀ t, Q t ∈ K)
    (hclamped : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t →
      (internalEDist K ((Set.IccExtend hT Q) s)
        ((Set.IccExtend hT Q) t)).toReal = min t ℓ - min s ℓ)
    {P : ℕ → ℝ → X} {L e : ℕ → ℝ}
    (hlim : TendstoUniformly (fun n (t : Icc (0 : ℝ) T) => P n t) Q atTop)
    (hL : Tendsto L atTop (𝓝 ℓ)) (he : Tendsto e atTop (𝓝 0))
    (hLT : ∀ n, L n ≤ T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s t, 0 ≤ s → s ≤ t → t ≤ L n →
        dist (P n s) (P n t) ≤ e n → t - s < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := intrinsic_uniform_small hK hKfin hKcont (ε / 2) (by positivity)
  have hδ4 : 0 < δ / 4 := by positivity
  have hδ2 : 0 < δ / 2 := by positivity
  have hmaxlim : Tendsto (fun n => max (L n - ℓ) 0) atTop (𝓝 0) := by
    simpa using (hL.sub_const ℓ).max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hclose := (Metric.tendstoUniformly_iff.mp hlim) (δ / 4) hδ4
  have heclose := he.eventually (eventually_lt_nhds hδ2)
  have hmaxclose := hmaxlim.eventually (eventually_lt_nhds (by positivity : 0 < ε / 2))
  filter_upwards [hclose, heclose, hmaxclose] with n hn hne hnmax s t hs hst htL hdist
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans htL |>.trans (hLT n)⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, htL.trans (hLT n)⟩
  have hdQQ : dist (Q ⟨s, hsT⟩) (Q ⟨t, htT⟩) < δ := by
    have htri : dist (Q ⟨s, hsT⟩) (Q ⟨t, htT⟩) ≤
        dist (Q ⟨s, hsT⟩) (P n s) + dist (P n s) (P n t) +
          dist (P n t) (Q ⟨t, htT⟩) := by
      calc
        dist (Q ⟨s, hsT⟩) (Q ⟨t, htT⟩)
            ≤ dist (Q ⟨s, hsT⟩) (P n s) + dist (P n s) (Q ⟨t, htT⟩) :=
          dist_triangle _ _ _
        _ ≤ dist (Q ⟨s, hsT⟩) (P n s) +
            (dist (P n s) (P n t) + dist (P n t) (Q ⟨t, htT⟩)) :=
          add_le_add_right (dist_triangle _ _ _) _
        _ = _ := by ring
    have hsclose := hn ⟨s, hsT⟩
    have htclose := hn ⟨t, htT⟩
    have hdist' := hdist
    rw [dist_comm] at htclose
    linarith
  have hdK : (internalEDist K ((Set.IccExtend hT Q) s)
      ((Set.IccExtend hT Q) t)).toReal < ε / 2 := by
    have h := hmod _ (hQK ⟨s, hsT⟩) _ (hQK ⟨t, htT⟩) hdQQ
    simpa only [Set.IccExtend_of_mem hT Q hsT,
      Set.IccExtend_of_mem hT Q htT] using h
  have hgap := time_gap_le_clamped_gap_add (ℓ := ℓ) hst htL
  rw [← hclamped s hsT t htT hst] at hgap
  linarith

end HigherDimLQGMetric

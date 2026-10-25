import SupercriticalLQGUniqueness.B2.PfeLocal.CircleMin

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 



theorem eventually_lt_setDistance_of_shrinking (D : LSCMetric)
    (A B : ℕ → Set ℂ) (z w : ℂ)
    (hA : ∀ n, IsCompact (A n)) (hB : ∀ n, IsCompact (B n))
    (hneA : ∀ n, (A n).Nonempty) (hneB : ∀ n, (B n).Nonempty)
    (hshrink : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, A n ⊆ ball z ε ∧ B n ⊆ ball w ε)
    {t : ℝ≥0∞} (ht : t < D.1 (z, w)) :
    ∀ᶠ n in atTop, t < Iface.setDistance D.1 (A n) (B n) := by
  have hopen : IsOpen {p : ℂ × ℂ | t < D.1 p} :=
    (lowerSemicontinuous_iff_isOpen_preimage.mp D.2.2) t
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ht)
  have hev := hshrink (δ / 2) (half_pos hδ)
  filter_upwards [hev] with n hn
  obtain ⟨u, hu, v, hv, hmin⟩ := setDistance_eq_at_min D (hA n) (hB n)
    (hneA n) (hneB n)
  rw [hmin]
  have huz : dist u z < δ / 2 := by
    exact mem_ball.mp (hn.1 hu)
  have hvw : dist v w < δ / 2 := by
    exact mem_ball.mp (hn.2 hv)
  apply hball
  rw [mem_ball, Prod.dist_eq]
  exact (max_lt huz hvw).trans_le (half_le_self hδ.le)

end SupercriticalLQGUniqueness.B2.PfeLocal

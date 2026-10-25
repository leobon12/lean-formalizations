import SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls.TraceChainGeom
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3
import LQGMetric.Metric.Geodesic




 





set_option autoImplicit false
noncomputable section
open Set LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls

 
theorem trace_dist_le_length (d : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    {x y : ℂ} (hx : x ∈ P '' Icc a b) (hy : y ∈ P '' Icc a b) :
    d (x, y) ≤ d.len P a b := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rcases le_total s t with hst | hts
  · change edist (d.pt (P s)) (d.pt (P t)) ≤
      curveLength (d.pt ∘ P) a b
    exact (edist_le_curveLength (d.pt ∘ P) hst).trans
      (curveLength_mono (d.pt ∘ P) hs.1 ht.2)
  · change edist (d.pt (P s)) (d.pt (P t)) ≤
      curveLength (d.pt ∘ P) a b
    rw [edist_comm]
    exact (edist_le_curveLength (d.pt ∘ P) hts).trans
      (curveLength_mono (d.pt ∘ P) ht.1 hs.2)

 
theorem setDist_lt_top_of_finite_trace_chain (d : LSCMetric)
    (n : ℕ) (P : ℕ → ℝ → ℂ) (a b : ℕ → ℝ)
    (hlen : ∀ i ≤ n, d.len (P i) (a i) (b i) < ⊤)
    (hmeet : ∀ i < n,
      ((P i '' Icc (a i) (b i)) ∩
       (P (i + 1) '' Icc (a (i + 1)) (b (i + 1)))).Nonempty)
    (K₁ K₂ : Set ℂ)
    (hfirst : (K₁ ∩ (P 0 '' Icc (a 0) (b 0))).Nonempty)
    (hlast : (K₂ ∩ (P n '' Icc (a n) (b n))).Nonempty) :
    OptimalConstants.Ratios.setDist d K₁ K₂ < ⊤ := by
  obtain ⟨x, hxK, hxP⟩ := hfirst
  have hreach : ∀ i ≤ n, ∃ y ∈ P i '' Icc (a i) (b i), d (x, y) < ⊤ := by
    intro i hi
    induction i with
    | zero =>
        exact ⟨x, hxP, by simp [d.isExtMetric.1 x]⟩
    | succ i ih =>
        obtain ⟨y, hy, hxy⟩ := ih (by omega)
        obtain ⟨z, hzi, hznext⟩ := hmeet i (by omega)
        have hyz : d (y, z) < ⊤ :=
          (trace_dist_le_length d (P i) hy hzi).trans_lt (hlen i (by omega))
        exact ⟨z, hznext,
          lt_of_le_of_lt (d.isExtMetric.2.2.2 x y z)
            (ENNReal.add_lt_top.mpr ⟨hxy, hyz⟩)⟩
  obtain ⟨y, hyK, hyP⟩ := hlast
  obtain ⟨z, hzP, hxz⟩ := hreach n le_rfl
  have hzy : d (z, y) < ⊤ :=
    (trace_dist_le_length d (P n) hzP hyP).trans_lt (hlen n le_rfl)
  have hxy : d (x, y) < ⊤ :=
    lt_of_le_of_lt (d.isExtMetric.2.2.2 x z y)
      (ENNReal.add_lt_top.mpr ⟨hxz, hzy⟩)
  exact (iInf₂_le_of_le x hxK (iInf₂_le_of_le y hyK le_rfl)).trans_lt hxy

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls

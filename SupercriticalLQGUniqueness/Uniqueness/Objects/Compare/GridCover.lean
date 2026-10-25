import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.CompareScale




 

set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Compare

private theorem exists_int_half_mesh {x a : ℝ} (ha : 0 < a) :
    ∃ m : ℤ, |x - a * m| ≤ a / 2 := by
  let m : ℤ := Int.floor (x / a + 1 / 2)
  have hlo : (m : ℝ) ≤ x / a + 1 / 2 := Int.floor_le _
  have hhi : x / a + 1 / 2 < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have hnormalized : |x / a - (m : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨m, ?_⟩
  have heq : x - a * (m : ℝ) = a * (x / a - (m : ℝ)) := by
    field_simp [ha.ne']
  rw [heq, abs_mul, abs_of_pos ha]
  nlinarith only [hnormalized, ha.le]

 

theorem exists_grid_near {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ∃ w ∈ Objects.CorrectedEvent.grid a, dist z w < a := by
  obtain ⟨m, hm⟩ := exists_int_half_mesh (x := z.re) ha
  obtain ⟨n, hn⟩ := exists_int_half_mesh (x := z.im) ha
  let w : ℂ := ((a * m : ℝ) : ℂ) + ((a * n : ℝ) : ℂ) * Complex.I
  have hw : w ∈ Objects.CorrectedEvent.grid a := ⟨m, n, rfl⟩
  have hcoord : (dist z w) ^ 2 = (z.re - a * m) ^ 2 + (z.im - a * n) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [w, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring
  have h1 : (z.re - a * m) ^ 2 ≤ (a / 2) ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_of_nonneg (by positivity : 0 ≤ a / 2)] using hm
  have h2 : (z.im - a * n) ^ 2 ≤ (a / 2) ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_of_nonneg (by positivity : 0 ≤ a / 2)] using hn
  have hdist : dist z w < a := by
    have hnonneg : 0 ≤ dist z w := dist_nonneg
    nlinarith only [hcoord, h1, h2, ha, hnonneg]
  exact ⟨w, hw, hdist⟩

 

theorem narrow_grid_acr_le_internal (D : LSCMetric)
    {U K S : Set ℂ} (p : U × U) {a s : ℝ}
    (hK : IsCompact K) (hUK : U ⊆ K)
    (ha : 0 < a) (hmesh : a ≤ s/4)
    (hfar : s + a < dist (p.1 : ℂ) (p.2 : ℂ))
    (hsite : (p.1 : ℂ) ∈ S) :
    ∃ v ∈ Objects.CorrectedEvent.grid a,
      Metric.infDist v S ≤ a ∧
      Objects.CorrectedEvent.acr D v (s/4) s ≤ D.internal U p := by
  obtain ⟨v, hvgrid, hvnear⟩ := exists_grid_near ha (p.1 : ℂ)
  have hvnear' : dist v (p.1 : ℂ) < a := by rwa [dist_comm]
  have hfirst : dist (p.1 : ℂ) v ≤ s/4 := hvnear.le.trans hmesh
  have hlast : s ≤ dist (p.2 : ℂ) v := by
    have htri := dist_triangle (p.1 : ℂ) v (p.2 : ℂ)
    rw [dist_comm v (p.2 : ℂ)] at htri
    linarith
  refine ⟨v, hvgrid, (Metric.infDist_le_dist_of_mem hsite).trans hvnear'.le, ?_⟩
  exact acr_le_internal_of_endpoint_order D hK hUK (by linarith) hfirst hlast


end SupercriticalLQGUniqueness.Uniqueness.Objects.Compare

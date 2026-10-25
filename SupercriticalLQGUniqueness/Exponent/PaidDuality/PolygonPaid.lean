import SupercriticalLQGUniqueness.Exponent.PaidDuality.AnnularRect
import SupercriticalLQGUniqueness.Exponent.PolygonCofinality




 






set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set
open scoped Convex ENNReal

 
def polygonEdges {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ι → ℕ) : Finset (Σ _ : ι, ℕ) :=
  s.sigma (fun i => Finset.range (n i))

 
def polygonFamilyTrace {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ) : Set ℂ :=
  ⋃ e ∈ polygonEdges s n, [v e.1 e.2 -[ℝ] v e.1 (e.2 + 1)]

 
theorem polygon_family_cost_eq_edges {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ)
    (ξ : ℝ) (f : ℂ → ℝ) :
    (∑ e ∈ polygonEdges s n,
      LQGMetric.LFPP.segCost ξ f (v e.1 e.2) (v e.1 (e.2 + 1))) =
      ∑ i ∈ s, LQGMetric.lfppLen ξ f
        (Exponent.PolygonCofinality.polygonPath (v i) (n i)) := by
  classical
  rw [polygonEdges, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  have hvertices : ∀ j ≤ n i, v i j ∈ (Set.univ : Set ℂ) := by simp
  have hcost := (Exponent.PolygonCofinality.polygonPath_data (ξ := ξ) (f := f) (S := Set.univ)
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)) (v i) (n i) hvertices).2.2
  simpa only [] using hcost.symm

 
theorem paid_central_rect_of_polygon_family {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ)
    (hadmitted : LQGMetric.Disconnects
      (polygonFamilyTrace s v n) innerSquare outerOpenSquareᶜ)
    (k : Fin 4) (ξ : ℝ) (f : ℂ → ℝ) :
    ∃ P : ℝ → ℂ,
      LQGMetric.DDDF.AdmPath (centralRect k).toSet
        (centralRect k).side₁ (centralRect k).side₂ P ∧
      LQGMetric.lfppLen ξ f P ≤
        ∑ i ∈ s, LQGMetric.lfppLen ξ f
          (Exponent.PolygonCofinality.polygonPath (v i) (n i)) := by
  let E := polygonEdges s n
  let a : (Σ _ : ι, ℕ) → ℂ := fun e => v e.1 e.2
  let b : (Σ _ : ι, ℕ) → ℂ := fun e => v e.1 (e.2 + 1)
  obtain ⟨P, hP, hcost⟩ :=
    paid_central_rect_of_annular_segment_family E a b hadmitted k ξ f
  exact ⟨P, hP, hcost.trans (polygon_family_cost_eq_edges s v n ξ f).le⟩

end SupercriticalLQGUniqueness.Exponent.PaidDuality


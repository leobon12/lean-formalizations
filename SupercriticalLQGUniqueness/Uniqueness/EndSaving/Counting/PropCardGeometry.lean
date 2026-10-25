import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.PropCardCore




 
set_option autoImplicit false
noncomputable section
open Set Finset
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting

def B4 (r : Set.Ioi (0 : ℝ)) (i : ℤ × ℤ) : Set ℂ :=
  Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))

def obstacles (b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) : Set ℂ :=
  K₁ ∪ K₂ ∪ Metric.sphere (0 : ℂ) b

private theorem disjoint_B4_of_not_neighbor (r : Set.Ioi (0 : ℝ))
    (i j : ℤ × ℤ) (h : i ∉ neighbors j) : Disjoint (B4 r i) (B4 r j) := by
  by_contra hn
  exact h (ball_overlap_mem_neighbors r i j hn)

 
theorem configuration_union_of_separated
    (r b : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (Z₀ Z₁ : Finset (ℤ × ℤ))
    (hcfg₀ : EndSaving.Interfaces.Configuration r b K₁ K₂ Z₀)
    (hgeom : ∀ i ∈ Z₁, Disjoint (B4 r i) (obstacles b K₁ K₂))
    (hfar : ∀ i ∈ Z₁, ∀ a ∈ Z₀, i ∉ neighbors a)
    (hsep : ∀ i ∈ Z₁, ∀ j ∈ Z₁, i ≠ j → i ∉ neighbors j) :
    EndSaving.Interfaces.Configuration r b K₁ K₂ (Z₀ ∪ Z₁) := by
  constructor
  · intro i hi j hj hij
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact hcfg₀.1 i hi j hj hij
      · exact (disjoint_B4_of_not_neighbor r j i (hfar j hj i hi)).symm
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact disjoint_B4_of_not_neighbor r i j (hfar i hi j hj)
      · exact disjoint_B4_of_not_neighbor r i j (hsep i hi j hj hij)
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hcfg₀.2 i hi
    · exact hgeom i hi

 
theorem disjoint_of_far (Z₀ Z₁ : Finset (ℤ × ℤ))
    (hfar : ∀ i ∈ Z₁, ∀ a ∈ Z₀, i ∉ neighbors a) :
    Disjoint Z₀ Z₁ := by
  apply Finset.disjoint_left.mpr
  intro i hi₀ hi₁
  exact hfar i hi₁ i hi₀ (self_mem_neighbors i)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting

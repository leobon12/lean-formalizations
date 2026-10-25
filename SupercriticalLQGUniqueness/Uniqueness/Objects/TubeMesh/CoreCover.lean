import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.SpineSep




 





set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

 

theorem finite_interior_cover {U : Set ℂ} (hbounded : Bornology.IsBounded U)
    {a : ℝ} (ha : 0 < a) :
    ∃ F : Finset U, ∀ y ∈ closure U,
      ∃ x ∈ F, dist y (x : ℂ) < a / 4 := by
  classical
  have hcompact : IsCompact (closure U) := hbounded.isCompact_closure
  have hcover : closure U ⊆ ⋃ x : U, ball (x : ℂ) (a / 4) := by
    intro y hy
    obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.mp hy (a / 4) (by linarith)
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa only [mem_ball] using hdist⟩
  obtain ⟨F, hF⟩ := hcompact.elim_finite_subcover
    (fun x : U => ball (x : ℂ) (a / 4))
    (fun _ => isOpen_ball) hcover
  refine ⟨F, ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (hF hy)
  exact ⟨x, hx, by simpa only [mem_ball] using hxy⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

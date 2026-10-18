import BouRabeeGwynne.FiniteDirichlet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace BouRabeeGwynne.MeshRates

open BouRabeeGwynne

/-- MR Lemma (Dirichlet principle and maximum principle), (8): on a finite network whose vertices
outside `A` play the role of `∂A`, if every vertex of `A` is joined to `∂A`, then for all boundary
values `g` there is a unique `u` equal to `g` off `A` and harmonic on `A`, and `u` lies between
the minimum and maximum of `g` on `∂A`. -/
theorem lemma8_dirichlet_maximum {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)
    (A : Set V) (haccess : N.BoundaryAccessible A) (g : V → ℝ) :
    ∃! u : V → ℝ, N.SolvesDirichlet A g u ∧
      (∀ M : ℝ, (∀ w, w ∉ A → g w ≤ M) → ∀ v, u v ≤ M) ∧
      (∀ M : ℝ, (∀ w, w ∉ A → M ≤ g w) → ∀ v, M ≤ u v) := by
  obtain ⟨u, hu, huniq⟩ := N.existsUnique_dirichlet A haccess g
  refine ⟨u, ⟨hu, ?_, ?_⟩, fun f hf => huniq f hf.1⟩
  · intro M hM
    exact N.maximum_principle A haccess u M (fun v hv => le_of_eq (hu.1 v hv).symm)
      (fun v hv => (hu.2 v hv).symm ▸ hM v hv)
  · intro M hM v
    have h := N.maximum_principle A haccess (-u) (-M)
      (fun v hv => by rw [N.laplacian_neg, hu.1 v hv, neg_zero])
      (fun w hw => by simp only [Pi.neg_apply, neg_le_neg_iff, hu.2 w hw]; exact hM w hw) v
    simpa using h

end BouRabeeGwynne.MeshRates

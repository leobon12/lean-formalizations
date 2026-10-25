import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.Mesh




 





set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

 

theorem tube_mesh (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams)
    (hP : P.Good) (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) :
    ∃ (ρ₀ : ℝ) (X : Finset ℂ),
      0 < ρ₀ ∧ ρ₀ ≤ C.A_set * C.r / 4 ∧ X.Nonempty ∧
      (∀ x ∈ X, closedBall x (2 * ρ₀) ⊆ P.tube C.r) ∧
      (∀ x ∈ X, ∀ y ∈ X,
        Relation.ReflTransGen
          (fun u v : ℂ => u ∈ X ∧ v ∈ X ∧ ρ₀ < dist u v ∧ dist u v < 2 * ρ₀) x y) ∧
      LQGMetric.Disconnects (⋃ x ∈ X, ball x ρ₀)
        (closedBall 0 (1.5 * C.r)) (ball 0 (2.5 * C.r))ᶜ ∧
      (∀ y ∈ closure (P.tube C.r), ∃ x ∈ X,
        dist y x ≤ C.A_set * C.r / 2) := by
  have hG1 := Objects.Tube.TubeParams.tube_open_bounded_pathConnected (P := P) (r := C.r) hP C.rPos
  have hG2 := (Objects.Tube.TubeParams.nbhd_and_thickening_subset_annulus (P := P) (r := C.r) (Asup := C.A_sup)
    hP C.rPos hSmall).1
  have hBounded : Bornology.IsBounded (P.tube C.r) :=
    (isBounded_ball (x := (0 : ℂ)) (r := 3 * C.r)).subset hG1.2.1
  have hAnn : P.tube C.r ⊆ LQGMetric.Blueprint.annulus 0 0 (3 * C.r) := by
    intro x hx
    have hxV : x ∈ P.nbhd C.r C.A_sup :=
      self_subset_thickening (mul_pos C.supPos C.rPos) _ hx
    have hb := hG2 hxV
    change 3 / 2 * C.r < ‖x‖ ∧ ‖x‖ < 5 / 2 * C.r at hb
    change (0 : ℝ) < ‖x - 0‖ ∧ ‖x - 0‖ < 3 * C.r
    simp only [sub_zero]
    constructor <;> nlinarith [C.rPos]
  exact finite_connected_mesh hG1.1 hBounded hG1.2.2 hAnn
    (P.spine C.r) (Objects.Tube.TubeParams.range_spine_subset_tube hP C.rPos)
    (spine_disconnects_mesh_targets C P hP hSmall)
    (mul_pos C.setPos C.rPos)


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

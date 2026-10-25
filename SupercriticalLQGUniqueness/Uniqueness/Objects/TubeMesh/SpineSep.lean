import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.SelectedParams




 






set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

 
theorem spine_disconnects_mesh_targets (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams)
    (hP : P.Good) (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ) :
    LQGMetric.Disconnects (range (P.spine C.r))
      (closedBall 0 (1.5 * C.r)) (ball 0 (2.5 * C.r))ᶜ := by
  have hG2 := (Objects.Tube.TubeParams.nbhd_and_thickening_subset_annulus (P := P) (r := C.r) (Asup := C.A_sup)
    hP C.rPos hSmall).1
  have hsp : ∀ t, P.spine C.r t ∈ P.nbhd C.r C.A_sup := by
    intro t
    exact self_subset_thickening (mul_pos C.supPos C.rPos) _
      (Objects.Tube.TubeParams.spine_mem_tube hP C.rPos t)
  exact Objects.TubeLoops.loop_disconnects _ (Objects.Tube.TubeParams.spine_closed hP)
    (Objects.Tube.TubeParams.spine_ne_zero hP C.rPos)
    (by rw [Objects.Tube.TubeParams.spine_loopDeg hP C.rPos]; norm_num)
    (fun t => by norm_num; exact (hG2 (hsp t)).1)
    (fun t => by norm_num; exact (hG2 (hsp t)).2)

 
theorem mesh_separator_of_spine_cover (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams)
    (hP : P.Good) (hSmall : 100 * C.A_sup ≤ P.sp * P.ρ)
    (X : Finset ℂ) (rho0 : ℝ)
    (hcover : range (P.spine C.r) ⊆ ⋃ x ∈ X, ball x rho0) :
    LQGMetric.Disconnects (⋃ x ∈ X, ball x rho0)
      (closedBall 0 (1.5 * C.r)) (ball 0 (2.5 * C.r))ᶜ :=
  (spine_disconnects_mesh_targets C P hP hSmall).mono hcover le_rfl le_rfl


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

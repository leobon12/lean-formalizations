import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.TubeMesh




 






set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

 

theorem exists_dataMatch (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams)
    (S : TubeSelection C P) (hSupNar : C.A_sup < C.A_nar) :
    ∃ (ρ₀ : ℝ) (X : Finset ℂ),
      Objects.CorrectedEvent.DataMatch C
        (Objects.TubeBridge.tubeDataOf C P S.good (S.small hSupNar).1 ρ₀ X) := by
  let hP : P.Good := S.good
  let hSmall : 100 * C.A_sup ≤ P.sp * P.ρ := (S.small hSupNar).1
  obtain ⟨ρ₀, X, hρ₀, hρ₀le, hX, hM1, hM2, hM3, hM4⟩ :=
    tube_mesh C P hP hSmall
  let T := Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X
  have hTube : Objects.CorrectedEvent.tubeSet T = P.tube C.r :=
    Objects.TubeBridge.tubeDataOf_tubeSet_eq C P hP hSmall ρ₀ X S.widthEq
  have hM1' : ∀ x ∈ X, closedBall x (2 * ρ₀) ⊆ Objects.CorrectedEvent.tubeSet T := by
    intro x hx
    rw [hTube]
    exact hM1 x hx
  have hM4' : ∀ y ∈ closure (Objects.CorrectedEvent.tubeSet T),
      ∃ x ∈ X, dist y x ≤ C.A_set * C.r / 2 := by
    intro y hy
    rw [hTube] at hy
    exact hM4 y hy
  have hMol := Objects.TubeBridge.tubeDataOf_mollifier_props C P hP hSmall ρ₀ X
  have hShape := Objects.TubeBridge.tubeDataOf_bump_shape C P hP hSmall ρ₀ X S.widthEq
  have hFormula := Objects.TubeBridge.tubeDataOf_bump_formula C P hP hSmall ρ₀ X S.widthEq
  have hBlock := S.blockRadius_bounds
  refine ⟨ρ₀, X, ?_⟩
  unfold Objects.CorrectedEvent.DataMatch
  change T.r = C.r ∧ T.rho = C.ρ ∧ T.lambda = C.lamConst ∧
    T.A_endpt = C.A_endpt ∧ T.alpha = C.K_ann ∧
    T.K = Nat.ceil (C.lamConst / (C.A_loc * C.ρ)) ∧
    T.orientation ^ 4 = 1 ∧
    T.psiU ∈ Icc (-Real.pi/2) (Real.pi/2) ∧
    T.psiV ∈ Icc (-Real.pi/2) (Real.pi/2) ∧
    C.A_endpt*C.ρ*C.r ≤ T.blockRadius ∧
    T.blockRadius ≤ Real.sqrt C.A_endpt*C.ρ*C.r ∧
    0 < T.netRadius ∧ T.netRadius ≤ C.A_set*C.r/4 ∧
    T.netSites.Nonempty ∧
    (∀ x ∈ T.netSites, closedBall x (2*T.netRadius) ⊆ Objects.CorrectedEvent.tubeSet T) ∧
    (∀ x ∈ T.netSites, ∀ y ∈ T.netSites,
      Relation.ReflTransGen
        (fun u v : ℂ => u ∈ T.netSites ∧ v ∈ T.netSites ∧
          T.netRadius < dist u v ∧ dist u v < 2*T.netRadius) x y) ∧
    LQGMetric.Disconnects
      (⋃ x ∈ T.netSites, ball x T.netRadius)
      (closedBall 0 (1.5*C.r)) (ball 0 (2.5*C.r))ᶜ ∧
    (∀ y ∈ closure (Objects.CorrectedEvent.tubeSet T),
      ∃ x ∈ T.netSites, dist y x ≤ C.A_set*C.r/2) ∧
    (∀ x, 0 ≤ T.mollifier x) ∧
    (∀ x, C.A_sup*C.r/4 ≤ dist x 0 → T.mollifier x = 0) ∧
    (∫ x : ℂ, T.mollifier x) = 1 ∧
    (∀ x, T.bump x = Objects.CorrectedEvent.bumpFormula T C.A_max C.A_sup x) ∧
    (∀ x, 0 ≤ T.bump x ∧ T.bump x ≤ C.A_max) ∧
    (∀ x ∈ closure (Objects.CorrectedEvent.tubeSet T), T.bump x = C.A_max) ∧
    (∀ x ∉ Objects.CorrectedEvent.tubeV T C.A_sup, T.bump x = 0)
  exact ⟨rfl, S.rhoEq, rfl, rfl, S.alphaEq, S.countEq,
    S.orientFourth, (by simpa only [T, Objects.TubeBridge.tubeDataOf, neg_div] using S.angleU),
    (by simpa only [T, Objects.TubeBridge.tubeDataOf, neg_div] using S.angleV),
    hBlock.1, hBlock.2, hρ₀, hρ₀le, hX,
    hM1', hM2, hM3, hM4', hMol.1, hMol.2.1, hMol.2.2,
    hFormula, hShape.1, hShape.2.1, hShape.2.2⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

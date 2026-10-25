import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.DataMatch




 






set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

 

theorem exists_selected_tube_inputs (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams)
    (S : TubeSelection C P) (hSupNar : C.A_sup < C.A_nar) :
    ∃ (ρ₀ : ℝ) (X : Finset ℂ),
      let hP := S.good
      let hSmall := (S.small hSupNar).1
      let T := Objects.TubeBridge.tubeDataOf C P hP hSmall ρ₀ X
      Objects.CorrectedEvent.DataMatch C T ∧
      Objects.CorrectedEvent.tubeSet T ⊆
        (Objects.CentreZero.uZero P hP C.r C.A_sup C.rPos C.supPos hSmall : Set ℂ) ∧
      Objects.CorrectedEvent.tubeSet T ⊆ ball 0 (2.5 * C.r) ∧
      Objects.CentreZero.fZero P hP C.r C.A_sup C.A_max C.rPos C.supPos hSmall = T.bump := by
  obtain ⟨ρ₀, X, hData⟩ := exists_dataMatch C P S hSupNar
  refine ⟨ρ₀, X, hData, ?_, ?_, ?_⟩
  · exact Objects.TubeBridge.tubeDataOf_tube_sub C P S.good (S.small hSupNar).1
      ρ₀ X S.widthEq
  · exact Objects.TubeBridge.tubeDataOf_tube_middle C P S.good (S.small hSupNar).1
      ρ₀ X S.widthEq
  · exact Objects.TubeBridge.fZero_eq_tubeDataOf_bump C P S.good
      (S.small hSupNar).1 ρ₀ X

 

theorem boundsAt_of_selected_mesh
    (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams)
    (S : TubeSelection C P) (hSupNar : C.A_sup < C.A_nar)
    (ρ₀ : ℝ) (X : Finset ℂ)
    (hData : Objects.CorrectedEvent.DataMatch C
      (Objects.TubeBridge.tubeDataOf C P S.good (S.small hSupNar).1 ρ₀ X))
    {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (hEvent : Objects.CorrectedEvent.correctedEvent C
      (Objects.TubeBridge.tubeDataOf C P S.good (S.small hSupNar).1 ρ₀ X) hData F D D' g)
    (hL : (D g).IsLengthSpace) (hForget : Continuous (BiLipschitz.Barrier.forget (D g)))
    (hInner : Objects.CorrectedEvent.ambientAcross (D g) 0 C.r (1.5 * C.r) =
      Objects.CorrectedEvent.acr (D g) 0 C.r (1.5 * C.r))
    (hOuter : Objects.CorrectedEvent.ambientAcross (D g) 0 (2.5 * C.r) (3 * C.r) =
      Objects.CorrectedEvent.acr (D g) 0 (2.5 * C.r) (3 * C.r))
    (hEucl : ∀ (γ : ℝ → ℂ) (a b : ℝ),
      (D g).IsCurve γ a b → (D g).len γ a b < ∞ → ContinuousOn γ (Icc a b))
    {par : EndSaving.Interfaces.Parameters ⟨C.ξ, C.ξPos⟩}
    (hAcross : par.Cacross = C.A_across)
    (hAround : par.Caround = C.A_around)
    (hCt : par.Ctube = C.A_internal) :
    Objects.Producer.BoundsAt D ⟨C.ξ, C.ξPos⟩ C.Q par 0 ⟨C.r, C.rPos⟩
      (Objects.CentreZero.uZero P S.good C.r C.A_sup C.rPos C.supPos (S.small hSupNar).1)
      (Objects.CentreZero.vZero P S.good C.r C.A_sup C.rPos C.supPos (S.small hSupNar).1) g := by
  exact Objects.TubeBridge.boundsAt_of_identified_tube hEvent P S.good ⟨C.r, C.rPos⟩
    rfl rfl rfl rfl rfl rfl rfl rfl S.widthEq (S.small hSupNar).1
    hL hForget hInner hOuter hEucl rfl rfl rfl hAcross hAround hCt


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly.TubeSelection
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh.Consumers




 
set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly

 

theorem exists_tube_data {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (t : Objects.Density.T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    ∃ (ρ₀ : ℝ) (X : Finset ℂ),
      let C := t.toConstants r
      let P := tubeParams t
      let S := tubeSelection t r
      let T := Objects.TubeBridge.tubeDataOf C P S.good (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X
      Objects.CorrectedEvent.DataMatch C T ∧
      Objects.CorrectedEvent.tubeSet T ⊆
        (Objects.CentreZero.uZero P S.good C.r C.A_sup C.rPos C.supPos
          (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 : Set ℂ) ∧
      Objects.CorrectedEvent.tubeSet T ⊆ ball 0 (2.5 * C.r) ∧
      Objects.CentreZero.fZero P S.good C.r C.A_sup C.A_max C.rPos C.supPos
        (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 = T.bump := by
  exact Objects.TubeMesh.exists_selected_tube_inputs (t.toConstants r) (tubeParams t)
    (tubeSelection t r) (t.sup_lt_set.trans t.set_lt_nar)

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly

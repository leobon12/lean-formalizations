import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.ExcursionCode
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces




 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes

theorem excursionRelation_iff_endSavingExcursion (O : Set ℂ)
    (V : TopologicalSpace.Opens ℂ) (p : ExcursionInput) :
    ExcursionRelation O (V : Set ℂ) p ↔
      EndSaving.Interfaces.Excursion p.1 (p.2 0) O V
        (p.2 1) (p.2 2) (p.2 3) (p.2 4) := by
  rfl

 

theorem endSavingExcursion_borel (O : Set ℂ) (hO : IsOpen O)
    (V : TopologicalSpace.Opens ℂ) :
    MeasurableSet {p : ExcursionInput |
      EndSaving.Interfaces.Excursion p.1 (p.2 0) O V
        (p.2 1) (p.2 2) (p.2 3) (p.2 4)} := by
  convert excursionRelation_borel (V := (V : Set ℂ)) hO using 1
  ext p
  exact (excursionRelation_iff_endSavingExcursion O V p).symm


end SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes

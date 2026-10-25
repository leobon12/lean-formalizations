import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.RawHitsMeas
import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.InterfaceBridge




 





set_option autoImplicit false
noncomputable section
open Set MeasureTheory unitInterval
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

private def unitClamp : C(ℝ, unitInterval) :=
  ⟨fun t => projIcc 0 1 zero_le_one t, continuous_projIcc⟩

def unitExtension (R : Measurability.GeodesicCodes.Path) : Measurability.GeodesicCodes.RealPath :=
  R.comp unitClamp

theorem continuous_unitExtension : Continuous unitExtension :=
  ContinuousMap.continuous_precomp unitClamp

 
abbrev UnitExcursionInput := Measurability.GeodesicCodes.Path × (Fin 5 → ℝ)

private def excursionInput (p : UnitExcursionInput) : Measurability.GeodesicCodes.ExcursionInput :=
  (unitExtension p.1, p.2)

private theorem measurable_excursionInput : Measurable excursionInput := by
  have hpath : Measurable (fun p : UnitExcursionInput => unitExtension p.1) :=
    continuous_unitExtension.measurable.comp measurable_fst
  exact hpath.prodMk measurable_snd

 
def UnitExcursion (O : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (p : UnitExcursionInput) : Prop :=
  p.2 0 = 1 ∧ EndSaving.Interfaces.Excursion (unitExtension p.1) (p.2 0) O V
    (p.2 1) (p.2 2) (p.2 3) (p.2 4)

theorem unitExcursion_borel (O : Set ℂ) (hO : IsOpen O)
    (V : TopologicalSpace.Opens ℂ) :
    MeasurableSet {p : UnitExcursionInput | UnitExcursion O V p} := by
  have htime : MeasurableSet {p : UnitExcursionInput | p.2 0 = (1 : ℝ)} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const
  have h := htime.inter
    ((Measurability.GeodesicCodes.endSavingExcursion_borel O hO V).preimage measurable_excursionInput)
  convert h using 1
  ext p
  rfl

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

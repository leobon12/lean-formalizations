import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.CompactPointCost




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory unitInterval
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

def excursionInternalProxy (W : Set ℂ) (p : LSCMetric × UnitExcursionInput) : ℝ≥0∞ :=
  openInternalProxy W
    (p.1, ((unitExtension p.2.1) (p.2.2 2),
      (unitExtension p.2.1) (p.2.2 3)))

private theorem excursionEval_measurable (i : Fin 5) :
    Measurable (fun p : LSCMetric × UnitExcursionInput =>
      (unitExtension p.2.1) (p.2.2 i)) := by
  have hpath : Measurable (fun p : LSCMetric × UnitExcursionInput =>
      unitExtension p.2.1) :=
    continuous_unitExtension.measurable.comp (measurable_fst.comp measurable_snd)
  have htime : Measurable (fun p : LSCMetric × UnitExcursionInput => p.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact continuous_eval.measurable.comp (hpath.prodMk htime)

theorem excursionInternalProxy_measurable {W : Set ℂ}
    (hWc : IsCompact (closure W)) :
    Measurable (excursionInternalProxy W) := by
  have harg : Measurable (fun p : LSCMetric × UnitExcursionInput =>
      (p.1, ((unitExtension p.2.1) (p.2.2 2),
        (unitExtension p.2.1) (p.2.2 3)))) :=
    measurable_fst.prodMk ((excursionEval_measurable 2).prodMk
      (excursionEval_measurable 3))
  exact (openInternalProxy_measurable hWc).comp harg

theorem excursionInternalProxy_eq_internal_of_scaled
    (D : LSCMetric) (hforget : Continuous (Measurability.SetGeodesicCodes.euclidForget D))
    {W : Set ℂ} (hW : IsOpen W) (hWne : Wᶜ.Nonempty)
    (P : ℝ → ℂ) (T : ℝ) (R : Measurability.GeodesicCodes.Path) (hT : 0 < T)
    (hscaled : ∀ q : unitInterval, R q = P (T * (q : ℝ)))
    (a b c d : ℝ) (hb : b ∈ Icc 0 T) (hc : c ∈ Icc 0 T)
    (hPb : P b ∈ W) (hPc : P c ∈ W) :
    excursionInternalProxy W
      (D, (R, normalizedExcursionTimes T a b c d)) =
      D.internal W (⟨P b, hPb⟩, ⟨P c, hPc⟩) := by
  have hEq := scaled_unitExtension_eq_source P T R hT hscaled
  have hbc : (unitExtension R) (b / T) = P b := hEq hb
  have hcc : (unitExtension R) (c / T) = P c := hEq hc
  change openInternalProxy W
    (D, ((unitExtension R) (b / T), (unitExtension R) (c / T))) = _
  rw [hbc, hcc]
  exact openInternalProxy_eq_internal D hforget hW hWne
    ⟨P b, hPb⟩ ⟨P c, hPc⟩

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

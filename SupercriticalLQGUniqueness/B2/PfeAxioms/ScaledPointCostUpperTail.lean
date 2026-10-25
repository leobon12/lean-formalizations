import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledPointCostLaw

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.DDDF LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem scaled_point_cost_upper_tail
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (U : TopologicalSpace.Opens ℂ) (hUc : IsConnected (U : Set ℂ))
    (x y : ℂ) (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (δ : Ioo (0 : ℝ) 1) (r : ℝ), 0 < r →
        P {ω | ENNReal.ofReal M <
          ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
            crossLenIn (ξ : ℝ)
              (heatMollify (δ : ℝ) (fieldScale r (h ω))) U {x} {y}} ≤
          ENNReal.ofReal η := by
  let : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  have hhCan := normalized_canonical_model.2
  have hb := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hhCan.1
  let E (t : Ioi (0 : ℝ)) := exists_heatVersion_bdd hb t
  let X (t : Ioi (0 : ℝ)) : DistC → C(ℂ, ℝ) := (E t).choose
  have hX : ∀ t, IsHeatSmoothing normGFFLaw id t (X t) :=
    fun t => (E t).choose_spec.2
  have hT := (hS ξ Q hQ m hm).1 normGFFLaw id hhCan X hX U hUc x y hx hy hxy
  intro η hη
  obtain ⟨M, hM, hTail⟩ := hT.2 η hη
  refine ⟨M, hM, ?_⟩
  intro δ r hr
  let F : DistC → ℝ≥0∞ := fun g =>
    ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
      crossLenIn (ξ : ℝ) (heatMollify (δ : ℝ) g) U {x} {y}
  have hf : AEMeasurable F normGFFLaw :=
    aemeasurable_canonical_normalized_crossLenIn hS ξ Q hQ m hm
      δ U hUc x y hx hy hxy
  have hLaw : P.map (fun ω => F (fieldScale r (h ω))) = normGFFLaw.map F := by
    have hfP : AEMeasurable F (P.map h) := by
      simpa only [← normGFFLaw_eq_of_normalized P h hh] using hf
    calc
      P.map (fun ω => F (fieldScale r (h ω))) =
          P.map (fun ω => F (h ω)) :=
        map_canonical_observable_fieldScale P h hh F hf hr
      _ = (P.map h).map F :=
        (AEMeasurable.map_map_of_aemeasurable hfP hh.1.measurable.aemeasurable).symm
      _ = normGFFLaw.map F := by rw [normGFFLaw_eq_of_normalized P h hh]
  have hScaleMeas : AEMeasurable (fun ω => F (fieldScale r (h ω))) P := by
    have hLawField : P.map (fun ω => fieldScale r (h ω)) = normGFFLaw := by
      rw [map_fieldScale
        (SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh)
        hr]
      exact (normGFFLaw_eq_of_normalized P h hh).symm
    have hf' : AEMeasurable F (P.map fun ω => fieldScale r (h ω)) := by
      simpa only [hLawField] using hf
    exact hf'.comp_aemeasurable
      (isWholePlaneGFF_fieldScale hh.1 hr).measurable.aemeasurable
  have hLawEvent :
      P {ω | ENNReal.ofReal M < F (fieldScale r (h ω))} =
        normGFFLaw {g | ENNReal.ofReal M < F g} := by
    calc
      P {ω | ENNReal.ofReal M < F (fieldScale r (h ω))} =
          (P.map (fun ω => F (fieldScale r (h ω)))) (Ioi (ENNReal.ofReal M)) :=
        (Measure.map_apply_of_aemeasurable hScaleMeas measurableSet_Ioi).symm
      _ = (normGFFLaw.map F) (Ioi (ENNReal.ofReal M)) := by rw [hLaw]
      _ = normGFFLaw {g | ENNReal.ofReal M < F g} :=
        Measure.map_apply_of_aemeasurable hf measurableSet_Ioi
  have hEq : ∀ᵐ g ∂normGFFLaw,
      F g = ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
        crossLenIn (ξ : ℝ) (X ⟨(δ : ℝ), δ.property.1⟩ g) U {x} {y} := by
    filter_upwards [(E ⟨(δ : ℝ), δ.property.1⟩).choose_spec.1] with g hg
    dsimp [F]
    congr 1
    congr 1
    funext z
    exact (hg z).symm
  calc
    P {ω | ENNReal.ofReal M <
        ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
          crossLenIn (ξ : ℝ)
            (heatMollify (δ : ℝ) (fieldScale r (h ω))) U {x} {y}}
      = normGFFLaw {g | ENNReal.ofReal M < F g} := hLawEvent
    _ ≤ normGFFLaw {g | ENNReal.ofReal M <
        ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
          crossLenIn (ξ : ℝ) (X ⟨(δ : ℝ), δ.property.1⟩ g) U {x} {y}} :=
      measure_mono_ae (hEq.mono fun g hg hlt => by
        change ENNReal.ofReal M < F g at hlt
        change ENNReal.ofReal M < _
        simpa only [hg] using hlt)
    _ ≤ ENNReal.ofReal η := (hTail δ).1

end SupercriticalLQGUniqueness.B2.PfeAxioms

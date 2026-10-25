import SupercriticalLQGUniqueness.B2.PfeAxioms.R68VCircleSubseq
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledFiniteMetric
import SupercriticalLQGUniqueness.B2.PfeAxioms.CanonicalAcrossLowerTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2ProdAcrossCoupled

 






set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

def r68vScaledFiniteMetric (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (ε r : Ioi (0 : ℝ))
    (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (g : DistC) : LSCMetric :=
  B2.LscTop.smulMetric
    ⟨((m ε : ℝ) /
        ((r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos ε.property r.property)⟩ : ℝ))) *
        Real.exp (-(ξ : ℝ) * circleAvg g r 0),
      Set.mem_Ioi.mpr (mul_pos
        (div_pos (m ε).property
          (mul_pos r.property (m ⟨(ε : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos ε.property r.property)⟩).property))
        (Real.exp_pos _))⟩
    (B2.LscTop.dilate r
      (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m ε) (V ε g)))

 
theorem measurable_r68vScaledFiniteMetric
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε r : Ioi (0 : ℝ)) (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hV : Measurable (V ε)) :
    Measurable (r68vScaledFiniteMetric ξ m ε r V) := by
  have hC : Measurable (fun g : DistC =>
      (⟨((m ε : ℝ) /
          ((r : ℝ) * (m ⟨(ε : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos ε.property r.property)⟩ : ℝ))) *
          Real.exp (-(ξ : ℝ) * circleAvg g r 0),
        Set.mem_Ioi.mpr (mul_pos
          (div_pos (m ε).property
            (mul_pos r.property (m ⟨(ε : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos ε.property r.property)⟩).property))
          (Real.exp_pos _))⟩ : Ioi (0 : ℝ))) := by
    apply Measurable.subtype_mk
    exact measurable_const.mul (Real.measurable_exp.comp
      (((LQGMetric.measurable_circleAvg_left r 0)).const_mul (-(ξ : ℝ))))
  have hG : Measurable (fun g : DistC =>
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m ε) (V ε g)) :=
    measurable_normalizedLFPPMetric_comp (ξ : ℝ) (m ε)
      (fun z => (continuous_eval_const z).measurable.comp hV)
  have hD : Measurable (fun g : DistC =>
      B2.LscTop.dilate r
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m ε) (V ε g))) :=
    B2.LscTop.measurable_dilate.comp (measurable_const.prodMk hG)
  exact B2.LscTop.measurable_smulMetric.comp (hC.prodMk hD)

 

theorem r68v_finite_scaled_crossing_lower_tail
    (hPerc : DG20PercEstimate')
    {ξ : Ioi (0 : ℝ)} {Q : ℝ} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {c : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (A : EuclideanAnnulus) (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ (n : ℕ) (r : Ioi (0 : ℝ)),
        (e n : ℝ) / (r : ℝ) < min ε₀ 1 →
        P' {ω | acrossDist (r68vScaledFiniteMetric ξ m (e n) r V (hN n ω)) A <
          ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal η := by
  letI : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  have hhCan := normalized_canonical_model.2
  have hXcan : ∀ δ, IsHeatSmoothing normGFFLaw (id : DistC → DistC) δ (V δ) :=
    isHeatSmoothing_canonical_of_heat_ae hB.heat_ae
  obtain ⟨T, ε₀, hT, hε₀, htail⟩ :=
    finite_across_lower_tail_uniform_fieldScale hPerc ξ m hB.normalizer
      normGFFLaw id hhCan A η hη
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro n r he
  obtain ⟨Y, hY, hYeq⟩ := exists_scaled_finite_metric_family
    normGFFLaw (id : DistC → DistC) hhCan V hXcan (ξ : ℝ) m r r.property
  let δ : Ioo (0 : ℝ) 1 :=
    ⟨(e n : ℝ) / (r : ℝ), div_pos (e n).property r.property,
      lt_of_lt_of_le he (min_le_right _ _)⟩
  let E : Ioi (0 : ℝ) := ⟨(δ : ℝ), δ.property.1⟩
  let F : DistC → ℝ≥0∞ := fun g =>
    acrossDist (r68vScaledFiniteMetric ξ m (e n) r V g) A
  have hFm : Measurable F :=
    (measurable_acrossDist A).comp
      (measurable_r68vScaledFiniteMetric ξ m (e n) r V (hB.heat_measurable (e n)))
  have hEq : ∀ᵐ g ∂normGFFLaw,
      acrossDist (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m E) (Y E g)) A = F g := by
    filter_upwards [hYeq (e n)] with g hg
    have hδ : E = ⟨(e n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e n).property r.property)⟩ := rfl
    rw [hδ]
    exact congrArg (fun D : LSCMetric => acrossDist D A)
      (show PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m ⟨(e n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (e n).property r.property)⟩)
          (Y ⟨(e n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (e n).property r.property)⟩ g) =
          r68vScaledFiniteMetric ξ m (e n) r V g by
        simpa only [r68vScaledFiniteMetric, id_eq] using hg)
  have hLaw : P' {ω | F (hN n ω) < ENNReal.ofReal T⁻¹} =
      normGFFLaw {g | F g < ENNReal.ofReal T⁻¹} := by
    rw [← hB.field_law n,
      Measure.map_apply (hB.field_measurable n)
        (measurableSet_lt hFm measurable_const)]
    rfl
  change P' {ω | F (hN n ω) < ENNReal.ofReal T⁻¹} ≤ _
  rw [hLaw]
  calc
    normGFFLaw {g | F g < ENNReal.ofReal T⁻¹} ≤
        normGFFLaw {g | acrossDist
          (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m E) (Y E g)) A <
          ENNReal.ofReal T⁻¹} := by
            apply measure_mono_ae
            filter_upwards [hEq] with g hg hlt
            simpa only [hg] using hlt
    _ ≤ ENNReal.ofReal η :=
      htail δ r r.property (lt_of_lt_of_le he (min_le_left _ _)) (Y E) (hY E)

end SupercriticalLQGUniqueness.B2.PfeAxioms

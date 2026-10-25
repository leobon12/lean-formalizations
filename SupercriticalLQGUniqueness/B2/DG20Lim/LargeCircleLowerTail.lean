import SupercriticalLQGUniqueness.B2.DG20Lim.LargeCircleCostThreshold
import SupercriticalLQGUniqueness.B2.DG20Lim.LargeScaleThreshold
import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledUnitCircleLowerTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_large_circle_lower_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e))
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (X : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing μ id e (X e))
    (T η : ℝ) (hT : 0 < T) (hη : 0 < η) :
    ∃ R₀ ε₀ : ℝ, 1 < R₀ ∧ 0 < ε₀ ∧
      ∀ (r : Ioi (1 : ℝ)) (e : Ioo (0 : ℝ) 1),
        R₀ ≤ (r : ℝ) → (e : ℝ) < ε₀ →
        μ {g | LQGMetric.Blueprint.setDist
          (normalizedContLFPP (ξ : ℝ)
            (m ⟨(e : ℝ), e.property.1⟩)
            (X ⟨(e : ℝ), e.property.1⟩ g))
          ((B2.Polylog.dilateHomeo
            (lt_trans one_pos r.property)) '' unitInnerCircle.toSet)
          ((B2.Polylog.dilateHomeo
            (lt_trans one_pos r.property)) '' unitOuterCircle.toSet) <
          ENNReal.ofReal T} ≤ ENNReal.ofReal η := by
  have hhalf : 0 < η / 2 := half_pos hη
  have hβ : 0 < Q / 4 := div_pos (hPos ξ Q hQ) (by norm_num)
  obtain ⟨M, ε₀, hM, hε₀, hunit⟩ :=
    exists_scaled_unit_circle_lower_tail_of_perc
      hPerc ξ m hm μ hμ X hX (η / 2) hhalf
  obtain ⟨R₁, hR₁, hscale⟩ :=
    exists_large_scale_field_threshold_of_inputs
      hS4 hPos ξ Q hQ m hm T M hT hM
  obtain ⟨R₂, hR₂, hgauss⟩ :=
    exists_large_circle_average_lower_tail μ hμ (Q / 4) (η / 2) hβ hhalf
  refine ⟨max R₁ R₂, ε₀,
    lt_of_lt_of_le hR₁ (le_max_left _ _), hε₀, ?_⟩
  intro r e hr he
  let r' : Ioi (0 : ℝ) :=
    ⟨(r : ℝ), Set.mem_Ioi.mpr (lt_trans one_pos r.property)⟩
  let δ : Ioo (0 : ℝ) 1 := ⟨(e : ℝ) / (r : ℝ),
    div_pos e.property.1 r'.property,
    (div_lt_one r'.property).mpr (lt_trans e.property.2 r.property)⟩
  let E : Ioi (0 : ℝ) := ⟨(e : ℝ), e.property.1⟩
  let cr : DistC → ℝ := fun g => circleAvg (affineComp (r : ℝ) 0 g) 1 0
  let Y : DistC → C(ℂ, ℝ) :=
    fun g => B2.Polylog.unitField (X E g) r' (cr g)
  let A : Set DistC := {g | finiteCircleCoords
    (normalizedContLFPP (ξ : ℝ) (m ⟨(δ : ℝ), δ.property.1⟩) (Y g))
    (unitInnerCircle, unitOuterCircle) < ENNReal.ofReal M⁻¹}
  let B : Set DistC := {g | cr g ≤ -(Q / 4 * Real.log (r : ℝ))}
  have hδ : (δ : ℝ) < ε₀ :=
    (div_lt_self e.property.1 r.property).trans he
  have hE : (⟨(r' : ℝ) * (δ : ℝ),
      mul_pos r'.property δ.property.1⟩ : Ioi (0 : ℝ)) = E := by
    apply Subtype.ext
    dsimp [r', δ, E]
    have hr0 : (r : ℝ) ≠ 0 := (lt_trans one_pos r.property).ne'
    field_simp [hr0]
  have hA : μ A ≤ ENNReal.ofReal (η / 2) := by
    have hh := hunit r' δ hδ
    simpa only [A, Y, cr, E, hE, r'] using hh
  have hB : μ B ≤ ENNReal.ofReal (η / 2) := by
    exact hgauss r ((le_max_right _ _).trans hr)
  have hsub :
      {g | LQGMetric.Blueprint.setDist
        (normalizedContLFPP (ξ : ℝ) (m E) (X E g))
        ((B2.Polylog.dilateHomeo r'.property) '' unitInnerCircle.toSet)
        ((B2.Polylog.dilateHomeo r'.property) '' unitOuterCircle.toSet) <
        ENNReal.ofReal T} ⊆ A ∪ B := by
    intro g hg
    by_contra hn
    simp only [mem_union, not_or] at hn
    have hc : -(Q / 4 * Real.log (r : ℝ)) ≤ cr g :=
      (not_le.mp hn.2).le
    have hfac : T * M ≤
        ((r' : ℝ) * (m ⟨(δ : ℝ), δ.property.1⟩ : ℝ) /
          (m E : ℝ)) * Real.exp ((ξ : ℝ) * cr g) := by
      simpa only [δ, E, r'] using
        hscale r e ((le_max_left _ _).trans hr) (cr g) hc
    have hcost := normalizedContLFPP_scaled_circle_threshold
      (ξ : ℝ) (m E) (m ⟨(δ : ℝ), δ.property.1⟩)
      (X E g) r' (cr g) T M hT hM hfac
      (not_lt.mp hn.1)
    exact (not_lt_of_ge hcost) hg
  change μ {g | LQGMetric.Blueprint.setDist
    (normalizedContLFPP (ξ : ℝ) (m E) (X E g))
    ((B2.Polylog.dilateHomeo r'.property) '' unitInnerCircle.toSet)
    ((B2.Polylog.dilateHomeo r'.property) '' unitOuterCircle.toSet) <
    ENNReal.ofReal T} ≤ ENNReal.ofReal η
  calc
    _ ≤ μ (A ∪ B) := measure_mono hsub
    _ ≤ μ A + μ B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hA hB
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      ring

end SupercriticalLQGUniqueness.B2.DG20Lim

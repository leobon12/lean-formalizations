import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledPointPowerBound
import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledUnitPointUpperTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_small_centered_point_upper_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (X : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing μ id ε (X ε))
    (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ (r : Ioo (0 : ℝ) 1), (r : ℝ) ≤ r₀ →
      ∀ (δ : Ioo (0 : ℝ) 1),
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ),
            mul_pos r.property.1 δ.property.1⟩
        μ {g | ENNReal.ofReal θ <
          edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e g)).pt 0)
            ((normalizedContLFPP (ξ : ℝ) (m e) (X e g)).pt (r : ℂ))} ≤
          ENNReal.ofReal η := by
  have hQpos : 0 < Q := hPos ξ Q hQ
  let β : ℝ := Q / 4
  let α : ℝ := (ξ : ℝ) * Q / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hα : 0 < α := by
    dsimp [α]
    exact div_pos (mul_pos ξ.property hQpos) (by norm_num)
  have hhalf : 0 < η / 2 := half_pos hη
  obtain ⟨C, hC, hscale⟩ :=
    exists_point_scale_power_of_section4 hS4 hPos ξ Q hQ m hm
  obtain ⟨M, hM, hunit⟩ :=
    exists_scaled_unit_point_upper_tail_of_section4
      hS4 ξ Q hQ m hm μ hμ X hX (η / 2) hhalf
  obtain ⟨rG, hrG, hgauss⟩ :=
    exists_small_scaled_circle_average_tail μ hμ β (η / 2) hβ hhalf
  obtain ⟨rP, hrP, hsmall⟩ :=
    B2.Polylog.exists_rpow_le hα
      (t := θ / (C * M)) (div_pos hθ (mul_pos hC hM))
  let r₀ : ℝ := min rG rP
  have hr₀ : 0 < r₀ := lt_min hrG hrP
  refine ⟨r₀, hr₀, ?_⟩
  intro r hrr₀ δ
  let e : Ioi (0 : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property.1 δ.property.1⟩
  let d : Ioi (0 : ℝ) := ⟨(δ : ℝ), δ.property.1⟩
  let cr : DistC → ℝ :=
    fun g => circleAvg (affineComp r 0 g) 1 0
  let Y : DistC → C(ℂ, ℝ) :=
    fun g => B2.Polylog.unitField (X e g) r (cr g)
  let B : Set DistC := {g | β * Real.log ((r : ℝ)⁻¹) ≤ cr g}
  let A : Set DistC := {g | ENNReal.ofReal M <
    edist ((normalizedContLFPP (ξ : ℝ) (m d) (Y g)).pt 0)
      ((normalizedContLFPP (ξ : ℝ) (m d) (Y g)).pt 1)}
  have hpow : (r : ℝ) ^ α ≤ θ / (C * M) :=
    hsmall r r.property.1.le (hrr₀.trans (min_le_right _ _))
  have hgeom : C * (r : ℝ) ^ α * M ≤ θ := by
    have hh := mul_le_mul_of_nonneg_left hpow (mul_pos hC hM).le
    dsimp [α] at hh
    have hCM : C * M ≠ 0 := (mul_pos hC hM).ne'
    calc
      C * (r : ℝ) ^ α * M = (C * M) * (r : ℝ) ^ α := by ring
      _ ≤ (C * M) * (θ / (C * M)) := hh
      _ = θ := mul_div_cancel₀ θ hCM
  have hsub :
      {g | ENNReal.ofReal θ <
        edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e g)).pt 0)
          ((normalizedContLFPP (ξ : ℝ) (m e) (X e g)).pt (r : ℂ))}
        ⊆ A ∪ B := by
    intro g hg
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have hunitg : edist ((normalizedContLFPP (ξ : ℝ) (m d) (Y g)).pt 0)
        ((normalizedContLFPP (ξ : ℝ) (m d) (Y g)).pt 1) ≤
        ENNReal.ofReal M := by
      exact not_lt.mp (show ¬ ENNReal.ofReal M <
        edist ((normalizedContLFPP (ξ : ℝ) (m d) (Y g)).pt 0)
          ((normalizedContLFPP (ξ : ℝ) (m d) (Y g)).pt 1) from hnot.1)
    have hcr : cr g ≤ β * Real.log ((r : ℝ)⁻¹) :=
      (not_le.mp hnot.2).le
    have hscaleg := hscale r δ (cr g) hcr
    have hD := normalizedContLFPP_scaled_point_le_power
      (ξ : ℝ) (m e) (m d) (X e g)
      ⟨(r : ℝ), r.property.1⟩ (cr g) C α M hC.le hscaleg hunitg
    have hθE : ENNReal.ofReal (C * (r : ℝ) ^ α * M) ≤
        ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal hgeom
    exact (not_lt_of_ge (hD.trans hθE)) hg
  change μ {g | ENNReal.ofReal θ <
    edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e g)).pt 0)
      ((normalizedContLFPP (ξ : ℝ) (m e) (X e g)).pt (r : ℂ))} ≤
    ENNReal.ofReal η
  calc
    μ {g | ENNReal.ofReal θ <
      edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e g)).pt 0)
        ((normalizedContLFPP (ξ : ℝ) (m e) (X e g)).pt (r : ℂ))}
        ≤ μ (A ∪ B) := measure_mono hsub
    _ ≤ μ A + μ B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
      add_le_add (by simpa only [A, d, e, cr, Y] using
        (hunit ⟨(r : ℝ), r.property.1⟩ δ))
        (by
          apply (hgauss r (hrr₀.trans (min_le_left _ _))).trans_eq
          rfl)
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le,
        show η / 2 + η / 2 = η by ring]

end SupercriticalLQGUniqueness.B2.DG20Lim

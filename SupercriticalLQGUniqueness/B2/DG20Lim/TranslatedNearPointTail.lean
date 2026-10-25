import SupercriticalLQGUniqueness.B2.DG20Lim.CenteredNearPointTailAny
import SupercriticalLQGUniqueness.B2.DG20Lim.TranslatedPointDistance
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatTranslateVersion
import SupercriticalLQGUniqueness.B2.DG20Pt.RealRandomTail

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_small_translated_point_upper_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (z : ℂ) (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ (r : Ioo (0 : ℝ) 1), (r : ℝ) ≤ r₀ →
      ∀ (δ : Ioo (0 : ℝ) 1),
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property.1 δ.property.1⟩
        P {ω | ENNReal.ofReal θ <
          edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt z)
            ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt (z + (r : ℂ)))} ≤
          ENNReal.ofReal η := by
  let c : Ω → ℝ := fun ω => circleAvg (h ω) 1 z
  have hc : Measurable c :=
    (measurable_circleAvg_left 1 z).comp hh.1.measurable
  have hhalf : 0 < η / 2 := half_pos hη
  obtain ⟨M, hM, hctail⟩ :=
    B2.DG20Pt.dg20_real_random_tail P c hc (η / 2) hhalf
  let K : ℝ := Real.exp (|(ξ : ℝ)| * M)
  have hK : 0 < K := Real.exp_pos _
  let θ' : ℝ := θ / K
  have hθ' : 0 < θ' := div_pos hθ hK
  let g : Ω → DistC := fun ω =>
    addConst (affineComp 1 z (h ω)) (-c ω)
  have hg : IsNormalizedWholePlaneGFF g P :=
    (B2.DG20Pt.dg20_heat_translate_normalized P h hh z 1 one_pos).1
  obtain ⟨Y, hY, hYeq⟩ :=
    B2.DG20Pt.dg20_exists_translated_heat_family P h hh X hX z
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    exists_small_centered_point_upper_tail_any_of_inputs
      hS4 hPos ξ Q hQ m hm θ' (η / 2) hθ' hhalf
  refine ⟨r₀, hr₀, ?_⟩
  intro r hrr₀ δ
  let e : Ioi (0 : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property.1 δ.property.1⟩
  let A : Set Ω := {ω | ENNReal.ofReal θ' <
    edist ((normalizedContLFPP (ξ : ℝ) (m e) (Y e ω)).pt 0)
      ((normalizedContLFPP (ξ : ℝ) (m e) (Y e ω)).pt (r : ℂ))}
  let B : Set Ω := {ω | M < |c ω|}
  let E : Set Ω := {ω | ¬ ∀ u, Y e ω u = X e ω (u + z) - c ω}
  have hE : P E = 0 := ae_iff.mp (hYeq e)
  have hA : P A ≤ ENNReal.ofReal (η / 2) := by
    simpa only [A, e] using hsmall P g hg Y hY r hrr₀ δ
  have hsub :
      {ω | ENNReal.ofReal θ <
        edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt z)
          ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt (z + (r : ℂ)))} ⊆
        A ∪ (B ∪ E) := by
    intro ω hbad
    by_cases hAe : ω ∈ A
    · exact Or.inl hAe
    right
    by_cases hBe : ω ∈ B
    · exact Or.inl hBe
    right
    by_contra hEe
    have hψ : ∀ u, Y e ω u = X e ω (u + z) - c ω := by
      exact not_not.mp (show ¬ ¬ ∀ u, Y e ω u = X e ω (u + z) - c ω from hEe)
    have hdist := normalizedContLFPP_translate_point_distance
      (ξ : ℝ) (m e) z (r : ℂ) (c ω) hψ
    have hcM : |c ω| ≤ M := le_of_not_gt hBe
    have hfac : ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) ≤
        ENNReal.ofReal K := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      calc
        (ξ : ℝ) * c ω ≤ |(ξ : ℝ) * c ω| := le_abs_self _
        _ = |(ξ : ℝ)| * |c ω| := abs_mul _ _
        _ ≤ |(ξ : ℝ)| * M := mul_le_mul_of_nonneg_left hcM (abs_nonneg _)
    have hunit : edist ((normalizedContLFPP (ξ : ℝ) (m e) (Y e ω)).pt 0)
        ((normalizedContLFPP (ξ : ℝ) (m e) (Y e ω)).pt (r : ℂ)) ≤
        ENNReal.ofReal θ' := not_lt.mp hAe
    have hθeq : ENNReal.ofReal K * ENNReal.ofReal θ' =
        ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_mul hK.le]
      congr 1
      exact mul_div_cancel₀ θ hK.ne'
    have hle : edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt z)
        ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt (z + (r : ℂ))) ≤
        ENNReal.ofReal θ := by
      rw [show z + (r : ℂ) = (r : ℂ) + z by ac_rfl, hdist]
      exact (mul_le_mul hfac hunit bot_le bot_le).trans_eq hθeq
    exact (not_lt_of_ge hle) hbad
  change P {ω | ENNReal.ofReal θ <
    edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt z)
      ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt (z + (r : ℂ)))} ≤
    ENNReal.ofReal η
  calc
    _ ≤ P (A ∪ (B ∪ E)) := measure_mono hsub
    _ ≤ P A + (P B + P E) := by
      calc
        _ ≤ P A + P (B ∪ E) := measure_union_le _ _
        _ ≤ P A + (P B + P E) := add_le_add_right (measure_union_le _ _) _
    _ ≤ ENNReal.ofReal (η / 2) + (ENNReal.ofReal (η / 2) + 0) := by
      exact add_le_add hA (add_le_add hctail hE.le)
    _ = ENNReal.ofReal η := by
      rw [add_zero, ← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      ring

end SupercriticalLQGUniqueness.B2.DG20Lim

import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeLoops.Compose
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.WeylLength




 






set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Compare

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 

theorem exterior_excursion_weyl_length (D : LSCMetric) (ξ : ℝ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (euclidForget D))
    {P : ℝ → ℂ} {V : Set ℂ} {c : ℂ} {R a b α β : ℝ}
    (hV : IsOpen V) (hcont : ContinuousOn P (Icc a b))
    (haα : a ≤ α) (hαβ : α < β) (hβb : β ≤ b)
    (hext : ∀ t ∈ Ioo α β, R < dist (P t) c)
    (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c R)
    (hf : ∀ x ∉ V, f x = 0)
    (hP : D.IsCurve P α β) :
    (∀ t ∈ Icc α β, P t ∉ V) ∧
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale ξ f D (x, y))
        (D.pt ∘ P) α β = D.len P α β := by
  have hoff := Objects.TubeChecks.excursion_endpoints_off hV hcont haα hαβ hβb hext hwin
  refine ⟨hoff, ?_⟩
  exact Toolkit.WeylLength.weylCurveLength_eq_of_zero_on_trace D ξ f hforget hP
    (fun t ht => hf (P t) (hoff t ht))

 

theorem exterior_excursion_metric_length (D D₀ : LSCMetric) (ξ : ℝ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ x y : ℂ, D₀ (x, y) = weylScale ξ f D (x, y))
    {P : ℝ → ℂ} {V : Set ℂ} {c : ℂ} {R a b α β : ℝ}
    (hV : IsOpen V) (hcont : ContinuousOn P (Icc a b))
    (haα : a ≤ α) (hαβ : α < β) (hβb : β ≤ b)
    (hext : ∀ t ∈ Ioo α β, R < dist (P t) c)
    (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c R)
    (hf : ∀ x ∉ V, f x = 0)
    (hP : D.IsCurve P α β) :
    D₀.len P α β = D.len P α β := by
  have h := (exterior_excursion_weyl_length D ξ f hforget hV hcont
    haα hαβ hβb hext hwin hf hP).2
  have hdelta : (fun x y : D.Space => weylScale ξ f D (x, y)) =
      (fun x y : D.Space => D₀ (x, y)) := by
    funext x y
    exact (hWeyl x y).symm
  rw [hdelta] at h
  have hD₀ : D₀.len P α β =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => D₀ (x, y)) (D.pt ∘ P) α β := by
    rw [D₀.len_eq_curveLength]
    exact (HigherDimLQGMetric.curveLengthWith_edist (D₀.pt ∘ P) α β).symm
  exact hD₀.trans h

 


theorem exterior_excursion_internal_charge (D D₀ : LSCMetric) (ξ : ℝ)
    (f : C(ℂ, ℝ)) (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ x y : ℂ, D₀ (x, y) = weylScale ξ f D (x, y))
    {P : ℝ → ℂ} {V U : Set ℂ} {c : ℂ} {R a b α β L : ℝ}
    (hV : IsOpen V) (hcont : ContinuousOn P (Icc a b))
    (haα : a ≤ α) (hαβ : α < β) (hβb : β ≤ b)
    (hext : ∀ t ∈ Ioo α β, R < dist (P t) c)
    (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c R)
    (hf : ∀ x ∉ V, f x = 0)
    (hP : D.IsCurve P α β)
    (hU : MapsTo P (Icc α β) U)
    (hunit : HasUnitSpeedOn (D₀.pt ∘ P) (Icc 0 L))
    (hα : α ∈ Icc 0 L) (hβ : β ∈ Icc 0 L) :
    D.internal U (⟨P α, hU ⟨le_rfl, hαβ.le⟩⟩,
      ⟨P β, hU ⟨hαβ.le, le_rfl⟩⟩) ≤ ENNReal.ofReal (β - α) := by
  have hlen := exterior_excursion_metric_length D D₀ ξ f hforget hWeyl
    hV hcont haα hαβ hβb hext hwin hf hP
  have hunitlen : D₀.len P α β = ENNReal.ofReal (β - α) := by
    rw [D₀.len_eq_curveLength]
    exact LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hunit hα hβ
  have hcost : D.internal U (⟨P α, hU ⟨le_rfl, hαβ.le⟩⟩,
      ⟨P β, hU ⟨hαβ.le, le_rfl⟩⟩) ≤ D.len P α β := by
    exact iInf_le_of_le P <| iInf_le_of_le α <| iInf_le_of_le β <|
      iInf_le_of_le hP <| iInf_le_of_le hU <|
        iInf_le_of_le rfl <| iInf_le_of_le rfl le_rfl
  exact hcost.trans (hlen.symm.trans hunitlen).le


end SupercriticalLQGUniqueness.Uniqueness.Objects.Compare

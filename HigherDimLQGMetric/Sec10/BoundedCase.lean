import HigherDimLQGMetric.Sec10.TightBounded

/-!
# The bounded-perturbation tightness clause of Lemma 10.1
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}

/-- A strong assignment has sharp weak tightness over all positive scales for an LGF plus a
bounded continuous perturbation. -/
theorem IsStrongExpMetric.tightOver_bdd (hd : 2 ≤ d) (hξ : 0 < ξ)
    (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusBddCont h P) :
    TightOver P (fun r ω => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r)
      (Ioi 0) := by
  obtain ⟨hmh, f, hf, hfb, hg⟩ := hh
  let g : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
  have hgf : ∀ ω, addFun (g ω) (f ω) = h ω := by
    intro ω
    simp only [g, addFun]
    exact sub_add_cancel _ _
  let A : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => (D (s8a_pureRescaled g r ω)).1
  let B : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r
  have hAm : ∀ r ∈ Ioi (0 : ℝ), Measurable (A r) := by
    intro r hr
    exact (measurable_subtype_coe.comp hD.measurable).comp
      (s8a_pureRescaled_isLGF hg hr).measurable
  have hBm : ∀ r ∈ Ioi (0 : ℝ), Measurable (B r) := by
    intro r _
    have hs : B r = scaledField ξ D (fun s => s ^ (ξ * Q)) r 0 ∘ h := by
      funext ω
      exact (scaledField_zero ξ D (fun s => s ^ (ξ * Q)) r (h ω)).symm
    rw [hs]
    exact (measurable_scaledField hD.measurable _ r 0).comp hmh
  let μ : Measure C(Rd d × Rd d, ℝ) := P.map (A 1)
  have : IsProbabilityMeasure μ := inferInstance
  have hAlaw : ∀ r ∈ Ioi (0 : ℝ), P.map (A r) = μ := by
    intro r hr
    have hDm : Measurable fun k : DistRd d => (D k).1 :=
      measurable_subtype_coe.comp hD.measurable
    change P.map ((fun k : DistRd d => (D k).1) ∘ s8a_pureRescaled g r) =
      P.map ((fun k : DistRd d => (D k).1) ∘ s8a_pureRescaled g 1)
    rw [← Measure.map_map hDm (s8a_pureRescaled_isLGF hg hr).measurable,
      ← Measure.map_map hDm (s8a_pureRescaled_isLGF hg one_pos).measurable,
      s8a_map_pureRescaled_eq hd hg hr, s8a_map_pureRescaled_eq hd hg one_pos]
  have hμ : ∀ᵐ E ∂μ, IsContinuousMetric E := by
    exact (ae_map_iff (μ := P) (f := A 1) (hAm 1 (by simp)).aemeasurable
      (measurableSet_isContinuousMetric_select d)).2
      (ae_of_all _ fun ω => (D _).2)
  let M : Ω → ℝ := fun ω => ξ * (2 * s8a_supAbs (f ω))
  have hMm : Measurable M := measurable_const.mul (measurable_const.mul (s8a_measurable_supAbs hf))
  have hBmetric : ∀ r ∈ Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsContinuousMetric (B r ω) := by
    intro r hr
    exact ae_of_all _ fun ω =>
      s8a_normalizedAtScale_isContinuousMetric ξ D _ (h ω) hr
        (s8a_sharpNormalizer_pos r hr)
  have hcompare : ∀ r ∈ Ioi (0 : ℝ), ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A r ω p ≤ B r ω p ∧
      B r ω p ≤ Real.exp (M ω) * A r ω p := by
    intro r hr
    have hb := hD.ae_normalizedAtScale_bdd_compare hd hξ hg hf
      (fun ω => s8a_supAbs (f ω)) (fun ω x =>
        s8a_abs_le_supAbs (hfb ω).choose_spec x) hr
    filter_upwards [hb] with ω hω p
    simpa only [A, B, M, g, addFun, sub_add_cancel, neg_mul] using hω p.1 p.2
  exact s8a_tightOver_of_randomCompare P A B μ
    (fun r hr => (hAm r hr).aemeasurable)
    (fun r hr => (hBm r hr).aemeasurable)
    hAlaw hμ M hMm hBmetric hcompare

end HigherDimLQGMetric

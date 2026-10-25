import SupercriticalLQGUniqueness.B2.WeakStrong.Homothety
import SupercriticalLQGUniqueness.B2.WeakStrong.Field
import SupercriticalLQGUniqueness.Frozen.IsWeakLQGMetric

 














set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC DistOn ofCont addFun addConst IsGFFPlusCont affineComp circleAvg restrictTo
  affinePt)

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 
def dilMetric (D : DistC → LSCMetric) (Q : ℝ) (b : Set.Ioi (0 : ℝ)) (h : DistC) : LSCMetric :=
  dilateM (D (dilField Q b h)) (b : ℝ)⁻¹ (inv_ne_zero (ne_of_gt b.2))

theorem dilMetric_apply (D : DistC → LSCMetric) (Q : ℝ) (b : Set.Ioi (0 : ℝ)) (h : DistC)
    (p : ℂ × ℂ) :
    dilMetric D Q b h p = D (dilField Q b h) ((b : ℝ)⁻¹ • p.1, (b : ℝ)⁻¹ • p.2) := rfl

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

theorem measurable_dilMetric (hD : Measurable D) (b : Set.Ioi (0 : ℝ)) :
    Measurable (dilMetric D Q b) :=
  (measurable_dilateM _ _).comp (hD.comp (measurable_dilField Q b))

 
theorem length_dilMetric (hD : IsWeakLQGMetric ξ Q D) (b : Set.Ioi (0 : ℝ)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P → ∀ᵐ ω ∂P, (dilMetric D Q b (h ω)).IsLengthSpace := by
  intro Ω _ P _ h hh
  filter_upwards [hD.2.1 P _ (isGFFPlusCont_dilField hh Q b.2)] with ω hω
  exact isLengthSpace_dilateM hω _ _

 
theorem locality_dilMetric (hD : IsWeakLQGMetric ξ Q D) (b : Set.Ioi (0 : ℝ)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
        ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
          ∀ᵐ ω ∂P, (dilMetric D Q b (h ω)).internal (U : Set ℂ) = F (restrictTo U (h ω)) := by
  intro Ω _ P _ h hh U
  have hc : ((b : ℝ)⁻¹) ≠ 0 := inv_ne_zero (ne_of_gt b.2)
  have hY := smul_mem_smulOpens hc U
  obtain ⟨F, hF, hae⟩ := hD.2.2.1 P _ (isGFFPlusCont_dilField hh Q b.2) (smulOpens (b : ℝ)⁻¹ U)
  refine ⟨fun ρ p => F (restrictMap Q b.2 U ρ)
    (⟨(b : ℝ)⁻¹ • p.1.1, (hY _).2 p.1.2⟩, ⟨(b : ℝ)⁻¹ • p.2.1, (hY _).2 p.2.2⟩), ?_, ?_⟩
  · exact Measurable.of_eval fun p =>
      (measurable_pi_apply _).comp (hF.comp (measurable_restrictMap Q b.2 U))
  · filter_upwards [hae] with ω hω
    funext p
    change (dilateM (D (dilField Q b (h ω))) (b : ℝ)⁻¹ hc).internal (U : Set ℂ) p = _
    rw [internal_dilateM _ _ hc _ _ hY p, hω, restrictTo_dilField Q b.2]

 
theorem weyl_dilMetric (hD : IsWeakLQGMetric ξ Q D) (b : Set.Ioi (0 : ℝ)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ),
          weylScale (ξ : ℝ) f (dilMetric D Q b (h ω)) = (dilMetric D Q b (addFun (h ω) f)).1 := by
  intro Ω _ P _ h hh
  have hc : ((b : ℝ)⁻¹) ≠ 0 := inv_ne_zero (ne_of_gt b.2)
  filter_upwards [hD.2.2.2.1 P _ (isGFFPlusCont_dilField hh Q b.2)] with ω hω f
  funext p
  have hfg : ∀ z, (f.comp (affinePt b 0)) ((b : ℝ)⁻¹ • z) = f z := fun z => by
    rw [ContinuousMap.comp_apply, affinePt_smul_inv (ne_of_gt b.2)]
  change weylScale (ξ : ℝ) f (dilateM (D (dilField Q b (h ω))) (b : ℝ)⁻¹ hc) p = _
  rw [weylScale_dilateM (ξ : ℝ) _ _ hc hfg p, hω]
  change _ = D (dilField Q b (addFun (h ω) f)) _
  rw [dilField_addFun Q b.2]

 
theorem translation_dilMetric (hD : IsWeakLQGMetric ξ Q D) (b : Set.Ioi (0 : ℝ)) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (dilMetric D Q b (translateDist z (h ω))).1 (u, v) =
          (dilMetric D Q b (h ω)).1 (u + z, v + z) := by
  intro Ω _ P _ h hh z
  filter_upwards [hD.2.2.2.2.1 P _ (isGFFPlusCont_dilField hh Q b.2) ((b : ℝ)⁻¹ • z)]
    with ω hω u v
  change D (dilField Q b (translateDist z (h ω))) ((b : ℝ)⁻¹ • u, (b : ℝ)⁻¹ • v) =
    D (dilField Q b (h ω)) ((b : ℝ)⁻¹ • (u + z), (b : ℝ)⁻¹ • (v + z))
  rw [dilField_translate Q b.2, smul_add, smul_add]
  exact hω _ _

end SupercriticalLQGUniqueness.B2.WeakStrong

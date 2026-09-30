import QuantumZipper.Proofs.Thm18.G3ZrTr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (7): `G1.ChoiceRegularA` of the pulled-back translated field (`choiceRegularA_translate`)

See `G3ZrTr` for the argument. Test functions on `ℍ` are closed under real translations
(`testTranslate`), and Lebesgue measure on `ℂ` is translation invariant (`tmeas_map_add`), so the
continuum limits of `ChoiceRegularCore` at dilated test measures pass to real translates
(`contData_translate_of`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2 RegClosure

/-- The real translate `z ↦ ρ(z − t)` of a test function on `ℍ`. -/
def testTranslate (ρ : TestFun H) (t : ℝ) : TestFun H :=
  ⟨ρ.1 ∘ Homeomorph.subRight (t : ℂ), ρ.2.1.comp (contDiff_id.sub contDiff_const),
    ρ.2.2.1.comp_homeomorph (Homeomorph.subRight (t : ℂ)), by
      rw [tsupport_comp_eq_preimage]
      intro z hz
      have h : 0 < (z - (t : ℂ)).im := ρ.2.2.2 hz
      show 0 < z.im
      simpa using h⟩

/-- **Translation invariance of the test measures.** -/
theorem tmeas_map_add (σ : ℂ → ℝ) (t : ℂ) :
    (G1.tmeas σ).map (· + t) = G1.tmeas fun z => σ (z - t) := by
  have hm : Measurable fun z : ℂ => z + t := measurable_add_const t
  ext s hs
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hm hs), ← lintegral_indicator hs,
    ← lintegral_add_right_eq_self (μ := (volume : Measure ℂ))
      (fun z => s.indicator (fun z => ENNReal.ofReal (σ (z - t))) z) t]
  congr 1
  funext z
  simp only [Set.indicator, Set.mem_preimage, add_sub_cancel_right]
  rfl

/-- **Continuum limits of a real translate.** -/
theorem contData_translate_of {z : FieldSample} (hz : IsRegularSample z) (t : ℝ)
    {m : Measure ℂ} (hm : ∀ᵐ u ∂m, u ∈ Hbar) (h : F1.ContData z (m.map (· + (t : ℂ)))) :
    F1.ContData (translate z (t : ℂ)) m := by
  obtain ⟨F, hF⟩ := hz
  obtain ⟨hint, L, hL⟩ := h
  have htm : Measurable fun u : ℂ => u + (t : ℂ) := measurable_add_const _
  have hkey : ∀ ρ : ℝ, 0 < ρ → (fun u => evalReg (translate z (t : ℂ)) (foldedCircle u ρ)) =ᵐ[m]
      fun u => evalReg z (foldedCircle (u + t) ρ) := fun ρ hρ =>
    hm.mono fun u hu => evalReg_translate_fc hF t hu hρ
  have hI : ∀ ρ : ℝ, 0 < ρ →
      ∫ u, evalReg (translate z (t : ℂ)) (foldedCircle u ρ) ∂m =
        ∫ u, evalReg z (foldedCircle u ρ) ∂(m.map (· + (t : ℂ))) := fun ρ hρ => by
    rw [integral_congr_ae (hkey ρ hρ),
      integral_map htm.aemeasurable (measurable_evalReg_fc_slice z ρ).aestronglyMeasurable]
  refine ⟨fun ρ hρ => ?_, L, hL.congr' ?_⟩
  · exact ((integrable_map_measure (measurable_evalReg_fc_slice z ρ).aestronglyMeasurable
      htm.aemeasurable).1 (hint ρ hρ)).congr (hkey ρ hρ).symm
  · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    exact (hI ρ hρ).symm

end G3Zr
end Thm18Asm
end QuantumZipper

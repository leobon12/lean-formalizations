import HigherDimLQGMetric.Locality.CutoffH
import HigherDimLQGMetric.Field.Version
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Factorization of field observations through countable test coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_fullSigma_le_pairJ {d : ℕ} {Ω : Type*}
    (h : Ω → DistRd d) :
    fullSigmaRd h ≤ MeasurableSpace.comap
      (fun ω => pairJ ⊤ (h ω)) inferInstance := by
  let X : Ω → CoordJ → ℝ := fun ω => pairJ ⊤ (h ω)
  have he : h = (pairJInv ⊤) ∘ X := by
    funext ω
    exact (pairJInv_pairJ ⊤ (h ω)).symm
  change MeasurableSpace.comap h inferInstance ≤ MeasurableSpace.comap X inferInstance
  rw [he, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pairJInv ⊤).comap_le

/-- Doob–Dynkin factorization through the standard-Borel coordinate code of
the whole distribution. -/
theorem l7a_factor_field_observation {d : ℕ} {Ω β : Type*}
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    (h : Ω → DistRd d) (F : Ω → β)
    (hF : Measurable[fullSigmaRd h] F) :
    ∃ f : (CoordJ → ℝ) → β, Measurable f ∧
      F = f ∘ (fun ω => pairJ ⊤ (h ω)) := by
  have hcode := l7a_fullSigma_le_pairJ h
  exact (hF.mono hcode le_rfl).exists_eq_measurable_comp

end HigherDimLQGMetric

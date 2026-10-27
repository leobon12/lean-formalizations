import MatedCRTHarmonic.MesoModel.Annulus38

/-!
# One-scale bad-event export

Expose the corrected Lemma 3.8 failure estimate in the outer-measure form consumed by the
mesoscopic cell-model bundle.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

/-- Corrected [18] Lemma 3.8, exported as FIX13's outer-measure failure-event interface. -/
theorem lemma38AnnulusHitBad_of_oneScaleBadBound
    (F : CellFamily.RandomCellFamily) (ρ : ℝ)
    (hinput : Annulus38OneScaleBadBound F ρ) : CellFamily.Lemma38AnnulusHitBad F ρ :=
  annulus38_lemma38AnnulusHitBad_of_oneScaleBadBound F ρ hinput

end MatedCRTHarmonic.MesoModel

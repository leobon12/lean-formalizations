import HigherDimLQGMetric.Sec10.LocalCase

/-! Lemma 10.1: a strong assignment belongs to the sharp weak class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The strong axioms imply the sharp weak axioms in dimension at least two. -/
theorem lemma101 {d : ℕ} (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ Q D) : IsSharpWeakExpMetric d ξ Q D := by
  exact {
    measurable := hD.measurable
    length := hD.length
    locality := hD.locality
    weyl := hD.weyl
    translation := hD.ae_translation
    c_pos := fun r hr => s8a_sharpNormalizer_pos r hr
    tight := fun P _ h hh R hR => hD.tightOver_cont hd hξ P h hh R hR
    tight_bdd := fun P _ h hh => hD.tightOver_bdd hd hξ P h hh }

end HigherDimLQGMetric

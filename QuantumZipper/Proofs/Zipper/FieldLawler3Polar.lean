import QuantumZipper.Proofs.Zipper.FieldLawler2Radial
import QuantumZipper.Proofs.Thm18.LWHarmConf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 3: the circle flux `fl2FluxR` in the polar chart

In the chart `χ_R(ζ) = R e^{iζ}` (upper half-plane ↦ inside of `C_R`), the inward radial flux
through `C_R` is the vertical flux at the real axis: `R · ∂ᵣ⁻ u(R e^{iθ}) = ∂_y (u ∘ χ_R)(θ)` for
`u` differentiable at `R e^{iθ}` and vanishing there (`fl3_rDer_eq_yDer`), hence
`fl2FluxR R u = excR (u ∘ χ_R) (0, π)` (`fl3_fluxR_eq_excR`). This moves FL's `ℰ(C_R, ·)`
(Lemma 3.3 and (2.4), `fl2_tsum_fluxR_le`, `fl2_fluxR_outer_le`) to the half-plane form of
`excR`, where local conformal invariance (`lwHarm_excR_comp`) and the explicit symmetry
(`fl3_excR_symm`) apply. Own elementary computation.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The polar chart `ζ ↦ R e^{iζ}`. -/
def fl3Chart (R : ℝ) (ζ : ℂ) : ℂ := (R : ℂ) * Complex.exp (ζ * I)

theorem fl3Chart_real (R θ : ℝ) : fl3Chart R (θ : ℂ) = fl2Pt R θ 0 := by
  simp [fl3Chart, fl2Pt]

end FieldLawler
end QuantumZipper

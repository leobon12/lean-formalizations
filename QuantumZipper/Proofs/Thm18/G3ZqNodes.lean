import QuantumZipper.Proofs.Thm18.G3ZqMapZ
import QuantumZipper.Proofs.Thm18.G3ZqG2Palm
import QuantumZipper.Proofs.Thm18.G2AgreeBasic
import QuantumZipper.Proofs.NonVacuityWedgeUncond

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (7): the map-instance leaves of the generalized G2 engine (D92)

The generalized engine (`G3Zq.g2FixMixStmtZ_of_fix_zoomLoc`, G3ZqG2DisR) gives the fixed-region
mixing statement `G2FixMixStmtZ Z Z' γ` for any zoom pair from the structural hypotheses (proved
for the map zooms in G3ZqMapZ), the two fixed-point conditional zoom nodes and the two zoom
locality nodes. For the zooms through the local maps of a fixed good path `a`
(`g3zMapZ γ Ψ true a` at the Palm point, `g3zMapZ γ Ψ false a` at its partner) these nodes are
stated here, with the limit law the `γ`-wedge law `g2WedgeLaw P' Y'` (the same law as in the
plain engine, so that the plain and map limits coincide).

* `G3ZqFixXStmt`: Sheffield, arXiv:1012.4797, Prop. 1.6 and proof of Prop. 5.5 (pp. 24–25, 65),
  at a fixed Palm point of the free field, through the local map (D3⁺(i) with the field outside
  `B_κ(x)` and the cut length frozen); map version of `G2RootXFixStmt`.
* `G3ZqFixRStmt`: the same at the partner side; map version of `G2RootRFixStmt`.
* `G3ZqZoomLocStmt`: the zoom through the local map does not see a bump away from the point
  (proof of Prop. 5.5, p. 66); map version of `G2ZoomLocStmt`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

/-- A good path: continuous with a simple-chord trace (a.s. for Brownian motion; the normalized
side uniformizers then exist, `G1ZA1a.isNormalizedUniformizer_sideDom`). -/
def G3ZqGoodPath (γ : ℝ) (a : ℝ≥0 → ℝ) : Prop :=
  Continuous a ∧ IsSimpleChord (pathTrace (γ ^ 2) a)

/-- **Fixed-point conditional zoom through the local map, `x` side (open leaf).** -/
def G3ZqFixXStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ a : ℝ≥0 → ℝ, G3ZqGoodPath γ a →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : Ω' → FieldSample), IsQuantumWedge γ γ Y' P' →
    G2RootXFixStmtZ (g3zMapZ γ Ψ true a) γ (g2WedgeLaw P' Y')

/-- **Fixed-point conditional zoom through the local map, `R` side (open leaf).** -/
def G3ZqFixRStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ a : ℝ≥0 → ℝ, G3ZqGoodPath γ a →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : Ω' → FieldSample), IsQuantumWedge γ γ Y' P' →
    G2RootRFixStmtZ (g3zMapZ γ Ψ false a) γ (g2WedgeLaw P' Y')

end G3Zq
end Thm18Asm
end QuantumZipper

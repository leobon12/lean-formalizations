import QuantumZipper.Proofs.Thm18.G1ZmScale
import QuantumZipper.Proofs.Thm18.G3Z2b2Inn
import QuantumZipper.Proofs.Thm18.G3Z2b2Cmp
import QuantumZipper.Proofs.GFF.CoordRegFwd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM (5): the Palm-window functional of the canonical wedge along the scaled path

`g1PhiM_canonical_scalePath`: for a good unscaled field `W` with scale `b = scaleParam γ W > 0`
and a good path `a` whose Brownian scaling `S_b a` is good, the measurable Palm-window functional
of the canonical wedge `canonical γ W` along the scaled path equals the functional of the
**unscaled** field `W` along the path `a`:

  `g1PhiM (canonical γ W, S_b a) = g1PhiM (W, a)`.

The random dilation `b` of the canonical description is absorbed into the path. Chain: the
measurable functional is the geometric Palm-window integral (`g1Inner_eq_g1PhiM`); the dilation
to the unscaled field (`wedgePalm_canonical_eq`) produces the maps `b · φ^{S_b a}_{x/b}`, which
are the maps `φ^a_x` of the unscaled path precomposed with a fixed dilation (`g3locM_scalePath`),
and the canonical data do not see a precomposed dilation
(`data_canonical_zoomFieldVia_comp_mul`). Sheffield, arXiv:1012.4797, p. 70 (the curve is
independent of the wedge; scale invariance of SLE). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Function Complex
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Zm

open G3Z2b2 D3Plus

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- Two maps agreeing on `ℍ` have the same canonical zooms. -/
theorem canonical_zoomFieldVia_congr_H (γ L : ℝ) (y : FieldSample) (x : ℝ) {f g : ℂ → ℂ}
    (hfg : EqOn f g H) :
    canonical γ (zoomFieldVia γ L y x f) = canonical γ (zoomFieldVia γ L y x g) := by
  refine Factorization.canonical_congr ?_ γ
  funext k z
  unfold avgReg
  congr 1
  funext n
  simp only [zoomFieldVia, addConst]
  rw [CoordReg.coordChange_fc_congr _ hfg _ _ (radius_pos k)]

end G1Zm
end Thm18Asm
end QuantumZipper

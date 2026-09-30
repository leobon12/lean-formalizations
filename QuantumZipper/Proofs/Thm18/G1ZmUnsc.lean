import QuantumZipper.Proofs.Thm18.G1ZmResc
import QuantumZipper.Proofs.Thm18.G1ZmRed
import QuantumZipper.Proofs.Thm18.G4TraceNull2Scale
import QuantumZipper.Proofs.Zipper.ESMComplF1
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM (6): Brownian scaling of the path law (tool for removing the random dilation)

`lintegral_pathOf_scale`: for a Brownian motion `B` and `b > 0`,
`E F(path) = E F(S_b path)` with `S_b a = a(b² ·)/b` (`pathOf_scaledBM`). Together with
`g1PhiM_canonical_scalePath` (G1ZmResc) this is the rescaling route to the unscaled wedge
`wedgeU = wedgeField (lateralPart X) A Q`:

The random dilation `b = scaleParam γ W` of the canonical description is absorbed into the path:
for each wedge sample, the path law is invariant under the Brownian scaling `S_b`
(`lintegral_pathOf_scale`), and along the scaled path the canonical functional is the unscaled one
(`g1PhiM_canonical_scalePath`). This removes the "Palm after dilation" obstacle: after the
rescaling the local maps are deterministic and the field is the unscaled wedge, to which the Palm
identity `G3WedgePalmIdStmt` applies. Sheffield, arXiv:1012.4797, p. 70 (the curve is
independent of the wedge; SLE is scale invariant). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Zm

open G3Z2b2 D3Plus

/-- The unscaled wedge field (circle-average embedding) of the wedge representative. -/
abbrev wedgeU (γ : ℝ) {Ω' : Type} (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (ω' : Ω') :
    FieldSample :=
  wedgeField (lateralPart (X ω')) (fun t => A t ω') (Qc γ)

theorem pathOf_scaledBM {Ω : Type} {B : ℝ≥0 → Ω → ℝ} {b : ℝ} (hb : 0 < b) (ω : Ω) :
    pathOf (G4TraceNull2.scaledBM b B) ω = scalePath b (pathOf B ω) := by
  funext s
  simp only [pathOf, G4TraceNull2.scaledBM, scalePath]
  rw [Real.coe_toNNReal _ (sq_nonneg b), Real.sqrt_sq hb.le, div_eq_inv_mul]

/-- **Brownian scaling of the path law.** -/
theorem lintegral_pathOf_scale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {b : ℝ} (hb : 0 < b)
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (pathOf B ω) ∂P = ∫⁻ ω, F (scalePath b (pathOf B ω)) ∂P := by
  have hB' := G4TraceNull2.isBrownianReal_scaledBM hB hb
  rw [← lintegral_map' hF.aemeasurable (IsBrownianReal.aemeasurable_pathOf hB),
    F1.map_pathOf_eq_of_isBrownianReal hB hB',
    lintegral_map' hF.aemeasurable (IsBrownianReal.aemeasurable_pathOf hB')]
  simp only [pathOf_scaledBM hb]

end G1Zm
end Thm18Asm
end QuantumZipper

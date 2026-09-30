import QuantumZipper.Proofs.Thm18.G3ZqL4Resc
import QuantumZipper.Proofs.Thm18.G3ZqSMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (11): the one-point regularity node reduced to the unscaled-wedge clause

`G3ZqL1ResclRegStmt` (G3ZqL4Resc) has three clauses. Clauses (i) (`G1FacRegA` of the canonical
field along the randomly scaled path) and (ii) (`DilReg`) are proved by the helper G3ZqS
(`G3ZqS.ae_g1FacRegA_scaled`, `G3ZqS.ae_dilReg_scaled`: the randomly scaled Brownian motion on the
product space, which avoids the quantifier swap). Only clause (iii) remains:
`G3ZqL1RegUStmt`, the one-point analog of `G3ZqS.G3ZqSRegUStmt` (`G3ZqRegU` of the UNSCALED
wedge along the unscaled path at `ν`-a.e. window point).

Headlines: `g3ZqL1ResclRegStmt_of_regU`, `g1WedgePalmLimStmt_of_regU_pathU`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open G3Z2b2 G1Zm D3Plus G3Zq

/-- **Node: area-only regularity of the unscaled wedge along the path (one point).** -/
def G3ZqL1RegUStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    (∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) →
  ∀ (left : Bool) (U L : ℝ), ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P,
    ∀ᵐ x ∂(qBoundaryMeasure γ (wedgeU γ X A ω')), x ∈ g1zWedgeWin γ left (wedgeU γ X A ω') U →
      G3ZqRegU γ L Ψ left (wedgeU γ X A ω') (pathOf B ω) x

/-- **`G3ZqL1ResclRegStmt` from the unscaled-wedge clause** (clauses (i), (ii) from G3ZqS). -/
theorem g3ZqL1ResclRegStmt_of_regU (h : G3ZqL1RegUStmt) : G3ZqL1ResclRegStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω _ P _ B hB hsc left U L
  filter_upwards [G3ZqS.ae_g1FacRegA_scaled (Ψ := Ψ) hγ hγ2 hsel hX hA hXA hB left L,
    G3ZqS.ae_dilReg_scaled hγ hγ2 hsel hX hA hXA hB hsc,
    h γ hγ hγ2 Ψ hsel P' X A hX hA hXA P B hB hsc left U L] with ω' h1 h2 h3
  filter_upwards [h1, h2, h3] with ω a1 a2 a3
  exact ⟨ae_of_all _ fun x hx => a1 x hx.1, fun x _ => a2 left x, a3⟩

end G3ZqL
end Thm18Asm
end QuantumZipper

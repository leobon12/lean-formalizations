import QuantumZipper.Proofs.Thm18.G3ZqSReg2
import QuantumZipper.Proofs.Thm18.G3ZqFub
import QuantumZipper.Proofs.Thm18.G3ZrRep2
import QuantumZipper.Proofs.Probability.BMExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3ZqS (4): `G3ZqResclRegStmt` from the regularity of the unscaled field along the path

Of the three clauses of `G3ZqResclFieldReg` and the goodness clauses of `G3ZqResclRegStmt`:

* goodness of `wedgeU`, of `wedgeRep` and positivity of the scale: proved nodes
  (`LogSingGood.wedgeRefGoodAS_holds`, `G3Zr.ae_good_wedgeRep`, `G1RC.ae_scale_pos`);
* clause (i), window regularity of the canonical field along the SCALED path (coupled with the
  field through its scale): `ae_g1FacRegA_scaled` (G3ZqSReg1, random-scale Brownian motion on the
  product space) and the positivity of the length partner (`ae_g3zPartner_pos`, same setting);
* clause (ii), `DilReg` for the scaled-path local maps: `ae_dilReg_scaled` (G3ZqSReg2);
* clause (iii), the regularity `G3ZqRegU` of the UNSCALED field along the unscaled path at a.e.
  window point and its partner: the remaining node **`G3ZqSRegUStmt`** (strictly smaller: one
  clause, no coupling of path and field scale).

Headline: **`g3ZqResclRegStmt_of_regU : G3ZqSRegUStmt → G3Zq.G3ZqResclRegStmt`**.
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqS

open G1Zm G3Zq G3Z2b2

/-- **Clause (iii) of `G3ZqResclFieldReg` (open node):** a.s. in the field, a.s. in the Brownian
sample, at a.e. window point of the unscaled wedge `wedgeU` and at its length partner, the
area-only regularity `G3ZqRegU` of the unscaled field along the unscaled path. -/
def G3ZqSRegUStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    (∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) →
  ∀ (U L : ℝ), ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P,
    ∀ᵐ x ∂(qBoundaryMeasure γ (wedgeU γ X A ω')), x ∈ g1zWedgeWin γ true (wedgeU γ X A ω') U →
      G3ZqRegU γ L Ψ true (wedgeU γ X A ω') (pathOf B ω) x ∧
        0 < R18.g3zPartner γ (wedgeU γ X A ω') x ∧
        G3ZqRegU γ L Ψ false (wedgeU γ X A ω') (pathOf B ω)
          (R18.g3zPartner γ (wedgeU γ X A ω') x)

variable {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}

/-- **The length partner of the canonical wedge is positive.** -/
theorem ae_partner_pos_rep {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P') (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω' ∂P', ∀ x : ℝ, x < 0 → 0 < R18.g3zPartner γ (wedgeRep γ X A ω') x := by
  obtain ⟨B, hB⟩ := BMExist.exists_isBrownianReal_stdP
  have hS := thm18Setting_rs (P := LQGDimension.ExistAsm.stdP) hγ hγ2 hX hA hXA hB
    (c := fun _ => 1) measurable_const (fun _ => one_pos)
  have hW : IsProbabilityMeasure (LQGDimension.ExistAsm.stdP.map (pathOf B)) :=
    (Measure.isProbabilityMeasure_map_iff (IsBrownianReal.aemeasurable_pathOf hB)).2
      inferInstance
  have h := Measure.ae_ae_of_ae_prod (G3Zq.ae_g3zPartner_pos hS (thm18Inputs_of_setting hS))
  filter_upwards [h] with ω' hω'
  exact hω'.exists.choose_spec

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **`G3ZqResclRegStmt` from clause (iii).** -/
theorem g3ZqResclRegStmt_of_regU (h : G3ZqSRegUStmt) : G3ZqResclRegStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω _ P _ B hB hsc U L
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  filter_upwards [G1RC.ae_scale_pos hγ hγ2 hX hA hXA,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA,
    G3Zr.ae_good_wedgeRep hγ hγ2 hX hA hXA,
    ae_g1FacRegA_scaled (Ψ := Ψ) hγ hγ2 hsel hX hA hXA hB true L,
    ae_g1FacRegA_scaled (Ψ := Ψ) hγ hγ2 hsel hX hA hXA hB false L,
    ae_partner_pos_rep hγ hγ2 hX hA hXA,
    ae_dilReg_scaled hγ hγ2 hsel hX hA hXA hB hsc,
    h γ hγ hγ2 Ψ hsel P' X A hX hA hXA P B hB hsc U L]
    with ω' hb hWg hy hFt hFf hpp hdil hU
  refine ⟨hb, hWg, hy, ?_⟩
  filter_upwards [hFt, hFf, hdil, hU] with ω h1 h2 h3 h4
  refine ⟨ae_of_all _ fun x hx => ?_, fun x hx => ⟨h3 true x, h3 false _⟩, h4⟩
  have hx0 : x ∈ g1SideHalf true := hx.1
  have hxneg : x < 0 := by simpa [g1SideHalf] using hx0
  have hp : 0 < R18.g3zPartner γ (canonical γ (wedgeU γ X A ω')) x := hpp x hxneg
  refine ⟨h1 x hx0, hp, h2 _ ?_⟩
  simpa [g1SideHalf] using hp

end G3ZqS
end Thm18Asm
end QuantumZipper

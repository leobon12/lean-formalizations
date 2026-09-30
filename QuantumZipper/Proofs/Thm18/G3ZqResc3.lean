import QuantumZipper.Proofs.Thm18.G3ZqResc2
import QuantumZipper.Proofs.Thm18.G3ZqWireU
import QuantumZipper.Proofs.Thm18.G3ZqGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (8): the a.s. two-point rescaling identity from a.s. regularity

`G3ZqResclIdStmt` (G3ZqWireU) is reduced to the almost-sure regularity of the fields and paths
at the window points (`G3ZqResclRegStmt`), by the deterministic two-point rescaling identity
`g3PhiM2_canonical_scalePath` (G3ZqResc2). The regularity conditions are those of Z-REG's
area-only form (D93): `G3Zr.G3FacRegA` for the canonical field along the scaled path, `DilReg`
for the dilation, and `G3ZqRegU` for the unscaled field along the path; plus the standard path
facts (continuity, simple-chord trace, continuous driving function starting at `0`, boundary
limits of the inverse Loewner maps).

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

open G3Z2b2 G1Zm

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The field regularity (area-only, D93) of an unscaled field `W` and a path `a` used by the
two-point rescaling identity at window `U` and level `L`. -/
def G3ZqResclFieldReg (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (W : FieldSample) (a : ℝ≥0 → ℝ)
    (U L : ℝ) : Prop :=
  (∀ᵐ x ∂(qBoundaryMeasure γ (canonical γ W)),
      x ∈ g1zWedgeWin γ true (canonical γ W) U →
        G3Zr.G3FacRegA γ L Ψ (canonical γ W) (scalePath (scaleParam γ W) a) x) ∧
    (∀ x ∈ g1SideHalf true,
      DilReg γ W (scaleParam γ W) x
        (g1zLocMap true (pathDrive (γ ^ 2) (scalePath (scaleParam γ W) a))
          (x / scaleParam γ W)) ∧
      DilReg γ W (scaleParam γ W) (R18.g3zPartner γ W x)
        (g1zLocMap false (pathDrive (γ ^ 2) (scalePath (scaleParam γ W) a))
          (R18.g3zPartner γ W x / scaleParam γ W))) ∧
    (∀ᵐ x ∂(qBoundaryMeasure γ W), x ∈ g1zWedgeWin γ true W U →
      G3ZqRegU γ L Ψ true W a x ∧ 0 < R18.g3zPartner γ W x ∧
        G3ZqRegU γ L Ψ false W a (R18.g3zPartner γ W x))

/-- **Almost-sure field regularity for the two-point rescaling identity (open leaf).** For the
wedge representative and an independent Brownian motion, for all `U, L`: a.s. the unscaled field
and its canonical description are good with positive scale, and a.s. in the Brownian sample the
conditions `G3ZqResclFieldReg` hold along its path. -/
def G3ZqResclRegStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    (∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) →
  ∀ (U L : ℝ), ∀ᵐ ω' ∂P', 0 < scaleParam γ (wedgeU γ X A ω') ∧
    IsLQGGood γ (wedgeU γ X A ω') ∧ IsLQGGood γ (wedgeRep γ X A ω') ∧
    ∀ᵐ ω ∂P, G3ZqResclFieldReg γ Ψ (wedgeU γ X A ω') (pathOf B ω) U L

theorem continuous_scalePath {b : ℝ} {a : ℝ≥0 → ℝ} (hac : Continuous a) :
    Continuous (scalePath b a) := by
  unfold scalePath
  exact (hac.comp (continuous_const.mul continuous_id)).div_const b

/-- **`G3ZqResclIdStmt` from the a.s. field regularity** (the path facts are `ae_goodPathF`). -/
theorem g3ZqResclIdStmt_of_reg (h : G3ZqResclRegStmt) : G3ZqResclIdStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω _ P _ B hB hsc U L s t hs ht
  have hsm := measurableSet_lawCyl hs
  have htm := measurableSet_lawCyl ht
  have hgm : AEMeasurable (pathOf B) P := IsBrownianReal.aemeasurable_pathOf hB
  filter_upwards [h γ hγ hγ2 Ψ hsel P' X A hX hA hXA P B hB hsc U L] with ω' ⟨hb, hWg, hy, hae⟩
  refine ⟨hb, ?_⟩
  set b := scaleParam γ (wedgeU γ X A ω') with hbdef
  have hm1 : Measurable fun a : ℝ≥0 → ℝ =>
      g3PhiM2 γ L Ψ U s t (wedgeRep γ X A ω', scalePath b a) :=
    (measurable_g3PhiM2 hsel L U hsm htm).comp (measurable_const.prodMk (measurable_scalePath b))
  have hm2 : Measurable fun a : ℝ≥0 → ℝ => g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a) :=
    (measurable_g3PhiM2 hsel L U hsm htm).comp (measurable_const.prodMk measurable_id)
  refine (ae_map_iff hgm (measurableSet_eq_fun hm1 hm2)).2 ?_
  filter_upwards [hae, ae_goodPathF hγ hγ2 hB hsc] with ω ⟨hreg1, hdil, hreg3⟩ hgood
  obtain ⟨hac, hs', hWd, hW0, hex⟩ := hgood
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b (pathOf B ω))) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs'
  exact g3PhiM2_canonical_scalePath hγ hsel hac hs' hWd hW0 hex hWg hb (continuous_scalePath hac)
    hsb (G1ZA1a.isNormalizedUniformizer_sideDom hsb true)
    (G1ZA1a.isNormalizedUniformizer_sideDom hsb false) hy U L s t hreg1 hdil hreg3

end G3Zq
end Thm18Asm
end QuantumZipper

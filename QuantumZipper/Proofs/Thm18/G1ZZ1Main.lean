import QuantumZipper.Proofs.Thm18.G1ZZ1Field
import QuantumZipper.Proofs.Thm18.G1ZZ1Meas
import QuantumZipper.Proofs.Thm18.G1CoreScale
import QuantumZipper.Proofs.Thm18.G1CoreSplit
import QuantumZipper.Proofs.Thm18.G1Z2ReflChord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-Z1 (3): `G1PalmToWedgeStmt` (Theorem 1.8, G1 zoom, decision D66)

`g1PalmToWedgeStmt_of : G1RegExStmt → G1SideTransportIdStmt → G1PalmToWedgeStmt`.

Route (Sheffield, arXiv:1012.4797, pp. 69–71). Fix `ω` outside a null set. The side boundary
measure is `ν_side = (ν_Y|_S).map Φ⁻¹` with `Φ` the boundary values of the side map `ψ`
(`G1SideTransportIdStmt`), so the Palm-window integral over `ν_side` becomes, by the
`MeasurableEquiv` change of variables `window_transport` (G1ZZ1Meas), the Palm-window integral over
`ν_Y|_S` of the integrand at `b = Φ⁻¹ x`; `b = g1zBdryPre x` (`g1zBdryPre_eq`, Carathéodory boundary
values of `ψ` from `SideReflGood`), and the integrands agree by the field identity
`regEq_side_zoomVia` (G1ZZ1Field) and `canonical_congr`. The regularity input (RC3 for the side
field) is `G1RegExStmt` transported to the chosen uniformizer (`choiceRegularCore_invFunOn_of_normalized`).

`G1SideTransportIdStmt` is `G1SideTransportStmt` with the transport map identified with the
boundary values of `ψ` (the `G1BdryGood` of `G1Z3Fixed` only gives *some* order isomorphism `Φ`,
which does not suffice: `∫ F(Φ⁻¹ x) dν_Y = ∫ F(ψ⁻¹|_∂ x) dν_Y` needs `Φ = ψ|_∂`).
It follows from `WedgeBdryAllMapsAwayStmt` (`g1SideTransportIdStmt_of_allMaps`, proof of
`g1SideTransportStmt_of`), and from the R2 route by adding the conjunct
`SideReflGood left (Ψ left p.1) Φ₀` to `G1Z4SideLimStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-- **Side transport with the map identified**: a.s. there is an order isomorphism `Φ`, the
boundary values of the side map `ψ` on the side half-line (`SideReflGood`), such that the side
boundary measure is the pullback of `ν_Y|_S` by `Φ`. -/
def G1SideTransportIdStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ᵐ ω ∂P, ∃ Φ : ℝ ≃o ℝ, SideReflGood left (g1zSideMap left (drive (γ ^ 2) B ω)) Φ ∧
      g1SideNu γ left (g1SideField γ B Y left ω) =
        ((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf left)).map Φ.symm

/-- **Z1: `G1PalmToWedgeStmt`** from the regularity half `G1RegExStmt` and the identified side
transport. -/
theorem g1PalmToWedgeStmt_of (hReg : G1RegExStmt) (hT : G1SideTransportIdStmt) :
    G1PalmToWedgeStmt := by
  intro γ Ω _ P _ B Y hS hIn left U hU C R Γ hΓ hΓ1
  have hγ : 0 < γ := hS.1
  have hReg' : G1RegExSide γ P B Y left := by
    cases left
    exacts [(hReg γ P B Y hS hIn).2, (hReg γ P B Y hS hIn).1]
  unfold g1PalmIntC g1zWedgePalmInt
  refine lintegral_congr_ae ?_
  filter_upwards [hT γ P B Y hS hIn left, hReg', ae_atomless_pos_wedge hS hIn, hIn.1, hIn.2.2]
    with ω ⟨Φ, hΦ, hν⟩ ⟨φ, hφ, hcore⟩ ⟨hatom, _⟩ ⟨hgood, _⟩ ⟨hsimp, _, hnL, hnR⟩
  have hu : IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)
      (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    cases left
    exacts [hnR, hnL]
  have hcore' := G1.choiceRegularCore_invFunOn_of_normalized hsimp left hφ hu hcore
  have hD : IsOpen (sideDom (sleTrace (γ ^ 2) B ω) left) := G1.isOpen_component hsimp left
  obtain ⟨-, -, hψm, hψD⟩ := G1.invFunOn_props hD hu
  have hDH : sideDom (sleTrace (γ ^ 2) B ω) left ⊆ H := by
    cases left
    exacts [rightComponent_subset_H _, leftComponent_subset_H _]
  obtain ⟨F, hF⟩ := hgood.1
  have hwin : g1Win γ left (g1SideField γ B Y left ω) U =
      {b | b ∈ g1SideHalf left ∧
        ((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf left)).map Φ.symm
          (g1SideSeg left b) ≤ ENNReal.ofReal U} := by
    unfold g1Win; rw [hν]
  rw [hwin, hν, G1ZZ1.window_transport hΦ.1 (hatom 0) left (ENNReal.ofReal U)]
  refine setLIntegral_congr_fun
    (G1ZZ1.measurableSet_win (qBoundaryMeasure γ (Y ω)) left (ENNReal.ofReal U)) ?_
  intro x hx
  have hxh : x ∈ g1SideHalf left := hx.1
  have hpre := G1ZZ1.g1zBdryPre_eq hΦ hxh
  have hreg := G1ZZ1.regEq_side_zoomVia hγ.ne' hF hψm (fun z hz => hDH (hψD hz))
    hcore'.2.1 (Φ.symm x) x C
  have hc := S5.FieldShift.canonical_congr hreg γ
  have hloc : g1zLocMap left (drive (γ ^ 2) B ω) x =
      fun w => g1zSideMap left (drive (γ ^ 2) B ω) (w + ((Φ.symm x : ℝ) : ℂ)) - (x : ℂ) := by
    unfold g1zLocMap; rw [hpre]
  beta_reduce
  rw [hloc]
  exact congrArg (fun z => Γ (D3Plus.locFieldFull R z)) hc

end Thm18Asm
end QuantumZipper

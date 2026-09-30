import QuantumZipper.Proofs.Thm18.G1ZB2CGeom
import QuantumZipper.Proofs.Thm18.G1ZA1bArea
import QuantumZipper.Proofs.Thm18.R18G3Const

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR (1): the shifted side regularity in area-only form (D89) and its consumers

Theorem 1.8, G1 zoom, node B2-C. Sheffield, arXiv:1012.4797, proof of Proposition 1.7
(pp. 25–26): adding a constant to the wedge field and re-embedding by Brownian scaling.

`G1SideShiftRegStmt` (G1ZB2CPath.lean) asks for `G1.ChoiceRegular` of the shifted field at the
side map. Its clause `IsLQGGood γ (coordChange (y + C) ψ Q)` contains a boundary limit of the
side field along the **whole** real line, i.e. also along the preimage of the SLE curve (the
quantum length of the curve seen from one side). The paper does not use it at this step, and the
consumer (`g1zB2c_data_eq`) only needs the *area-only* choice independence of the canonical data
(`G1ZA1b.g1za1b_dataFull_canonical_rescale`, as in A1b). Decision D89: the node is replaced by
`G1SideShiftRegAStmt`, where `G1.ChoiceRegular` is replaced by `G1.ChoiceRegularA` (regular
sample, RC3, an area limit, positive scale parameter, scale consistency at dilated test
measures). `G1SideShiftRegStmt → G1SideShiftRegAStmt` (`g1SideShiftRegAStmt_of_reg`), so this is a
genuine weakening; consumers are rewired through `g1SideShiftPathStmt_of_regA`.
Own bookkeeping (copy of `g1zB2c_data_eq` with the area-only step).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization CoordsFull

namespace G1

/-- **Area-only choice regularity** (D89): `ChoiceRegular` without the log-derivative clause and
with `IsLQGGood` replaced by "regular sample with an area limit". -/
def ChoiceRegularA (γ : ℝ) (y : FieldSample) (ψ : ℂ → ℂ) : Prop :=
  IsRegularSample (coordChange y ψ (Qc γ)) ∧
  (∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange y ψ (Qc γ)) (foldedCircle d r) =
      coordChange y ψ (Qc γ) (foldedCircle d r)) ∧
  (∃ μ : Measure ℂ, HasAreaLimit γ (coordChange y ψ (Qc γ)) μ) ∧
  0 < scaleParam γ (coordChange y ψ (Qc γ)) ∧
  ∀ b : ℝ, 0 < b → ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
    ScaleConsistentAt (coordChange y ψ (Qc γ)) (Qc γ) b
      ((tmeas σ).map fun z => (c : ℂ) * z)

end G1

/-- The shifted regularity package in area-only form (D89), for a general side map `ψ`. -/
def ShiftRegA (γ : ℝ) (y : FieldSample) (C : ℝ) (ψ : ℂ → ℂ) : Prop :=
  G1.ChoiceRegularA γ (addConst y C) ψ ∧
  (∀ d : ℂ, ∀ r > 0, E1.RegShift y ((foldedCircle d r).map ψ)) ∧
  ∀ b : ℝ, 0 < b → ∀ d : ℂ, ∀ r > 0,
    G1.ScaleConsistentAt (addConst y C) (Qc γ) (scaleParam γ (addConst y C))
      ((foldedCircle d r).map
        (fun w => ((scaleParam γ (addConst y C) : ℝ) : ℂ)⁻¹ * ψ ((b : ℂ) * w)))

/-- **A.s. regularity of the shifted field, area-only form** (node, D89). -/
def G1SideShiftRegAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ C : ℝ, ∀ᵐ ω ∂P,
      ShiftRegA γ (Y ω) C (g1zSideMap left (drive (γ ^ 2) B ω))

/-- **The pathwise identity, deterministic form, area-only** (copy of `g1zB2c_data_eq`). -/
theorem g1ssr_data_eq {γ : ℝ} (hγ : 0 < γ) {y : FieldSample} (C : ℝ) {ψ ψs : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    (hint : ∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    {b : ℝ} (hb : 0 < b) (hs : 0 < scaleParam γ (addConst y C))
    (hgeom : EqOn ψs (fun w => ((scaleParam γ (addConst y C) : ℝ) : ℂ)⁻¹ * ψ ((b : ℂ) * w)) H)
    (hreg : G1.ChoiceRegularA γ (addConst y C) ψ)
    (hshift : ∀ d : ℂ, ∀ r > 0, E1.RegShift y ((foldedCircle d r).map ψ))
    (hsc : ∀ d : ℂ, ∀ r > 0, G1.ScaleConsistentAt (addConst y C) (Qc γ)
      (scaleParam γ (addConst y C)) ((foldedCircle d r).map
        (fun w => ((scaleParam γ (addConst y C) : ℝ) : ℂ)⁻¹ * ψ ((b : ℂ) * w)))) :
    WedgeMeas.dataFull H (canonical γ (addConst (coordChange y ψ (Qc γ)) C)) =
      WedgeMeas.dataFull H (canonical γ (coordChange (canonical γ (addConst y C)) ψs (Qc γ))) := by
  set z := addConst y C with hz
  set s := scaleParam γ z with hsdef
  -- Step A: constants commute with the pull-back at folded circles
  have hA : avgReg (addConst (coordChange y ψ (Qc γ)) C) = avgReg (coordChange z ψ (Qc γ)) := by
    funext k w
    unfold avgReg
    congr 1
    funext n
    rw [hz, F2.coordChange_addConst_fc C (hshift _ _ (radius_pos k))]
    simp [addConst]
  -- Step B: the pull-back of the rescaled field is the pull-back by the dilated chart
  have hB : avgReg (coordChange (canonical γ z) ψs (Qc γ)) =
      avgReg (coordChange z (fun w => ψ ((b : ℂ) * w)) (Qc γ)) := by
    funext k w
    unfold avgReg
    congr 1
    funext n
    have hr := radius_pos k
    have hchart := g1zB2c_scaled_chart hψ0 hint hs hb (dyadicRoundC n w) hr
    have hψsm : Measurable (fun w : ℂ => (s : ℂ)⁻¹ * ψ ((b : ℂ) * w)) :=
      measurable_const.mul (hψm.comp (measurable_const_mul _))
    show coordChange (rescale z (Qc γ) s) ψs (Qc γ) _ = _
    rw [g1zMeas_coordChange_fc_congr (rescale z (Qc γ) s) hgeom (Qc γ) _ hr,
      G1Meas.coordChange_rescale_apply z hψsm (Qc γ) hs _ (hsc _ _ hr) hchart.1 hchart.2]
    congr 1
    funext u
    exact mul_inv_cancel_left₀ (by exact_mod_cast hs.ne') _
  -- Step C: area-only choice independence
  obtain ⟨hrg, hex, ⟨μ, hμ⟩, hsx, hscx⟩ := hreg
  have hR := G1.regEq_coordChange_comp_mul z (Qc γ) hψd hψ0 hψm hb hint hex
  have hC : WedgeMeas.dataFull H (canonical γ (coordChange z (fun w => ψ ((b : ℂ) * w)) (Qc γ))) =
      WedgeMeas.dataFull H (canonical γ (coordChange z ψ (Qc γ))) := by
    rw [Factorization.canonical_congr (B3d.avgReg_eq_of_regEq hR) γ]
    exact G1ZA1b.g1za1b_dataFull_canonical_rescale hγ hrg hμ hb hsx
      fun ρ σ hσ => hscx b hb _ (div_pos hsx hb) ρ σ hσ
  rw [Factorization.canonical_congr hA γ, Factorization.canonical_congr hB γ]
  exact hC.symm

/-- **`G1SideShiftPathStmt` from the geometry and the area-only shifted regularity.** -/
theorem g1SideShiftPathStmt_of_regA (hG : G1SideShiftGeomStmt) (hR : G1SideShiftRegAStmt) :
    G1SideShiftPathStmt := by
  intro γ Ω _ P _ B Y hS hIn left C
  obtain ⟨hpos, -, -, -⟩ := canonConfig_shift_facts hS C
  filter_upwards [hpos, hR γ P B Y hS hIn left C, hIn.2.2, ae_g1zDrvGood hS hIn]
    with ω hs hreg hω hW
  set η := sleTrace (γ ^ 2) B ω with hη
  have hu : IsNormalizedUniformizer (if left then leftComponent η else rightComponent η)
      (uniformizer (if left then leftComponent η else rightComponent η)) := by
    cases left
    · exact hω.2.2.2
    · exact hω.2.2.1
  have hD := G1.isOpen_component hω.1 left
  obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props hD hu
  have hint := G1.choiceRegular_logDeriv hD hu
  obtain ⟨b, hb, hgeom⟩ := hG _ hW _ hs left
  exact g1ssr_data_eq hS.1 (y := Y ω) C hψd hψ0 hψm hint hb hs hgeom hreg.1 hreg.2.1
    (hreg.2.2 b hb)

/-- **B2-C** from A2 and the area-only shifted regularity. -/
theorem g1SideConstInvStmt_of_regA (hF : G1RerootFactorStmt) (hR : G1SideShiftRegAStmt) :
    G1SideConstInvStmt :=
  g1SideConstInvStmt_of hF (g1SideShiftPathStmt_of_regA g1SideShiftGeomStmt_holds hR)

/-- **Step 2 of route (b)** (G3) from A2 and the area-only shifted regularity. -/
theorem g3JointConstInvStmt_of_regA (hF : G1RerootFactorStmt) (hR : G1SideShiftRegAStmt) :
    R18.G3JointConstInvStmt :=
  R18.g3JointConstInvStmt_of hF (g1SideShiftPathStmt_of_regA g1SideShiftGeomStmt_holds hR)

end Thm18Asm
end QuantumZipper

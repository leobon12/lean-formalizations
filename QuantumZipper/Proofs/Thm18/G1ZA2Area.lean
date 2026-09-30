import QuantumZipper.Proofs.Thm18.G1ZA2Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A2, part 4: shrinking the input of A2 to the small-mass clause

`G1A2GoodSetStmt` (G1ZA2Main.lean) is the measurable-set form of `G1Z2SideGoodStmt`. Here its
existence half is proved: the area limit and the side boundary limit of the selected field are
detected by the countable certificates `AreaCert` (GoodMeasurable.lean) and `SideCert`
(G1Z5SideCert.lean), which are measurable in the data on the regular set. What remains is only the
clause with an uncountable quantifier ("`μ` has mass `< 1` near every real point and infinite total
mass"), in the named node `G1A2SmallTopStmt`.

`g1A2GoodSetStmt_of : G1Z2SideGoodStmt → G1A2SmallTopStmt → G1A2GoodSetStmt`,
`g1RerootFactorStmt_of' : G1Z2SideGoodStmt → G1A2SmallTopStmt → G1RerootFactorStmt`.

Own bookkeeping (Sheffield–Wang, arXiv:1605.06171, Thm 1.4, for the a.s. content).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- **Node A2-ST (small mass near real points, infinite total mass, measurable-set form).**
There is a measurable set `E₁` of (path, wedge data) pairs of full law such that for `p ∈ E₁` with
continuous simple path, every area limit `μ` of the selected pulled-back field has mass `< 1`
near every real point and infinite total mass. The clause quantifies over all real points, so it
is not manifestly a measurable set of data (the path space is not Polish, so Lusin's theorem does
not apply); it is the measurable form of the last two clauses of `G1Z2MeasGood`. -/
def G1A2SmallTopStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ → ∀ left : Bool,
    ∃ E₁ : Set G1PathData, MeasurableSet E₁ ∧
      (∀ p ∈ E₁, Continuous p.1 → IsSimpleChord (pathTrace (γ ^ 2) p.1) →
        ∀ μ : Measure ℂ, HasAreaLimit γ (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ)) μ →
          (∀ q : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (q : ℂ) a ∩ H) < 1) ∧ μ H = ⊤) ∧
      ∀ᵐ ω ∂P, (pathOf B ω, WedgeMeas.dataFull H (Y ω)) ∈ E₁

namespace G1ZA2

theorem areaCert_congr {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    GoodMeas.AreaCert γ x ↔ GoodMeas.AreaCert γ x' := by
  have hb : areaR γ x = areaR γ x' := by
    funext r; unfold areaR areaDens evalReg; rw [h]
  simp only [GoodMeas.AreaCert, GoodMeas.CauchyA, GoodMeas.aI, hb]

theorem measurableSet_areaCert {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) : MeasurableSet {p : G1PathData | GoodMeas.AreaCert γ (xc γ Ψ left p)} := by
  have e : {p : G1PathData | GoodMeas.AreaCert γ (xc γ Ψ left p)} =
      xh γ Ψ left ⁻¹' {x | GoodMeas.AreaCert γ x} := by
    ext p
    simp only [mem_setOf_eq, mem_preimage]
    exact (areaCert_congr (avgReg_xh γ Ψ left p)).symm
  rw [e]
  exact measurable_xh hΨ left (measurableSet_setOfPred.2 (GoodMeas.measurable_AreaCert γ))

end G1ZA2

/-- **The good set from the small-mass node and the goodness node.** -/
theorem g1A2GoodSetStmt_of (hG : G1Z2SideGoodStmt) (hST : G1A2SmallTopStmt) :
    G1A2GoodSetStmt := by
  intro γ Ω _ P _ B Y hS hIn Ψ hΨ left
  obtain ⟨Est, hEstm, hEstp, hEstae⟩ := hST γ P B Y hS hIn Ψ hΨ left
  refine ⟨Est ∩ {p | GoodMeas.AreaCert γ (G1ZA2.xc γ Ψ left p)} ∩ G1ZA2.SetS γ Ψ left,
    (hEstm.inter (G1ZA2.measurableSet_areaCert hΨ left)).inter (G1ZA2.measurableSet_SetS hΨ left),
    ?_, ?_⟩
  · rintro p ⟨⟨hEst, hAC⟩, ⟨⟨F, hF⟩, hSC⟩⟩ hc hs
    obtain ⟨μ, hμ⟩ := GoodMeas.hasAreaLimit_of_cert hF hAC
    obtain ⟨hsm, htop⟩ := hEstp p hEst hc hs μ hμ
    obtain ⟨ν, hν⟩ := G1Z5.sideLim_of_cert hF hSC
    exact ⟨⟨μ, hμ, hsm, htop⟩, ⟨ν, hν⟩⟩
  · have hreg := g1z2_ae_isRegularSample (g1RegExStmt_of_rest g1RegRepRestStmt_holds) γ hS hIn hΨ
      left
    filter_upwards [hEstae, hG γ P B Y hS hIn left, hreg, hS.2.2.1.cont, hIn.2.2]
      with ω h1 hgood h2 hc hin
    have hη : IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω)) := hin.1
    obtain ⟨φ₀, hφ₀, hΨe⟩ := hΨ.2.2 (pathOf B ω) hc hη left
    have hM : G1Z2MeasGood γ left (g1z2Field γ Ψ B Y left ω) := by
      unfold g1z2Field
      rw [hΨe]
      exact hgood φ₀ hφ₀
    have hx : G1ZA2.xc γ Ψ left (pathOf B ω, WedgeMeas.dataFull H (Y ω)) =
        g1z2Field γ Ψ B Y left ω :=
      (g1z2_coordChange_congr (Cor15Group.regEq_fromC_coordsFull (Y ω)) _ _).symm
    obtain ⟨⟨μ, hμ, -, -⟩, ⟨ν, hν⟩⟩ := hM
    refine ⟨⟨h1, ?_⟩, ?_, ?_⟩
    · rw [Set.mem_setOf_eq, hx]
      exact GoodMeas.areaCert_of_hasAreaLimit hμ
    · rw [hx]; exact h2
    · rw [hx]; exact G1Z5.sideCert_of_lim hν

/-- **A2 from the goodness node and the small-mass node.** -/
theorem g1RerootFactorStmt_of' (hG : G1Z2SideGoodStmt) (hST : G1A2SmallTopStmt) :
    G1RerootFactorStmt :=
  g1RerootFactorStmt_of (g1A2GoodSetStmt_of hG hST)

end Thm18Asm
end QuantumZipper

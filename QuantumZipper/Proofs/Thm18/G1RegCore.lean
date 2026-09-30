import QuantumZipper.Proofs.Thm18.G1RegCanon
import QuantumZipper.Proofs.Thm18.G1Reduce

/-!
# G1-REG, part 3: the reduced G1 core (Theorem 1.8, node G1)

`G1CoreStmt` (G1Reduce.lean) asks, per side, for an a.s. choice `ψ = φ⁻¹` of inverse normalized
uniformizer with (a) the wedge law of the canonical description and (b) `G1.ChoiceRegular`
a.s. Of the five clauses of (b):

* (i) is deterministic (`G1.choiceRegular_logDeriv`, Koebe distortion);
* (iii) and (iv) follow from the wedge law (a) itself, per sample
  (`G1.isLQGGood_of_canonical`, `G1.scaleParam_pos_of_canonical`, with the a.s. goodness and
  unit area of a `γ`-wedge, `IsQuantumWedge.ae_unitArea`, `γ < Q`);
* (v) is taken in its PAIR-LIM form (`G1.choiceRegular_of_continuum`).

What remains of (b) is `G1.ChoiceRegularCore`: the pulled-back field `x = coordChange y ψ Q` is
a regular sample (RC2 analogue), its folded-circle values are its regularized ones (RC3
analogue), and its circle-smoothed pairings with dilated test measures converge (PAIR-LIM
analogue). `g1Stmt_of_coreReg : G1CoreRegStmt → G1Stmt`.

Own argument (bookkeeping).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1

/-- The part of `ChoiceRegular` not implied by the wedge law and Koebe distortion: RC2 (regular
sample), RC3 (folded-circle values are regularized values), PAIR-LIM (continuum limit of the
circle-smoothed pairings against dilated test measures). -/
def ChoiceRegularCore (γ : ℝ) (y : FieldSample) (ψ : ℂ → ℂ) : Prop :=
  IsRegularSample (coordChange y ψ (Qc γ)) ∧
  (∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange y ψ (Qc γ)) (foldedCircle d r) =
      coordChange y ψ (Qc γ) (foldedCircle d r)) ∧
  ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
    (∀ s : ℝ, 0 < s → Integrable (fun u => evalReg (coordChange y ψ (Qc γ)) (foldedCircle u s))
      ((tmeas σ).map fun z => (c : ℂ) * z)) ∧
    ∃ L : ℝ, Tendsto (fun s => ∫ u, evalReg (coordChange y ψ (Qc γ)) (foldedCircle u s)
      ∂((tmeas σ).map fun z => (c : ℂ) * z)) (𝓝[>] 0) (𝓝 L)

/-- **`ChoiceRegular` from `ChoiceRegularCore`** and the goodness and unit area of the canonical
description (per sample). -/
theorem choiceRegular_of_core {γ : ℝ} (hγ : 0 < γ) {y : FieldSample} {D : Set ℂ}
    (hD : IsOpen D) {φ : ℂ → ℂ} (hφ : IsNormalizedUniformizer D φ)
    (hcore : ChoiceRegularCore γ y (invFunOn φ D))
    (hgood : IsLQGGood γ (canonical γ (coordChange y (invFunOn φ D) (Qc γ))))
    (h1 : qAreaMeasure γ (canonical γ (coordChange y (invFunOn φ D) (Qc γ)))
      (ball 0 1 ∩ H) = 1) :
    ChoiceRegular γ y (invFunOn φ D) := by
  obtain ⟨hreg, hexact, hpair⟩ := hcore
  have hs := scaleParam_pos_of_canonical hγ h1
  exact choiceRegular_of_continuum (choiceRegular_logDeriv hD hφ) hexact
    (isLQGGood_of_canonical hγ hreg hexact hs hgood) hs hpair

end G1

theorem gamma_lt_Qc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < Qc γ := by
  unfold Qc
  have h : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]; nlinarith
  linarith

/-- **G1 core, one side, reduced**: as `G1SideCore`, with `G1.ChoiceRegular` replaced by
`G1.ChoiceRegularCore`. -/
def G1SideCoreReg (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (left : Bool) : Prop :=
  ∃ ψ : Ω → ℂ → ℂ,
    (∀ᵐ ω ∂P, ∃ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ ∧
      ψ ω = invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left) ∧
      G1.ChoiceRegularCore γ (Y ω) (ψ ω)) ∧
    IsQuantumWedge γ γ (fun ω => canonical γ (coordChange (Y ω) (ψ ω) (Qc γ))) P

theorem g1SideCore_of_reg {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y)
    (hIn : Thm18Inputs γ P B Y) {left : Bool} (h : G1SideCoreReg γ P B Y left) :
    G1SideCore γ P B Y left := by
  obtain ⟨hγ, hγ2, -⟩ := hS
  obtain ⟨ψ, hψ, hw⟩ := h
  have hα := gamma_lt_Qc hγ hγ2
  have hU := WedgeMeasND.IsQuantumWedge.ae_unitArea
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα)
    hγ hγ2 hw
  refine ⟨ψ, ?_, hw⟩
  filter_upwards [hψ, hIn.2.2, hU] with ω ⟨φ, hφ, hψe, hr⟩ hin ⟨hg, h1⟩
  refine ⟨φ, hφ, hψe, ?_⟩
  rw [hψe] at hr hg h1 ⊢
  exact G1.choiceRegular_of_core hγ (G1.isOpen_component hin.1 left) hφ hr hg h1

/-- **Reduced G1 core** (both sides). -/
def G1CoreRegStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    G1SideCoreReg γ P B Y true ∧ G1SideCoreReg γ P B Y false

theorem g1CoreStmt_of_reg (h : G1CoreRegStmt) : G1CoreStmt := by
  intro γ Ω _ P _ B Y hS hIn
  obtain ⟨hL, hR⟩ := h γ P B Y hS hIn
  exact ⟨g1SideCore_of_reg hS hIn hL, g1SideCore_of_reg hS hIn hR⟩

/-- `G1Stmt` from the reduced core. -/
theorem g1Stmt_of_coreReg (h : G1CoreRegStmt) : G1Stmt :=
  g1Stmt_of_core (g1CoreStmt_of_reg h)

end Thm18Asm
end QuantumZipper

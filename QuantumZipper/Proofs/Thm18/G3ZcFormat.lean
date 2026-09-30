import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.Thm18.G1ZoomWeighted
import QuantumZipper.Proofs.Zipper.D3PlusNonVac
import QuantumZipper.Proofs.Zipper.HeadlineWire2
import QuantumZipper.Proofs.NonVacuityWedgeUncond

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C (d), format conversion: `G1WApproxSeq` is the limit statement

`G1WApproxSeq γ R Γ ε a` asks for a weighted mixture of D3⁺ models (`α = γ`) whose weighted
model integrals approximate `a L`. By D3⁺(i) (`D3PlusIStmtRich`, proved:
`d3PlusIRich_of_N2 d3PlusIN2RichStmt_holds`) every such model integral converges to
`E w · E Γ(γ-wedge)`, so the mixture is only a way of saying that `a L` is eventually close to
`c = E Γ(locFieldFull R (γ-wedge))`. Conversely, if `a L` is eventually within `ε/2` of `c`, the
one-model mixture (a single free-field `Setup` with trivial side data, `g = 0`, weight `1`) is an
`ε`-approximation (`g1WApproxSeq_of_near`).

Consequence: `G1WedgePalmZoomStmt` (Z2 of G1Z-SPLIT, the open leaf of
`theorem1_8PaperMO_of_leaves6`) follows from the plain limit statement `G1WedgePalmLimStmt`:
for some window `U`, the normalized wedge Palm-window integral of the zooms through the local
maps is eventually within `ε` of the `γ`-wedge value. This is literally the paper's claim
(Sheffield, arXiv:1012.4797, p. 70–71: the zoom at a quantum-typical boundary point of the side
surface is a `γ`-quantum wedge, "as in Proposition 1.6"), with the D3⁺ model bookkeeping removed.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus

/-- **Format conversion.** If `a L` is eventually within `ε/2` of the `γ`-wedge value
`c = E Γ(locFieldFull R Y')`, then `G1WApproxSeq γ R Γ ε a` holds (one free-field D3⁺ model with
weight `1`; its model integrals converge to `c` by D3⁺(i)). -/
theorem g1WApproxSeq_of_near {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y' : Ω' → FieldSample} (hW : IsQuantumWedge γ γ Y' P') (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    {ε : ℝ≥0∞} (hε : 0 < ε) {a : ℝ → ℝ≥0∞}
    (ha : ∀ᶠ L in atTop, a L ≤ ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' + ε / 2 ∧
      ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' ≤ a L + ε / 2) :
    G1WApproxSeq γ R Γ ε a := by
  have hD3 : D3PlusIStmtRich := d3PlusIRich_of_N2 d3PlusIN2RichStmt_holds
  obtain ⟨Ω₀, _, P₀, X, hP₀, hS⟩ := exists_setup (r := 1) hγ hγ2 (gamma_lt_Qc hγ hγ2) one_pos
  set c := ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' with hc
  have hc1 : c ≤ 1 := g1z_lintegral_le_one hΓ1 _
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  -- the single model converges to `c`
  have hlim : Tendsto (fun L => g1zWMdl γ 1 L R (foldedCircle 0 (2 * 1)) P₀ X
      (fun _ _ => (0 : ℝ)) (fun _ => 1) Γ) atTop (𝓝 c) := by
    have h := g1zW_tendsto_of_D3 hD3 hS hW R hΓ hΓ1 (w := fun _ => 1) (M := 1)
      measurable_const (fun _ => by simp)
    simpa [hc] using h
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hev1 : ∀ᶠ L in atTop, g1zWMdl γ 1 L R (foldedCircle 0 (2 * 1)) P₀ X
      (fun _ _ => (0 : ℝ)) (fun _ => 1) Γ < c + ε / 2 :=
    hlim.eventually (gt_mem_nhds (ENNReal.lt_add_right hctop hε2.ne'))
  have hev2 : ∀ᶠ L in atTop, c ≤ g1zWMdl γ 1 L R (foldedCircle 0 (2 * 1)) P₀ X
      (fun _ _ => (0 : ℝ)) (fun _ => 1) Γ + ε / 2 := by
    by_cases hc0 : c = 0
    · exact Eventually.of_forall fun L => by rw [hc0]; exact bot_le
    · filter_upwards [hlim.eventually (lt_mem_nhds (ENNReal.sub_lt_self hctop hc0 hε2.ne'))]
        with L hL
      exact tsub_le_iff_right.1 hL.le
  have hmass : ∫⁻ _x : Unit, ∫⁻ _ω, (1 : ℝ≥0∞) ∂P₀ ∂(Measure.dirac ()) = 1 := by
    simp
  refine ⟨Unit, inferInstance, Measure.dirac (), fun _ => 1, fun _ => foldedCircle 0 (2 * 1),
    Ω₀, inferInstance, P₀, fun _ => X, Unit, inferInstance, fun _ _ => (), fun _ _ _ => 0,
    fun _ _ => 1, 1, inferInstance, hP₀, fun _ => hS, fun _ => measurable_const,
    fun _ _ => by simp, fun _ => Subsingleton.measurable.aemeasurable,
    Subsingleton.measurable.aemeasurable, ?_, ?_, ?_⟩
  · rw [hmass]; exact le_self_add
  · rw [hmass]; exact le_self_add
  · filter_upwards [ha, hev1, hev2] with L h h1 h2
    have hint : ∫⁻ _x : Unit, g1zWMdl γ 1 L R (foldedCircle 0 (2 * 1)) P₀ X
        (fun _ _ => (0 : ℝ)) (fun _ => 1) Γ ∂(Measure.dirac ()) =
        g1zWMdl γ 1 L R (foldedCircle 0 (2 * 1)) P₀ X (fun _ _ => (0 : ℝ)) (fun _ => 1) Γ := by
      simp
    rw [hint]
    constructor
    · calc _ ≤ c + ε / 2 := h1.le
        _ ≤ a L + ε / 2 + ε / 2 := add_le_add h.2 le_rfl
        _ = a L + ε := by rw [add_assoc, ENNReal.add_halves]
    · calc a L ≤ c + ε / 2 := h.1
        _ ≤ _ + ε / 2 + ε / 2 := add_le_add h2 le_rfl
        _ = _ + ε := by rw [add_assoc, ENNReal.add_halves]

/-- **The Palm zoom limit (Z2, plain form).** For every side, local radius `R`, measurable
`Γ ∈ [0,1]` and `ε > 0` there is a window `U > 0` and a `γ`-quantum wedge `Y'` such that the
normalized wedge Palm-window integral of the zooms through the local maps is eventually (in the
level `L`) within `ε` of `E Γ(locFieldFull R Y')` (Sheffield, arXiv:1012.4797, pp. 70–71). -/
def G1WedgePalmLimStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ R : ℕ, ∀ Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ U : ℝ, 0 < U ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (Y' : Ω' → FieldSample),
        IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ Y' P' ∧
        ∀ᶠ L in atTop,
          (ENNReal.ofReal U)⁻¹ * g1zWedgePalmInt γ P B Y left U L R Γ ≤
              ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' + ε ∧
            ∫⁻ ω', Γ (locFieldFull R (Y' ω')) ∂P' ≤
              (ENNReal.ofReal U)⁻¹ * g1zWedgePalmInt γ P B Y left U L R Γ + ε

/-- **Z2 from its plain limit form** (format conversion `g1WApproxSeq_of_near`). -/
theorem g1WedgePalmZoomStmt_of_lim (h : G1WedgePalmLimStmt) : G1WedgePalmZoomStmt := by
  intro γ Ω _ P _ B Y hS hIn left R Γ hΓ hΓ1 ε hε
  obtain ⟨U, hU, Ω', _, P', Y', hP', hW, hev⟩ :=
    h γ P B Y hS hIn left R Γ hΓ hΓ1 (ε / 2) (ENNReal.half_pos hε.ne')
  exact ⟨U, hU, g1WApproxSeq_of_near hS.1 hS.2.1 hW R hΓ hΓ1 hε hev⟩

end Thm18Asm
end QuantumZipper

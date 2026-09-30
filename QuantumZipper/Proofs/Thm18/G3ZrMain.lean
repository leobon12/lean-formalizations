import QuantumZipper.Proofs.Thm18.G3ZrTr3
import QuantumZipper.Proofs.Thm18.G3ZrWire2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (9): the window regularity of the zoom step, a.s. at every boundary point

* **`ae_g1FacRegA`**: in the Theorem 1.8 setting, a.s., the area-only window regularity
  `G1FacRegA` holds at **every** point `x` of the side half-line, from the side-area leaf
  `G1Z2SideGoodStmt` (area limit of the pulled-back side field, finite near real points, infinite
  in total; already a hypothesis of the headlines) and proved nodes: the side core
  `G1RegExSide` (`g1RegExStmt_of_rest g1RegRepRestStmt_holds`), the continuum smoothing limit at
  the side map (`g1SidePushContStmt_holds`) and `choiceRegularA_translate`.
  No Palm transfer is needed: the conditions hold at every `x`, so in particular at
  boundary-measure-a.e. window point.
* **`g1zWedgePalmInt_fubini_side`**, **`g3zWedgePalmCyl_fubini_side`**: the curve Fubini formulas
  of G3Z2B with the regularity hypothesis discharged (for the two-point one, up to the positivity
  of the length partner `R(x)`, a hypothesis about the wedge alone).

Sheffield, arXiv:1012.4797, pp. 69–71. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **The area-only window regularity holds a.s. at every point of the side half-line.** -/
theorem ae_g1FacRegA (hZ2 : G1Z2SideGoodStmt) (γ : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (hsel : G1PsiSel γ Ψ)
    (left : Bool) (L : ℝ) :
    ∀ᵐ ω ∂P, ∀ x ∈ g1SideHalf left, G1FacRegA γ L Ψ left (Y ω) (pathOf B ω) x := by
  have hB : IsBrownianReal B P := hS.2.2.1
  have hR : G1RegExSide γ P B Y left := by
    have := g1RegExStmt_of_rest g1RegRepRestStmt_holds γ P B Y hS hIn
    cases left
    · exact this.2
    · exact this.1
  filter_upwards [ae_g1FacReg_shift γ P B Y hS hIn hsel left, hR, hZ2 γ P B Y hS hIn left,
    g1SidePushContStmt_holds γ P B Y hS hIn left, hIn.1, hIn.2.2, hB.cont]
    with ω hsh hRω hZω hNω hYω hin hc
  obtain ⟨φ₀, hφ₀, hcore₀⟩ := hRω
  obtain ⟨hsc, -, hNl, hNr⟩ := hin
  rw [sleTrace_eq_pathTrace] at hsc hNl hNr hφ₀ hcore₀ hZω
  simp only [drive_eq_pathDrive] at hNω
  set a := pathOf B ω with ha
  have hN := normalized_side left hNl hNr
  obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 a hc hsc left
  have hcore : G1.ChoiceRegularCore γ (Y ω) (Ψ left a) := by
    rw [hΨa]; exact G1.choiceRegularCore_invFunOn_of_normalized hsc left hφ₀ hφ hcore₀
  obtain ⟨⟨μ, hμ, hsm, htop⟩, -⟩ := hZω φ hφ
  rw [← hΨa] at hμ
  have hΨm : Measurable (Ψ left a) := (hsel.1 left).comp (measurable_const.prodMk measurable_id)
  have hΨH : MapsTo (Ψ left a) H H := by
    obtain ⟨-, -, -, hD⟩ := G1.invFunOn_props (G1.isOpen_component hsc left) hφ
    rw [hΨa]
    exact fun w hw => G1ZA1a.sideDom_subset_H _ left (hD hw)
  -- continuum limits along the pushed circles of `Ψ left a`
  obtain ⟨c, hcpos, hEq⟩ := side_unique hsc hN hφ
  obtain ⟨hψm, -⟩ := sideMap_facts hsc left hN
  have hdil : Ψ left a = g1zSideMap left (pathDrive (γ ^ 2) a) ∘ fun z => ((c⁻¹ : ℝ) : ℂ) * z := by
    funext z
    rw [hΨa, invFunOn_dilate hN hφ hcpos hEq z]
    simp only [Function.comp]
    congr 1
    push_cast
    ring
  have hNΨ : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData (Y ω) ((foldedCircle d r).map (Ψ left a)) := by
    intro d r hr
    rw [hdil, ← Measure.map_map hψm (measurable_const_mul _),
      IndepParams.fc_map_mul' _ _ (inv_pos.2 hcpos)]
    exact hNω _ _ (mul_pos (inv_pos.2 hcpos) hr)
  intro x hx
  obtain ⟨h1, h2⟩ := hsh x hx
  refine ⟨h1, h2, ?_⟩
  have hg : g3mapP Ψ left (Y ω, a, 1, x) =
      fun w => Ψ left a (w + (g3bpre Ψ left a (x / 1) : ℂ)) - (x : ℂ) := by
    funext w
    simp [g3mapP, g3mapB, g3locM]
  rw [hg]
  exact choiceRegularA_translate hYω.1.1 hΨm hΨH hcore hμ hsm htop hNΨ _ x (L / γ)

/-- **The two-point curve Fubini formula with the window regularity discharged**, up to the
positivity of the length partner. -/
theorem g3zWedgePalmCyl_fubini_side (hZ2 : G1Z2SideGoodStmt) (γ : ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y)
    (hsel : G1PsiSel γ Ψ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' ∧ IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' ∧
      IndepFun X (fun ω t => A t ω) P' ∧
      ∀ (U L : ℝ) (s t : Set LawD), MeasurableSet s → MeasurableSet t →
        (∀ᵐ ω ∂P, ∀ᵐ x ∂(qBoundaryMeasure γ (Y ω)), x ∈ g1zWedgeWin γ true (Y ω) U →
          0 < R18.g3zPartner γ (Y ω) x) →
        R18.g3zWedgePalmCyl γ P B Y U L s t =
          ∫⁻ a, ∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeRep γ X A ω', a) ∂P' ∂(P.map (pathOf B)) := by
  obtain ⟨Ω', _, P', hP', X, A, hX, hA, hXA, H⟩ := g3zWedgePalmCyl_fubiniA γ P B Y hS hIn hsel
  refine ⟨Ω', inferInstance, P', hP', X, A, hX, hA, hXA, fun U L s t hs ht hpos =>
    H U L s t hs ht ?_⟩
  filter_upwards [ae_g1FacRegA hZ2 γ P B Y hS hIn hsel true L,
    ae_g1FacRegA hZ2 γ P B Y hS hIn hsel false L, hpos] with ω h1 h2 hp
  filter_upwards [hp] with x hx hw
  have hpx := hx hw
  exact ⟨h1 x hw.1, hpx, h2 _ (by simpa [g1SideHalf] using hpx)⟩

end G3Zr
end Thm18Asm
end QuantumZipper

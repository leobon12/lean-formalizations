import QuantumZipper.Proofs.Thm18.G1CoreScale

/-!
# G1-CORE, part 2: splitting `G1CoreRegStmt` into the zoom half and the regularity half

`G1CoreRegStmt` (G1RegCore.lean) asks, per side, for one `ψ : Ω → ℂ → ℂ` with
(a) the wedge law of the canonical description (the zoom lemma) and (b') a.s. `ψ ω` is the
inverse of a normalized uniformizer of the side component and `G1.ChoiceRegularCore γ (Y ω) (ψ ω)`.
Since `ChoiceRegularCore` does not depend on the normalization
(`G1.choiceRegularCore_invFunOn_of_normalized`, G1CoreScale.lean), the two halves decouple:

* `G1ZoomPartStmt`: (a), for some a.s. choice of inverse normalized uniformizer (any
  normalization, e.g. the measurable KT2 one);
* `G1RegPartStmt`: (b') for **every** normalized uniformizer, a.s.;
* `G1RegExStmt`: (b') for **some** normalized uniformizer, a.s. (the form a prover would
  establish, for a measurable choice of normalization).

`g1CoreRegStmt_of_parts : G1ZoomPartStmt → G1RegPartStmt → G1CoreRegStmt`,
`g1RegPartStmt_of_ex : G1RegExStmt → G1RegPartStmt`, so
`g1Stmt_of_zoom_regEx : G1ZoomPartStmt → G1RegExStmt → G1Stmt`.

Own argument (bookkeeping); the mathematical content is Sheffield, arXiv:1012.4797, §1.6 (remark
after (1.8)) and §5.4.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **G1 regularity half (b'), one side, every normalization**: a.s., for every normalized
uniformizer `φ` of the side component of `ℍ \ η`, the pulled-back field
`Y ∘ φ⁻¹ + Q log |(φ⁻¹)'|` satisfies `G1.ChoiceRegularCore`. -/
def G1RegPartSide (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (left : Bool) : Prop :=
  ∀ᵐ ω ∂P, ∀ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ →
    G1.ChoiceRegularCore γ (Y ω) (invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left))

/-- **G1 regularity half (b')**, both sides, in the Theorem 1.8 setting. -/
def G1RegPartStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    G1RegPartSide γ P B Y true ∧ G1RegPartSide γ P B Y false

/-- **G1 regularity half, existential form**, one side: a.s. `ChoiceRegularCore` holds for the
inverse of *some* normalized uniformizer of the side component. -/
def G1RegExSide (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (left : Bool) : Prop :=
  ∀ᵐ ω ∂P, ∃ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ ∧
    G1.ChoiceRegularCore γ (Y ω) (invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left))

/-- **G1 regularity half, existential form**, both sides. -/
def G1RegExStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    G1RegExSide γ P B Y true ∧ G1RegExSide γ P B Y false

/-- **G1 zoom half (a)**, one side: for some a.s. choice `ψ ω` of inverse normalized uniformizer
of the side component, the canonical description of `Y ∘ ψ + Q log |ψ'|` is a `γ`-quantum
wedge. -/
def G1ZoomPartSide (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (left : Bool) : Prop :=
  ∃ ψ : Ω → ℂ → ℂ,
    (∀ᵐ ω ∂P, ∃ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ ∧
      ψ ω = invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left)) ∧
    IsQuantumWedge γ γ (fun ω => canonical γ (coordChange (Y ω) (ψ ω) (Qc γ))) P

/-- **G1 zoom half (a)**, both sides. -/
def G1ZoomPartStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    G1ZoomPartSide γ P B Y true ∧ G1ZoomPartSide γ P B Y false

theorem g1SideCoreReg_of_parts {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} {left : Bool}
    (hZ : G1ZoomPartSide γ P B Y left) (hR : G1RegPartSide γ P B Y left) :
    G1SideCoreReg γ P B Y left := by
  obtain ⟨ψ, hψ, hw⟩ := hZ
  refine ⟨ψ, ?_, hw⟩
  filter_upwards [hψ, hR] with ω ⟨φ, hφ, hψe⟩ hr
  exact ⟨φ, hφ, hψe, hψe ▸ hr φ hφ⟩

/-- **`G1CoreRegStmt` from its two halves.** -/
theorem g1CoreRegStmt_of_parts (hZ : G1ZoomPartStmt) (hR : G1RegPartStmt) : G1CoreRegStmt := by
  intro γ Ω _ P _ B Y hS hIn
  obtain ⟨hZL, hZR⟩ := hZ γ P B Y hS hIn
  obtain ⟨hRL, hRR⟩ := hR γ P B Y hS hIn
  exact ⟨g1SideCoreReg_of_parts hZL hRL, g1SideCoreReg_of_parts hZR hRR⟩

theorem g1RegPartSide_of_ex {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hIn : Thm18Inputs γ P B Y) {left : Bool}
    (h : G1RegExSide γ P B Y left) : G1RegPartSide γ P B Y left := by
  filter_upwards [h, hIn.2.2] with ω ⟨φ₀, h₀, hc⟩ hin φ hφ
  exact G1.choiceRegularCore_invFunOn_of_normalized hin.1 left h₀ hφ hc

/-- **Every-normalization regularity from some-normalization regularity** (U6 +
`G1.choiceRegularCore_invFunOn_of_normalized`). -/
theorem g1RegPartStmt_of_ex (h : G1RegExStmt) : G1RegPartStmt := by
  intro γ Ω _ P _ B Y hS hIn
  obtain ⟨hL, hR⟩ := h γ P B Y hS hIn
  exact ⟨g1RegPartSide_of_ex hIn hL, g1RegPartSide_of_ex hIn hR⟩

/-- **G1 from the zoom half and the (existential) regularity half.** -/
theorem g1Stmt_of_zoom_regEx (hZ : G1ZoomPartStmt) (hR : G1RegExStmt) : G1Stmt :=
  g1Stmt_of_coreReg (g1CoreRegStmt_of_parts hZ (g1RegPartStmt_of_ex hR))

end Thm18Asm
end QuantumZipper

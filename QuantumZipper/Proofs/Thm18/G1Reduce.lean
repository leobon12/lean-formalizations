import QuantumZipper.Proofs.Thm18.G1Rescale

/-!
# G1, part 2: `G1Stmt` from a choice-free core (Theorem 1.8, node G1)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, proof of
Theorem 1.8: "that `(D₁, h)` is a `γ`-wedge follows from Proposition 1.6 … and the right side by
symmetry". The Palm-zoom argument (D4⁺, E5, G0, KT2) naturally produces the wedge law for the
canonical description built from *some* normalized uniformizer `φ` of the component (for KT2:
the left-normalized one, `φ(−1) = −1`), whereas `componentSurface` uses the
`Classical.epsilon`-chosen `uniformizer`. This file closes that gap (THM18-ASM mismatch 1):

* `G1SideCore γ P B Y left`: there is a choice `ψ ω = φ_ω⁻¹` of inverse normalized uniformizer
  of the component, a.s., whose pulled-back field is `ChoiceRegular` a.s., and whose canonical
  description is a `γ`-wedge;
* `isQuantumWedge_componentSurface_of_sideCore`: then `componentSurface γ B Y left` is a
  `γ`-wedge (U6 + `G1.data_canonical_coordChange_eq`: the `fieldLawFull` data coincide a.s.);
* `G1CoreStmt`, `g1Stmt_of_core : G1CoreStmt → G1Stmt`.

Own argument (bookkeeping on top of `G1Rescale`); the mathematical content is Sheffield §1.6
(canonical descriptions do not depend on the parametrization) and U6.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The component of `ℍ \ η` on the given side. -/
abbrev sideDom (η : ℝ → ℂ) (left : Bool) : Set ℂ :=
  if left then leftComponent η else rightComponent η

/-- **G1 core, one side.** Some a.s. choice `ψ ω = (φ_ω)⁻¹` of inverse normalized uniformizer of
the side component, whose pulled-back field `h ∘ ψ + Q log|ψ'|` is a.s. `ChoiceRegular`, has a
`γ`-quantum wedge as canonical description. This is what the Palm-zoom argument of G1 (D4⁺, E5,
G0, KT2) produces, for the KT2-normalized `φ`. -/
def G1SideCore (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (left : Bool) : Prop :=
  ∃ ψ : Ω → ℂ → ℂ,
    (∀ᵐ ω ∂P, ∃ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ ∧
      ψ ω = invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left) ∧ G1.ChoiceRegular γ (Y ω) (ψ ω)) ∧
    IsQuantumWedge γ γ (fun ω => canonical γ (coordChange (Y ω) (ψ ω) (Qc γ))) P

/-- **G1 core** (both sides), with the Theorem 1.8 setting and the proved inputs as premises. -/
def G1CoreStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    G1SideCore γ P B Y true ∧ G1SideCore γ P B Y false

/-- `componentSurface` unfolds to the canonical description for the chosen `uniformizer`. -/
theorem componentSurface_eq (γ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (left : Bool) (ω : Ω) :
    componentSurface γ B Y left ω = canonical γ (coordChange (Y ω)
      (invFunOn (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left))
        (sideDom (sleTrace (γ ^ 2) B ω) left)) (Qc γ)) := rfl

/-- **G1 from its core, one side.** -/
theorem isQuantumWedge_componentSurface_of_sideCore {γ : ℝ} (hγ : 0 < γ) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hIn : Thm18Inputs γ P B Y) {left : Bool} (hcore : G1SideCore γ P B Y left) :
    IsQuantumWedge γ γ (componentSurface γ B Y left) P := by
  obtain ⟨ψ, hψ, hα, Ω', mΩ', P', X, A, hP', hX, hA, hXA, hlaw⟩ := hcore
  refine ⟨hα, Ω', mΩ', P', X, A, hP', hX, hA, hXA, ?_⟩
  rw [← hlaw]
  unfold fieldLawFull
  refine Measure.map_congr ?_
  filter_upwards [hIn.2.2, hψ] with ω hin hω
  obtain ⟨hη, -, huL, huR⟩ := hin
  obtain ⟨φ, hφ, hψeq, hreg⟩ := hω
  have hu : IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)
      (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    cases left
    · exact huR
    · exact huL
  obtain ⟨b, hb, heq⟩ := G1.exists_invFunOn_uniformizer_eq hη left hφ hu
  obtain ⟨hd, h0, hm, -⟩ := G1.invFunOn_props (G1.isOpen_component hη left) hφ
  rw [hψeq] at hreg ⊢
  rw [componentSurface_eq]
  exact G1.data_canonical_coordChange_eq hγ (Y ω) hd h0 hm hb heq hreg

/-- **G1 from its core.** -/
theorem g1Stmt_of_core (h : G1CoreStmt) : G1Stmt := by
  intro γ Ω _ P _ B Y hS hIn
  obtain ⟨hL, hR⟩ := h γ P B Y hS hIn
  exact ⟨isQuantumWedge_componentSurface_of_sideCore hS.1 hIn hL,
    isQuantumWedge_componentSurface_of_sideCore hS.1 hIn hR⟩

end Thm18Asm
end QuantumZipper

import QuantumZipper.Proofs.Thm18.G1RegRepMeas

/-!
# G1-REGREP, part 4: `G1RegRepStmt` from a measurable selection, RC2 per path, and the rest

`ChoiceRegularCore γ y ψ` is RC2 (`IsRegularSample` of the pulled-back field) plus
`G1.CoreRest γ y ψ` (RC3 at every folded circle and PAIR-LIM). This file assembles the good set
of `G1RegRepStmt` (G1CoreRep.lean) as `E = E' ∩ {RC2 for both sides}`, where

* the RC2 part is measurable in (path, data) given the selection (`G1Meas.measurableSet_rc2`)
  and holds almost surely by `G1RegRepRC2Stmt` (for a.e. path, both sides, a.s. in the field;
  the fixed-chord Kolmogorov argument `G1Kolm.ae_isRegularSample_of_raw` is the tool);
* `E'` is a measurable set of pairs on which `CoreRest` holds (`G1RegRepRestStmt`).

`g1RegRepStmt_of_parts : G1PsiSelStmt → G1RegRepRC2Stmt → G1RegRepRestStmt → G1RegRepStmt`.

Own argument (bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

namespace G1

/-- The clauses of `ChoiceRegularCore` other than RC2: RC3 at every folded circle and
PAIR-LIM. -/
def CoreRest (γ : ℝ) (y : FieldSample) (ψ : ℂ → ℂ) : Prop :=
  (∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange y ψ (Qc γ)) (foldedCircle d r) =
      coordChange y ψ (Qc γ) (foldedCircle d r)) ∧
  ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
    (∀ s : ℝ, 0 < s → Integrable (fun u => evalReg (coordChange y ψ (Qc γ)) (foldedCircle u s))
      ((tmeas σ).map fun z => (c : ℂ) * z)) ∧
    ∃ L : ℝ, Tendsto (fun s => ∫ u, evalReg (coordChange y ψ (Qc γ)) (foldedCircle u s)
      ∂((tmeas σ).map fun z => (c : ℂ) * z)) (nhdsWithin 0 (Ioi 0)) (nhds L)

theorem choiceRegularCore_iff (γ : ℝ) (y : FieldSample) (ψ : ℂ → ℂ) :
    ChoiceRegularCore γ y ψ ↔ IsRegularSample (coordChange y ψ (Qc γ)) ∧ CoreRest γ y ψ :=
  Iff.rfl

end G1

/-- Input (1): a measurable selection of inverse normalized uniformizers exists. -/
def G1PsiSelStmt : Prop := ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ Ψ, G1PsiSel γ Ψ

/-- The setting of `G1RegRepStmt`, followed by a conclusion `C`. -/
def G1RepSetting (C : ∀ (_γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (_P : Measure Ω)
    (_B : ℝ≥0 → Ω → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (_P' : Measure Ω')
    (_X : Ω' → FieldSample) (_A : ℝ → Ω' → ℝ), Prop) : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' → C γ P B P' X A

/-- **RC2 half**: for a.e. path and every side, the pulled-back representative is a.s. a regular
sample, for every measurable selection. -/
def G1RegRepRC2Stmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      IsRegularSample (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))

/-- **The rest** (RC3 at every circle and PAIR-LIM) on a measurable set of full measure. -/
def G1RegRepRestStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∃ E' : Set G1PathData, MeasurableSet E' ∧
      (∀ p ∈ E', ∀ left : Bool, G1.CoreRest γ (E1.fromC p.2.1) (Ψ left p.1)) ∧
      ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
        (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E'

theorem g1RegRepStmt_of_parts (hS : G1PsiSelStmt) (h2 : G1RegRepRC2Stmt)
    (h3 : G1RegRepRestStmt) : G1RegRepStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA
  obtain ⟨Ψ, hΨ⟩ := hS γ hγ hγ2
  obtain ⟨E', hE'm, hE'g, hE'ae⟩ := h3 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ
  set R : Bool → Set G1PathData := fun left =>
    {p | IsRegularSample (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))} with hR
  refine ⟨E' ∩ (R true ∩ R false), hE'm.inter ((G1Meas.measurableSet_rc2 hΨ true).inter
    (G1Meas.measurableSet_rc2 hΨ false)), ?_, ?_⟩
  · rintro p ⟨hp, hpt, hpf⟩
    refine G1Meas.g1RegGood_of_core hΨ fun left => ?_
    refine (G1.choiceRegularCore_iff _ _ _).2 ⟨?_, hE'g p hp left⟩
    cases left
    · exact hpf
    · exact hpt
  · filter_upwards [hE'ae, h2 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a ha1 ha2
    filter_upwards [ha1, ha2 true, ha2 false] with ω' h1 ht hf
    have hc : ∀ left, IsRegularSample (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ)) →
        (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ R left := fun left h => by
      show IsRegularSample (coordChange (E1.fromC (CoordsFull.coordsFull (wedgeRep γ X A ω')))
        (Ψ left a) (Qc γ))
      rwa [Factorization.coordChange_congr (CoordsFull.avgReg_congr_full
        (E1.coordsFull_fromC (wedgeRep γ X A ω')))]
    exact ⟨h1, hc true ht, hc false hf⟩

end Thm18Asm
end QuantumZipper

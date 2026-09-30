import QuantumZipper.Proofs.Thm18.G1CoreSplit
import QuantumZipper.Proofs.Thm11.CharFunRhs
import QuantumZipper.Proofs.Probability.BrownianPathMeas

/-!
# G1-CORE, part 3: the independence/Fubini step of the regularity half

`G1RegExStmt` (G1CoreSplit.lean) is an a.s. statement about the pair (SLE path, wedge field),
which are independent in the Theorem 1.8 setting. This file reduces it to a statement about the
**product** of their laws, i.e. to a fixed path and an independent wedge field:

`G1RegFixedStmt`: there is a measurable set `E` of pairs (Brownian path `a`, wedge data `c`) such
that (good) whenever `(a, c) ∈ E`, `a` is continuous and the trace driven by `√κ a` is a simple
chord, every field
`y` with data `c` satisfies `G1.ChoiceRegularCore` for the inverse of some normalized uniformizer
of each side component; and (full) for `P.map (pathOf B)`-a.e. path `a`, `(a, c) ∈ E` for
`fieldLawFull H Y P`-a.e. `c`.

`g1RegExStmt_of_fixed : G1RegFixedStmt → G1RegExStmt` (independence: `CharFunRhs.ae_indep_ae`,
with a.e.-measurable modifications of the path map, `IsBrownianReal.aemeasurable_pathOf`, and
of the data map, `Thm18Inputs`). Since `ChoiceRegularCore γ y ψ` depends on `y` only through
`avgReg y`, hence through `coordsFull y` (`G1.choiceRegularCore_congr_avgReg`), (good) only
concerns the data, and (full) only the laws: for a fixed path it may be proved for any
representative of the wedge law (e.g. `canonical γ (wedgeField (lateralPart X) A Q)`).

Own argument (Fubini/independence bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The chordal SLE trace driven by `√κ a` for a deterministic path `a`
(`sleTrace κ B ω = pathTrace κ (pathOf B ω)` by definition). -/
def pathTrace (κ : ℝ) (a : ℝ≥0 → ℝ) : ℝ → ℂ :=
  trace fun t => Real.sqrt κ * a t.toNNReal

theorem sleTrace_eq_pathTrace {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    sleTrace κ B ω = pathTrace κ (pathOf B ω) := rfl

/-- The data space of `fieldLawFull H` and the path space. -/
abbrev G1PathData : Type := (ℝ≥0 → ℝ) × ((ℕ → ℝ) × (TestFun H → ℝ))

/-- The good pairs (path, wedge data): if the path is continuous and its trace is a simple chord,
every field with these data satisfies the regularity package on both sides, for some
normalization. (Continuity is needed: a measurable set of paths for the product σ-algebra is
determined by countably many coordinates, so it cannot exclude discontinuous junk paths.) -/
def G1RegGood (γ : ℝ) (p : G1PathData) : Prop :=
  Continuous p.1 → IsSimpleChord (pathTrace (γ ^ 2) p.1) → ∀ y : FieldSample, WedgeMeas.dataFull H y = p.2 →
    ∀ left : Bool, ∃ φ : ℂ → ℂ,
      IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) p.1) left) φ ∧
      G1.ChoiceRegularCore γ y (invFunOn φ (sideDom (pathTrace (γ ^ 2) p.1) left))

/-- **G1 regularity half, product form** (fixed path, independent wedge field). -/
def G1RegFixedStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∃ E : Set G1PathData, MeasurableSet E ∧ (∀ p ∈ E, G1RegGood γ p) ∧
      ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ c ∂(fieldLawFull H Y P), (a, c) ∈ E

namespace G1

/-- `ChoiceRegularCore γ y ψ` depends on `y` only through `avgReg y`. -/
theorem choiceRegularCore_congr_avgReg {γ : ℝ} {y y' : FieldSample} (h : avgReg y = avgReg y')
    (ψ : ℂ → ℂ) : ChoiceRegularCore γ y ψ ↔ ChoiceRegularCore γ y' ψ := by
  unfold ChoiceRegularCore
  rw [Factorization.coordChange_congr h ψ (Qc γ)]

/-- ... hence only through `coordsFull y`. -/
theorem choiceRegularCore_congr_coordsFull {γ : ℝ} {y y' : FieldSample}
    (h : CoordsFull.coordsFull y = CoordsFull.coordsFull y') (ψ : ℂ → ℂ) :
    ChoiceRegularCore γ y ψ ↔ ChoiceRegularCore γ y' ψ :=
  choiceRegularCore_congr_avgReg (CoordsFull.avgReg_congr_full h) ψ

end G1

theorem measurable_dataFull_H : Measurable (WedgeMeas.dataFull H) :=
  CoordsFull.measurable_coordsFull.prodMk
    (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _))

/-- **Independence/Fubini step**: the product form gives the a.s. form. -/
theorem g1RegExStmt_of_fixed (h : G1RegFixedStmt) : G1RegExStmt := by
  intro γ Ω _ P _ B Y hS hIn
  obtain ⟨E, hE, hgood, hae⟩ := h γ P B Y hS hIn
  obtain ⟨-, -, hB, -, hind⟩ := hS
  have hgm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have hdm : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P := hIn.2.1
  have hind' : IndepFun (hgm.mk _) (hdm.mk _) P :=
    (hind.comp measurable_id measurable_dataFull_H).congr hgm.ae_eq_mk hdm.ae_eq_mk
  have h1 : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, (hgm.mk _ ω, hdm.mk _ ω') ∈ E := by
    filter_upwards [ae_of_ae_map hgm hae, hgm.ae_eq_mk] with ω hω hω'
    filter_upwards [ae_of_ae_map hdm hω, hdm.ae_eq_mk] with ω' h2 h3
    rw [← hω', ← h3]; exact h2
  have h2 := CharFunRhs.ae_indep_ae hgm.measurable_mk hdm.measurable_mk hind' hE h1
  have hall : ∀ᵐ ω ∂P, ∀ left : Bool, ∃ φ : ℂ → ℂ,
      IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ ∧
      G1.ChoiceRegularCore γ (Y ω) (invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    filter_upwards [h2, hgm.ae_eq_mk, hdm.ae_eq_mk, hIn.2.2, hB.cont] with ω hω e1 e2 hin hc
    rw [← e1, ← e2] at hω
    exact hgood _ hω hc hin.1 (Y ω) rfl
  exact ⟨hall.mono fun ω h => h true, hall.mono fun ω h => h false⟩

/-- **G1 from the zoom half and the product-form regularity half.** -/
theorem g1Stmt_of_zoom_regFixed (hZ : G1ZoomPartStmt) (hR : G1RegFixedStmt) : G1Stmt :=
  g1Stmt_of_zoom_regEx hZ (g1RegExStmt_of_fixed hR)

end Thm18Asm
end QuantumZipper

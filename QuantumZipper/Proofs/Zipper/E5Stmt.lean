import QuantumZipper.Proofs.Zipper.E1Main
import QuantumZipper.Zipper.LengthZip
import QuantumZipper.LQG.Wedge
import QuantumZipper.Blueprint.External2

/-!
# E5 (zoom identification): the statement

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, node **E5**; Lean text copied verbatim from
`handoff/E-PLAN-2-statements.lean.txt` (`EPLAN2.Setup`, `EPLAN2.E5Stmt`), namespace changed to
`QuantumZipper.E5`. Paper: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 / Thm 1.3 (§5,
PDF pp. 66–69).

`E5Stmt loc` is the two-sided `ℝ≥0∞` TV-local form of
"`(𝐏|_{τ_x < T}).map (Z_C ∘ C̄_x) → p · P_*` TV-locally as `C → ∞`": for every `R`, every
`η > 0`, eventually in `C`, for all measurable `Γ ≤ 1` on the local data,
`|∫⁻∫⁻_{x ∈ [−δ,0], τ_x < T} Γ(loc R (Z_C C̄_x)) dν dP − p · E_{P_*} Γ(loc R ·)| ≤ η`.
It is stated without `Measure.map` (E-PLAN-2 flag 5: no junk `map` of a non-measurable map).

`loc` is a parameter: it is meant to be the local data map `locData` of E_BRANCH §2
(`TV.locField R` of the field together with the driver stopped at the exit of its hull from
`B_R`), which is not defined yet (TASKS R12 / S5-TV). **The statement is only meaningful for that
`loc`**; for an arbitrary `loc` (e.g. one reading the whole configuration) it is false.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5
open B2 E1 CoordsFull

/-- Common setup of the Palm-zip nodes (identical to `EPLAN2.Setup`). -/
def Setup (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) (ϖ : Measure ℂ) : Prop :=
  0 < κ ∧ κ < 4 ∧ 0 < T ∧ IsBrownianReal B P ∧ IsFreeGFFModConstH X P ∧
    IndepFun (pathOf B) X P ∧ IsNormalizer ϖ

/-- **E5** (zoom identification), relative to the local data map `loc` (identical to
`EPLAN2.E5Stmt`). -/
def E5Stmt (loc : ℕ → FieldSample × (ℝ → ℝ) → (ℕ → ℝ) × (ℝ≥0 → ℝ)) : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
    Blueprint.RevCouplingBoundaryMeasureRegular → Setup κ T P B X ϖ →
    IsQuantumWedge (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) Y P' →
    IsBrownianReal B' P' → IndepFun Y (pathOf B') P' → ∀ δ : ℝ, 0 < δ →
    let pm : ℝ≥0∞ := ∫⁻ ω, nuPalm κ T B X ϖ ω
      {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} ∂P
    let zc : ℝ → Ω → ℝ → FieldSample × (ℝ → ℝ) := fun C ω x =>
      canonConfig (Real.sqrt κ) (addConst (collided κ T B X ω x).1
        (-(mReg κ T B X ϖ ω) + C / Real.sqrt κ), (collided κ T B X ω x).2)
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ C in atTop,
      ∀ Γ : (ℕ → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
        let lhs := ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
          {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}.indicator
            (fun x => Γ (loc R (zc C ω x))) x ∂nuPalm κ T B X ϖ ω ∂P
        let rhs := pm * ∫⁻ ω', Γ (loc R (Y ω', drive κ B' ω')) ∂P'
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

end E5
end QuantumZipper

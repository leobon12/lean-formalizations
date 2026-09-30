import QuantumZipper.Proofs.Zipper.E5Stmt
import QuantumZipper.Statements.Thm13
import QuantumZipper.Statements.ConfigLaw

/-!
# Theorem 1.3, top-level assembly: the node statements (THM13-ASM)

Statements (no proofs) of the E/F nodes of `blueprint/E_BRANCH_BLUEPRINT.md` that Theorem 1.3
(`theorem1_3`, Sheffield arXiv:1012.4797, §5.4, pp. 70–72) still needs, in the form in which the
assembly `Thm13Asm.theorem1_3_of_nodes` (`Thm13Assembly.lean`) consumes them. Each node that is
proved *from* an earlier node is stated as an implication (its owner proves it with the earlier
node as hypothesis, as `E6.e6_concrete` already does with `E5.E5Stmt`):

* `E4Stmt` — E4 (field at collision), verbatim `EPLAN2.E4Stmt` of
  `handoff/E-PLAN-2-statements.lean.txt` (owner: E4-LIM/E4, `Proofs/Zipper/E4Lim*.lean`);
* `E5NodeStmt loc := E4Stmt → E5.E5Stmt loc` (owner: E5; D3⁺, E-SM, E5a enter its proof);
* `E6NodeStmt loc := E5.E5Stmt loc → E6LocStmt loc` (owner: E6, `E6Concrete.e6_concrete` plus
  its side inputs E6-ID, B5 locality, measurability, and an auxiliary Palm setup);
* `E6UpStmt loc := E6LocStmt loc → E6Stmt` (local laws for all `R` ⇒ `configLawFull`; new gap);
* `F1NodeStmt := E6Stmt → F1Stmt` (owner: F1a–F1c; F1d core `F1.f1cd_lengths_agree` is proved);
* `F2NodeStmt := F1Stmt → Thm13LenStmt` (owner: F2, steps (1)–(4) of SECTION5 F2).

`E6Stmt` and `F1Stmt` are the blueprint's E6 and F1, for samples of `P_*` in the form used by
`E5.E5Stmt` (`IsQuantumWedge γ α₀ Y`, `B'` Brownian, `IndepFun Y (pathOf B')`, driver
`drive κ B'`). `Thm13LenStmt` is clause 2 of `theorem1_3` (with the base pair, D9) verbatim.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm13Asm
open B2 E1 CoordsFull

/-! ## E4 (verbatim `EPLAN2.targetColl`, `EPLAN2.E4Stmt`) -/

/-- The collision target field: `targetField` with `F x` replaced by `0`. -/
def targetColl (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (Y : FieldSample) : FieldSample :=
  addConst (PalmNorm.normAt (varpiT V t ϖ)
    (ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0) + Y)) (-(qt κ V t ϖ))

/-- **E4** (field at collision), un-normalized, `coordsFull` only, collision strictly before `T`
(verbatim `EPLAN2.E4Stmt`, with `EPLAN2.Setup = E5.Setup`). -/
def E4Stmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X' : Ω' → FieldSample),
    Blueprint.RevCouplingBoundaryMeasureRegular → E5.Setup κ T P B X ϖ →
    IsFreeGFFModConstH X' P' → ∀ δ : ℝ,
    ∀ Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞, ∀ Φ : (ℕ → ℝ) → ℝ≥0∞,
    Measurable (Function.uncurry Ψ) → Measurable Φ →
    let τ : Ω → ℝ → ℝ := fun ω x => (realHitTime (Vr κ T B ω) x).toReal
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}.indicator
        (fun x => Ψ x (Vstop κ T (τ ω x) B ω, W0p κ T B ω) *
          Φ (coordsFull (addConst (Yf κ T (τ ω x) B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}.indicator
        (fun x => Ψ x (Vstop κ T (τ ω x) B ω, W0p κ T B ω) *
          ∫⁻ ω', Φ (coordsFull (targetColl κ (Vr κ T B ω) (τ ω x) ϖ (X' ω'))) ∂P') x
        ∂nuPalm κ T B X ϖ ω ∂P

/-- The local-data type of `E5.E5Stmt`. -/
abbrev LocMap := ℕ → FieldSample × (ℝ → ℝ) → (ℕ → ℝ) × (ℝ≥0 → ℝ)

/-! ## `P_*` samples, E6, F1 -/

/-- A sample of `P_*` as in `E5.E5Stmt`: `Y` a `(γ, γ − 2/γ)`-quantum wedge, `B'` a standard
Brownian motion independent of `Y`, `γ = √κ`, `κ ∈ (0,4)`; the configuration is
`(Y ω, drive κ B' ω)`. -/
def IsPStarSample (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ) : Prop :=
  0 < κ ∧ κ < 4 ∧ IsQuantumWedge (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) Y P' ∧
    IsBrownianReal B' P' ∧ IndepFun Y (pathOf B') P'

/-! ## F2 -/

/-- Clause 2 of `theorem1_3` (lengths agree at welded pairs, base pair included, D9), verbatim. -/
def Thm13LenStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P,
      ∀ xm xp : ℝ, xm < 0 → 0 < xp →
        revMapBdry (drive κ B ω) T xm = revMapBdry (drive κ B ω) T xp →
        revMapBdry (drive κ B ω) T xm ∈ insert 0 (revHull (drive κ B ω) T) →
        qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
            (Set.Icc xm 0) =
          qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
            (Set.Icc 0 xp)

end Thm13Asm
end QuantumZipper

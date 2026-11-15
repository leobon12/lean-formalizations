/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSafeConst
import InteractingSLE.Spec.Sec7.StripWallMeanFull

/-!
# The two-angle strip system: the strip system of Aux. lemma 130 restricted to the programs its pocket word uses

Packet PROVE-WORDSAFE. Theorem 1.2's expanded wiring (`Wire.theorem12Statement_night_expanded`) takes, for each
both-low index, a full `StripSys.IsStripSystem` of the supplied word objects (`hWordS`): staged histories of the strip
field for **every** boundary-continued program. PROVE-STRIPSYS-SAFE showed that this is not R48-constructible (a
program whose third angle lies strictly between the first two needs Theorem 1.2 outside the (4.4) regime). The pocket
word of Aux. lemma 130 (pp. 408–413) only runs

* the constant-angle paths `η_θ` (`R7Aux131.constSpec θ`; among them the unchanged extremal path `β = η_{π/2}`), and
* the two-angle paths `η^{t₀,∞}_{θ₀,θ}` (`StripSys.twoAngleSpec θ₀ t₀ θ`; among them `α = η^{1,∞}_{−π/2,θ₁}` and
  `β^{(r)} = η^{r,∞}_{π/2,θ₂}` of (RS13.1)).

Every such program is a *record-angle* program (its last angle is at least, or at most, every earlier angle), the class
PROVE-STRIPSYS-SAFE §4 identifies as reachable by the R48-safe (4.4) determination (directly, or after the reflection
`z ↦ −z̄`).

* **`IsTwoAngleStripSystem`**: `IsStripSystem` with its staged histories required only for those programs (same field
  names, plus `stagedTwoAngle`);
* `IsStripSystem.toTwoAngle`, `IsTwoAngleStripSystem.toConst` (to PROVE-STRIPSYS-SAFE's `IsConstStripSystem`);
* `IsTwoAngleStripSystem.isStagedHistory_alpha`, `…_beta`, `…_leftExtremal`: the methods the pocket-word proofs call;
* **`isTwoAngle_regStrip`**: the regularized family `StripWall.regStrip` of a two-angle strip system is one again.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.WordSafe

open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open R7Aux131 (constSpec)
open Theorem14.StagedReg (regHist isStagedHistory_regHist)

/-- **The two-angle strip system**: `StripSys.IsStripSystem` with its staged histories required only for the
constant-angle programs `constSpec θ` and the two-angle programs `twoAngleSpec θ₀ t₀ θ`, all angles in `[−π/2, π/2]`
(the incoming paths of Aux. lemmas 130–131 and (RS13.1)). The field names are those of `IsStripSystem` and
`StripSafe.IsConstStripSystem`. -/
structure IsTwoAngleStripSystem (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop where
  kappa_pos : 0 < κ
  kappa_lt_four : κ < 4
  boundaryData : IsPiecewiseConstantBoundaryData b jumps
  gff : IsGFFWithBoundaryData P h b jumps
  counterflow : IsCenteredCounterflowDriver κ P h W' ζ'
  lifetime : ∀ᵐ ω ∂P, ζ' ω = ⊤
  staged : ∀ θ : ℝ, θ ∈ Icc (-(π / 2)) (π / 2) → IsStagedHistory κ b jumps P h (constSpec θ) (E (constSpec θ))
  stagedTwoAngle : ∀ {θ₀ θ : ℝ}, θ₀ ∈ Icc (-(π / 2)) (π / 2) → θ ∈ Icc (-(π / 2)) (π / 2) → ∀ t₀ : ℝ≥0,
    IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) (E (StripSys.twoAngleSpec θ₀ t₀ θ))

section System

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- Every strip system is a two-angle strip system. -/
theorem _root_.InteractingSLE.Sec7.StripSys.IsStripSystem.toTwoAngle
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E) : IsTwoAngleStripSystem κ b jumps P h W' ζ' E :=
  ⟨hS.kappa_pos, hS.kappa_lt_four, hS.boundaryData, hS.gff, hS.counterflow, hS.lifetime,
    fun _ hθ => R7Aux131.isStagedHistory_const hS hθ,
    fun hθ₀ hθ t₀ => hS.staged _ (StripSys.isBoundaryContinuedProgram_twoAngleProg hθ₀ hθ t₀)⟩

/-- A two-angle strip system is a constant-angle strip system. -/
theorem IsTwoAngleStripSystem.toConst (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E) :
    StripSafe.IsConstStripSystem κ b jumps P h W' ζ' E :=
  ⟨hS.kappa_pos, hS.kappa_lt_four, hS.boundaryData, hS.gff, hS.counterflow, hS.lifetime, hS.staged⟩

/-- The drivers of `α = η^{1,∞}_{−π/2,θ₁}` form a staged history of `h`. -/
theorem IsTwoAngleStripSystem.isStagedHistory_alpha (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E) {θ₁ : ℝ}
    (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) :
    IsStagedHistory κ b jumps P h (StripSys.alphaSpec θ₁) (E (StripSys.alphaSpec θ₁)) :=
  hS.stagedTwoAngle StripSys.neg_pi_div_two_mem_Icc hθ₁ 1

/-- The drivers of `β^{(r)} = η^{r,∞}_{π/2,θ₂}` form a staged history of `h`. -/
theorem IsTwoAngleStripSystem.isStagedHistory_beta (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E) {θ₂ : ℝ}
    (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0) :
    IsStagedHistory κ b jumps P h (StripSys.betaSpec r θ₂) (E (StripSys.betaSpec r θ₂)) :=
  hS.stagedTwoAngle StripSys.pi_div_two_mem_Icc hθ₂ r

/-- The drivers of the unchanged extremal path `β = η_{π/2}` form a staged history of `h`. -/
theorem IsTwoAngleStripSystem.isStagedHistory_leftExtremal (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E) :
    IsStagedHistory κ b jumps P h StripSys.leftExtremalSpec (E StripSys.leftExtremalSpec) :=
  hS.staged _ StripSys.pi_div_two_mem_Icc

/-- The staged history of one program under the regularized family `StripWall.regStrip`. -/
theorem isStagedHistory_regStrip (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec}
    (hE : IsStagedHistory κ b jumps P h spec (E spec)) :
    IsStagedHistory κ b jumps P h spec (StripWall.regStrip κ b jumps P E spec) := by
  classical
  by_cases hR : StagedPiecesRegular κ b jumps P spec (E spec)
  · rw [StripWall.regStrip_of hR]
    exact isStagedHistory_regHist hb hE hR
  · simp only [StripWall.regStrip, hR, ↓reduceIte]
    exact hE

/-- **The regularized family of a two-angle strip system is again a two-angle strip system** (port of
`StripWall.isStripSystem_regStrip`). -/
theorem isTwoAngle_regStrip (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E) :
    IsTwoAngleStripSystem κ b jumps P h W' ζ' (StripWall.regStrip κ b jumps P E) :=
  ⟨hS.kappa_pos, hS.kappa_lt_four, hS.boundaryData, hS.gff, hS.counterflow, hS.lifetime,
    fun θ hθ => isStagedHistory_regStrip hS.boundaryData (hS.staged θ hθ),
    fun hθ₀ hθ t₀ => isStagedHistory_regStrip hS.boundaryData (hS.stagedTwoAngle hθ₀ hθ t₀)⟩

end System

end InteractingSLE.Sec7.WordSafe

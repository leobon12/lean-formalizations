import QuantumZipper.Proofs.Zipper.UnscaledResampleBasic
import QuantumZipper.Proofs.Zipper.F1StrictMonoCore
import QuantumZipper.Proofs.Zipper.F1LenInScale
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT
import QuantumZipper.Proofs.Zipper.F1LenInRefl
import QuantumZipper.Proofs.Zipper.F1LenInCanon
import QuantumZipper.Proofs.Zipper.F1LenReg
import QuantumZipper.Proofs.Zipper.WedgeDecompCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D29 resampling nodes, part 2: from the `Γ⁰` picture to the unscaled wedge (κ ∈ (0,4))

Decision D29 (`DECISIONS.md`). The unscaled wedge field is, pathwise on a product extension
(`WedgeUnzip.WDec.wedgeDecompStmt_holds`, proved), `Z = X'' + α₀(−log|·|) + G` with `X''` a free field
independent of the driver and `G` continuous. Since `α₀(−log|·|) = 𝔥₀ − γ log|·|`, the wedge
field is the `Γ⁰` field `𝔥₀ + X''` plus `f = −γ log|·| + G`, which is continuous away from `0` but
**singular at `0`**. Consequently:

* there is no law-level transfer: `X'' + c log|·|` (`c ≠ 0`) is singular with respect to `X''`
  near `0` (its circle-average process at `0` gets the drift `−c t`), so no a.s. statement whose
  truth depends on the field near `0` transfers by absolute continuity;
* the lengths read the field near `0` at *every* time (the interval `[O⁻_t, 0]` ends at the image
  `O⁻_t` of `0⁻`), so finiteness of the wedge lengths is a genuine tip input (TIP-X, D29 layer 4),
  not a consequence of the `Γ⁰` statements.

What *does* transfer is the length measure along the curve: in capacity time, the `Γ⁰` lengths are
`L_t = μ(0,t]` and the wedge lengths are `∫_{(0,t]} w dμ` with `w(s) = e^{γ f(η(s))/2}`, finite
and positive for `s > 0` (Sheffield, arXiv:1012.4797, §1.4 and §5.4 pp. 71–72: quantum length is
the boundary measure transported by the unzipping maps, and adding a continuous function
multiplies the boundary measure by `e^{γ f/2}`, M4-T1 `GoodSample.qBoundaryMeasure_add_ofFun`).
Named inputs (one general principle, three uses):

* `LogShiftLenDensityStmt`: the density representation;
* `LogShiftLenFiniteStmt`: the wedge lengths are finite (tip input);
* `LogShiftLenFlowMeasStmt`: the wedge lengths along the capacity flow come from one measure
  (used for the pair cocycle, which is *not* a transfer: a numerical cocycle for `μ` says nothing
  about the weighted lengths).

**Range of `κ`.** The unscaled statements `LenStrictMonoUnscaledStmt`, `LenRegUnscaledStmt`,
`LenPairCocycleUnscaledStmt` quantify over *all* `κ`, while the `Γ⁰` statements only cover
`0 < κ < 4`; for `κ = 0` (`γ = 0`, `qBoundaryMeasure 0 = volume`, zero driver, `L±_t = 2√t`) the
pair cocycle fails, and for `4 ≤ κ < 8` the boundary measure of the wedge vanishes, so strict
monotonicity fails. The results below are therefore stated for `0 < κ < 4` (the only range used
by the consumers, which get it from `Thm13Asm.IsPStarSample`).

Own bookkeeping; the deterministic measure theory is in `UnscaledResampleBasic.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## The named inputs -/

/-! ## Helpers -/

/-- **The general principle**: the unscaled wedge configuration is, on the product extension of
`WedgeDecompStmt`, a log-shifted field over a `Γ⁰` configuration, so every a.s. statement about
log-shifted fields gives the corresponding statement for the unscaled wedge. -/
theorem ae_unscaled_of_logShift {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (S : FieldSample × (ℝ → ℝ) → Prop)
    (hS : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
      (B : ℝ≥0 → Ω₁ → ℝ) (X : Ω₁ → FieldSample) (G : Ω₁ → ℂ → ℝ) (Z : Ω₁ → FieldSample),
      IsBrownianReal B P₁ → IsFreeGFFModConstH X P₁ → IndepFun (pathOf B) X P₁ →
      (∀ᵐ ω ∂P₁, Continuous (G ω) ∧ ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
        Z ω (foldedCircle d r) = (X ω + F2.logSingField κ + ofFun (G ω)) (foldedCircle d r)) →
      ∀ᵐ ω ∂P₁, S (Z ω, drive κ B ω))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B'' : ℝ≥0 → Ω → ℝ}
    (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hI : IndepFun X' (fun ω t => A t ω) P) (hB : IsBrownianReal B'' P)
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P) :
    ∀ᵐ ω ∂P, S (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) := by
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q)
    (S := fun ω => S (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)) ?_
  have hGZ : ∀ᵐ ω ∂(P.prod Q), Continuous (G ω) ∧ ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      F2.zU (Real.sqrt κ) X' A ω.1 (foldedCircle d r) =
        (X'' ω + F2.logSingField κ + ofFun (G ω)) (foldedCircle d r) :=
    hae.mono fun ω h => ⟨h.1, h.2.2⟩
  filter_upwards [hS (P.prod Q) _ X'' G (fun ω => F2.zU (Real.sqrt κ) X' A ω.1) hB2 hX'' hI2
    hGZ] with ω hω
  exact hω

/-! ## The three D29 nodes on `0 < κ < 4` -/

section Nodes

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B'' : ℝ≥0 → Ω → ℝ}

end Nodes

end F1
end QuantumZipper

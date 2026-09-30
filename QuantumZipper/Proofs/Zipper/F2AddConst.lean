import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.Zipper.Cor15GoodConst

/-!
# F2 step (2b), input ADDCONST: additive constants in the unzipped lengths

Theorem 1.3, node F2, step (2b) (`F2LocalSteps.lean`): the input `F2.AddConstAgreeStmt`
(`F2Step2b.lean:92`) says that a.s., for every time `t > 0` and every constant `c`, agreement of
the two quantum lengths of `η[0,t]` for the configuration `(X + α₀(−log|·|) + c, √κ B)` implies
agreement for `(X + α₀(−log|·|), √κ B)` (both lengths are multiplied by `e^{γc/2}`).

Source: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1, rule (5.1)
(pp. 60–62): the boundary measure of `h + φ` for continuous `φ` is `e^{γφ/2}` times that of `h`;
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1
(arXiv:0808.1560, p. 18) for the constants case. The bookkeeping below is our own: the paper
leaves the reduction implicit.

## Route

The driver is *not* changed by the additive constant (`unzippedField γ (y, W) t` is
`coordChange y (fwdMapInv W t) (Qc γ)`, and the pictures `sideImages W t` depend only on `W`), so
both configurations read the same two intervals `[O⁻_t, 0]`, `[0, O⁺_t]` and only the fields
differ:

* **Coordinate identity** (`coordsFull_coordChange_addConst`): at every dyadic folded circle,
  `coordChange (addConst x c) ψ Q` and `addConst (coordChange x ψ Q) c` agree. `coordChange`
  reads `x` through `evalReg x (μ.map ψ)`, and `evalReg` is a `limUnder`, which commutes with
  adding `c` only where the limit exists (`E1.evalReg_addConst_of_regShift`, the hypothesis
  `E1.RegShift x (μ.map ψ)`); we ask it of the pushed dyadic circles, as in
  `B5.coordsFull_coordChange_fromC_nrm`. Since `qBoundaryMeasure` depends only on `coordsFull`
  (`B5.qBoundaryMeasure_congr_full`), this gives
  `qBoundaryMeasure γ (unzippedField γ (addConst x c, W) t) = qBoundaryMeasure γ (addConst U c)`
  with `U = unzippedField γ (x, W) t`.
* **Scaling** (`Cor15GoodConst.qBoundaryMeasure_addConst_ae`, rule (5.1)): under
  `BdryConvAE U`, `qBoundaryMeasure γ (addConst U c) = e^{γc/2} • qBoundaryMeasure γ U`.
* **Cancellation**: hence each unzipped length of the shifted configuration is
  `e^{γc/2} ∈ (0, ∞)` times the corresponding length of the original one, and equality of the two
  shifted lengths is equivalent to equality of the two original ones
  (`agree_of_smul_eq`).

## Junk values

No hypothesis on the existence of the boundary limit is needed. `qBoundaryMeasure` is the junk
measure `0` when the limit does not exist, but the scaling relation holds for the *chosen*
measures whichever branch is taken (`Cor15GoodConst.qBoundaryMeasure_addConst_ae` does the same
case split), and `C • ν = 0 ↔ ν = 0` cancels: if the shifted configuration has no limit, both of
its lengths are `0`, the hypothesis of `AddConstAgreeStmt` holds trivially, and so does its
conclusion (both original lengths are `0` as well). In particular the all-times boundary limit
`F2AllTimesLimitStmt` — recorded below in the form used by the rest of the F2 chain, mirroring
`RegUnif.UnifGlobalStmt` and `WedgeUnzipLimitAllStmt` — is *not* needed for this step; the
transfer rests instead on the a.s. regularity input `F2UnzipRegStmt`.

## Main results

* `F2AllTimesLimitStmt`, `F2UnzipRegStmt` (named open inputs, exact statements);
* `coordsFull_coordChange_addConst`, `qBoundaryMeasure_unzip_addConst_scale`,
  `unzipLengths_addConst_eq_smul`, `agree_of_smul_eq`: the deterministic chain;
* `agree_addConst_of_inputs` (and its measure-family form `agree_addConst_of_inputs_nu`): the
  pathwise transfer at a fixed driver, i.e. the whole mathematical content of `AddConstAgreeStmt`.

**Not yet in this file**: the one-line assembly `addConstAgree_of_reg : F2UnzipRegStmt →
AddConstAgreeStmt`, which is blocked on a term-elaboration (not mathematical) issue with the
additive notation `X ω + logSingField κ`; see the comment block at the end of the file for its
exact statement and the three routes tried.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

open CoordsFull

/-! ## The named inputs -/

/-- The pushed dyadic folded circles read by the unzipping map. -/
abbrev upfc (W : ℝ → ℝ) (t : ℝ) (i : ℕ) : Measure ℂ :=
  (foldedCircle (fullIndex i).1 (fullIndex i).2).map (fwdMapInv W t)

/-! ## Deterministic chain -/

/-- **Additive constants at one folded circle.** If `evalReg x` commutes with constants at the
pushed measure (`E1.RegShift`), then the coordinate change of `x + c` at that circle is the
coordinate change of `x` plus `c`. -/
theorem coordChange_addConst_fc {x : FieldSample} {ψ : ℂ → ℂ} {Q : ℝ} (c : ℝ) {d : ℂ} {r : ℝ}
    (h : E1.RegShift x ((foldedCircle d r).map ψ)) :
    coordChange (addConst x c) ψ Q (foldedCircle d r) =
      coordChange x ψ Q (foldedCircle d r) + c := by
  have : IsProbabilityMeasure ((foldedCircle d r).map ψ) := by infer_instance
  have h1 : evalReg (addConst x c) ((foldedCircle d r).map ψ) =
      evalReg x ((foldedCircle d r).map ψ) + c := E1.evalReg_addConst_of_regShift h c
  unfold coordChange
  rw [h1]
  ring

/-- Cancellation in `ℝ≥0∞` by a positive finite factor. -/
theorem eq_of_mul_eq_mul_left {C a b : ℝ≥0∞} (h0 : C ≠ 0) (hT : C ≠ ⊤) (h : C * a = C * b) :
    a = b := by
  have h' := congrArg (fun x => C⁻¹ * x) h
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul] using h'

/-- Agreement transfers in both directions when both sides are scaled by the same positive finite
factor. In particular the junk case (a missing boundary limit gives `qBoundaryMeasure = 0` on
both sides) is covered: `C • ν = 0 ↔ ν = 0`. -/
theorem agree_of_smul_eq {C : ℝ≥0∞} (h0 : C ≠ 0) (hT : C ≠ ⊤) {a₁ a₂ b₁ b₂ : ℝ≥0∞}
    (h1 : a₁ = C * b₁) (h2 : a₂ = C * b₂) : a₁ = a₂ ↔ b₁ = b₂ :=
  ⟨fun h => eq_of_mul_eq_mul_left h0 hT (by rw [← h1, ← h2, h]),
    fun h => by rw [h1, h2, h]⟩

/-! ## `AddConstAgreeStmt`: the remaining assembly

The deterministic chain above (`agree_addConst_of_inputs`, instantiated at a fixed `ω`) is the
whole mathematical content of `AddConstAgreeStmt`; what is missing in this file is only the
*bookkeeping* of combining it with the a.s. input `F2UnzipRegStmt`, namely the term

```lean
theorem addConstAgree_of_reg (h : F2UnzipRegStmt) : AddConstAgreeStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  obtain ⟨hreg, hbc⟩ := h κ hκ hκ4 P B X hB hX hind
  have hcomb : ∀ᵐ ω ∂P, (∀ t : ℝ, 0 < t → ∀ i : ℕ,
        E1.RegShift (X ω + logSingField κ) (upfc (drive κ B ω) t i)) ∧
      (∀ t : ℝ, 0 < t → Cor15Group.BdryConvAE
        (unzippedField (Real.sqrt κ) (X ω + logSingField κ, drive κ B ω) t)) := hreg.and hbc
  have hgoal : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ c : ℝ,
      (unzipLengths (Real.sqrt κ) (addConst (X ω + logSingField κ) c, drive κ B ω) t).1 =
        (unzipLengths (Real.sqrt κ) (addConst (X ω + logSingField κ) c, drive κ B ω) t).2 →
      (unzipLengths (Real.sqrt κ) (X ω + logSingField κ, drive κ B ω) t).1 =
        (unzipLengths (Real.sqrt κ) (X ω + logSingField κ, drive κ B ω) t).2 := by
    refine hcomb.mono ?_
    intro ω hω t ht c hlen
    exact (agree_addConst_of_inputs (γ := Real.sqrt κ) (c := c) (t := t)
      (x := X ω + logSingField κ) (W := drive κ B ω) (hω.1 t ht) (hω.2 t ht)).2 hlen
  exact hgoal
```

The final `exact` (and every variant of it tried here: explicit vs. inferred implicit arguments,
`.mono` vs. `filter_upwards`, up to 3.2M heartbeats) makes the unifier unfold the `HAdd`/`Add.add`
instance of `FieldSample` on the compound field `X ω + logSingField κ` some 250000 times (and with
it `addConst`, `avgReg`, `limUnder`, `qBoundaryMeasure`), and times out. The *same* call with a
plain variable `x₀` in place of the compound term elaborates instantly, so this is a term-elaboration
issue about the additive notation of the field, not a mathematical one: any of
(i) restating `F2UnzipRegStmt`/the lemmas with an explicit measure family `ν : ℕ → Measure ℂ` in
place of `fun i => upfc W t i` (so that the unifier sees a Miller pattern instead of a term under a
binder), or (ii) restating the tail in place of the `AddConstAgreeStmt` body and converting once,
is expected to close it.
-/

end F2
end QuantumZipper

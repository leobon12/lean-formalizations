import QuantumZipper.Proofs.Zipper.UnifRCConv
import QuantumZipper.Proofs.Zipper.F2Step3DensSplit
import QuantumZipper.Proofs.Zipper.JointModFinal

/-!
# UNIF-RC: the regularization split of F2 step (3) at all times (dyadic circles)

`step3EvalSplitDy_holds`: almost surely, **for all `t ≥ 0`** and every dyadic folded circle
`fc(lpt n a b, 2^{-k})`, with `ν = (f_t⁻¹)_* fc`,

`evalReg ((X + α₀(−log|·|)) + γ log|·|) ν = evalReg (X + α₀(−log|·|)) ν + ∫ γ log|·| dν`.

Both sides are `evalReg (a log|·| + X) ν` for two coefficients `a`, which equals
`a ∫ log|·| dν + lim_j ∫ avgReg X j dν` once the last limit exists
(`RegUnif.evalReg_logMul_add_of_tendsto`); the limit exists at all times at once by
`RegUnif.ae_forall_tendsto_dyadic` (REG-CONT Kolmogorov step in `(t, ρ)`).

Consequences: the dyadic form of `Step3FieldCircStmt` (`step3FieldCircDy_holds`) and
`step3LocalDensity_of_unif`, which removes both the circle-level field identity and the
`JointModStmt` input of `step3LocalDensity_of_remaining`. Only dyadic circles are needed, because
`avgReg` only reads raw values at dyadic centres `dyadicRoundC n s = lpt n _ _` and dyadic radii
(`forall_avgReg_eq_of_lpt`). The all-circle statement `Step3EvalSplitStmt` (arbitrary centres
and radii) is **not** proved here and is not needed.

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (via `RegCont`); the rest is
own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

open RegCont

/-- `x + α₀(−log|·|)` as a log field plus `x`. -/
theorem add_logSingField_eq (κ : ℝ) (x : FieldSample) :
    x + logSingField κ =
      ofFun (fun v => -(Real.sqrt κ - 2 / Real.sqrt κ) * Real.log ‖v‖) + x := by
  rw [add_comm]
  congr 1
  unfold logSingField
  congr 1
  funext v
  ring

/-- **The split at `ν_t`**, given convergence of the regularized values of `x` (deterministic). -/
theorem evalSplit_of_tendsto {κ : ℝ} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (w : ℂ) {r : ℝ} (hr : 0 < r) {x : FieldSample} (hx : RegAvgGood x) {L : ℝ}
    (hL : Tendsto (fun k => ∫ z, avgReg x k z ∂νT W w r t) atTop (𝓝 L)) :
    evalReg ((x + logSingField κ) + gammaLog κ) (νT W w r t) =
      evalReg (x + logSingField κ) (νT W w r t) +
        ∫ z, Real.sqrt κ * Real.log ‖z‖ ∂νT W w r t := by
  rw [← h0rev_add_eq, add_logSingField_eq,
    show ofFun (h0rev κ) = ofFun (fun v => 2 / Real.sqrt κ * Real.log ‖v‖) from rfl,
    RegUnif.evalReg_logMul_add_of_tendsto hW hW0 ht w hr _ hx hL,
    RegUnif.evalReg_logMul_add_of_tendsto hW hW0 ht w hr _ hx hL, integral_const_mul]
  ring

/-- **Regularization split, dyadic circles, all times.** -/
def Step3EvalSplitDyStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ (n : ℕ) (a b : ℤ) (k : ℕ),
      evalReg ((X ω + logSingField κ) + gammaLog κ)
          ((foldedCircle (CircleCont.lpt n a b) (radius k)).map (fwdMapInv (drive κ B ω) t)) =
        evalReg (X ω + logSingField κ)
            ((foldedCircle (CircleCont.lpt n a b) (radius k)).map (fwdMapInv (drive κ B ω) t)) +
          ∫ z, Real.sqrt κ * Real.log ‖z‖
            ∂(foldedCircle (CircleCont.lpt n a b) (radius k)).map (fwdMapInv (drive κ B ω) t)

/-- **`Step3EvalSplitDyStmt` holds.** -/
theorem step3EvalSplitDy_holds : Step3EvalSplitDyStmt := by
  intro κ _ _ Ω _ P _ B X hB hX hind
  have hreg : ∀ᵐ ω ∂P, RegAvgGood (X ω) :=
    ae_all_iff.2 fun k => FrostmanReg.ae_circleAvg_tendsto_frostman hX k
  filter_upwards [RegUnif.ae_forall_tendsto_dyadic κ hB hX hind, hreg, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hω hr hc h0 t ht n a b k
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  obtain ⟨L, hL⟩ := hω t ht n a b k
  exact evalSplit_of_tendsto hWc hW0 ht _ (radius_pos k) hr hL

/-- **Circle-level field identity, dyadic circles, all times.** -/
def Step3FieldCircDyStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ (n : ℕ) (a b : ℤ) (k : ℕ),
      unzX κ (X ω) (drive κ B ω) t (foldedCircle (CircleCont.lpt n a b) (radius k)) =
        unzY κ (X ω) (drive κ B ω) t (foldedCircle (CircleCont.lpt n a b) (radius k)) +
          ∫ z, -(Real.sqrt κ * Real.log ‖extInv (drive κ B ω) t z‖)
            ∂foldedCircle (CircleCont.lpt n a b) (radius k)

theorem step3FieldCircDy_holds : Step3FieldCircDyStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [step3EvalSplitDy_holds κ hκ hκ4 P B X hB hX hind, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hω hc h0 t ht n a b k
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  exact unzX_fc_eq_of_split hWc hW0 ht (radius_pos k) (hω t ht n a b k)

/-- Equal raw values on all dyadic folded circles give equal `avgReg` everywhere. -/
theorem forall_avgReg_eq_of_lpt {x y : FieldSample}
    (h : ∀ (n : ℕ) (a b : ℤ) (k : ℕ), x (foldedCircle (CircleCont.lpt n a b) (radius k)) =
      y (foldedCircle (CircleCont.lpt n a b) (radius k))) (k : ℕ) (z : ℂ) :
    avgReg x k z = avgReg y k z := by
  unfold avgReg
  congr 1
  funext n
  rw [CircleCont.dyadicRoundC_eq_lpt]
  exact h _ _ _ _

end F2
end QuantumZipper

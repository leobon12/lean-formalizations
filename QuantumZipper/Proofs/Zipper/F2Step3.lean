import QuantumZipper.Proofs.Zipper.F2LocalSteps

/-!
# F2 step (3): from the log singularity `α₀(−log|·|)` to the `Γ⁰` field `h⁰`

Theorem 1.3, node F2, step (3) (`Step3Stmt := LogSingLocLenAgree → GammaZeroLocLenAgree`,
`F2LocalSteps.lean`; blueprint `SECTION5_BLUEPRINT.md`, F2 route R7). Source for the two
ingredients: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1
(pp. 60–62: rule (5.1), adding a function `φ` continuous near the boundary multiplies the boundary
measure by `e^{γφ/2}`; Duplantier–Sheffield 2011, (5.1)) and §5.4 (pp. 70–72). The paper itself
derives Theorem 1.3 from Theorem 1.8 by absolute continuity (p. 72); the chain through the
deterministic `γ log|·|` is the blueprint's route R7 (own route, recorded in `DEVIATIONS.md`).

## Argument (own bookkeeping around two exactly stated inputs)

With `γ = √κ`, `α₀ = γ − 2/γ`, `x = X + α₀(−log|·|)` and `y = h⁰ + X = (2/γ) log|·| + X`:

1. **Exact field identity** (`h0rev_add_eq`, proved): `y = x + ofFun (γ log‖·‖)` as field
   samples, since `−α₀ + γ = 2/γ` and `∫ c·f dμ = c ∫ f dμ` holds for every `μ` (also when `f`
   is not integrable, where all three pairings are the junk value `0`).
2. **Rule (5.1) at the unzipped level** (input `Step3DensityStmt`). Unzipping by `t`, the
   function `γ log|·|` becomes `γ log|F_t|` with `F_t` the boundary extension of `f_t⁻¹`
   (`invBdry`), which is continuous and finite on `[O⁻_t, O⁺_t]` except at the endpoints `O^±_t`
   (which `F_t` sends to `0`, where the density `|F_t|^{γ²/2}` vanishes continuously) and there is
   no atom at the endpoints. So the two lengths of `(y, W)` at time `t` are
   `∫_{[O⁻_t,0]} |F_t|^{γ²/2} dν_{x_t}` and `∫_{[0,O⁺_t]} |F_t|^{γ²/2} dν_{x_t}`.
3. **Welding invariance** (input `Step3WeldStmt`). If the lengths of `(x, W)` agree at every time
   `s ≤ t`, the conformal welding identifying the two sides of `η[0,t]` preserves `ν_{x_t}`:
   `∫_{[O⁻_t,0]} g∘F_t dν_{x_t} = ∫_{[0,O⁺_t]} g∘F_t dν_{x_t}` for every measurable `g ≥ 0` on `ℂ`
   (welded points have the same image under `F_t`: "the density is the same on both sides").
4. Taking `g = |·|^{γ²/2}` in 3 and combining with 2 gives `L⁻_t(y) = L⁺_t(y)`
   (`step3_of_inputs`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- The boundary extension of the inverse centered forward map `f_t⁻¹` at a real point `w`:
the limit of `fwdMapInv W t u` as `u → w` inside `ℍ` (junk value if the limit does not exist).
For a simple `SLE_κ` curve (`κ < 4`) this is the Carathéodory extension, sending `[O⁻_t, O⁺_t]`
onto the two sides of `η[0,t]`, `O^±_t ↦ 0` and `0 ↦ η(t)`. -/
def invBdry (W : ℝ → ℝ) (t : ℝ) (w : ℝ) : ℂ :=
  limUnder (𝓝[H] (w : ℂ)) (fwdMapInv W t)

/-- The boundary density `|F_t(w)|^{γ²/2}` produced by adding `γ log|·|` (rule (5.1)). -/
def logDens (γ : ℝ) (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (‖z‖ ^ (γ ^ 2 / 2))

theorem measurable_logDens (γ : ℝ) : Measurable (logDens γ) :=
  ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)

/-- The deterministic function `γ log|·|` added in step (3). -/
def gammaLog (κ : ℝ) : FieldSample := ofFun fun z => Real.sqrt κ * Real.log ‖z‖

/-- **Exact field identity** (step (3), item 1): `h⁰ + X = (X + α₀(−log|·|)) + γ log|·|`. -/
theorem h0rev_add_eq (κ : ℝ) (x : FieldSample) :
    ofFun (h0rev κ) + x = (x + logSingField κ) + gammaLog κ := by
  funext μ
  simp only [Pi.add_apply, ofFun, logSingField, gammaLog, h0rev]
  have h1 : (∫ z, (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖ ∂μ) =
      -(Real.sqrt κ - 2 / Real.sqrt κ) * ∫ z, Real.log ‖z‖ ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  rw [h1, integral_const_mul, integral_const_mul]
  ring

/-! ## The density input from the local rule on the open interval `(O⁻_t, O⁺_t)` -/

end F2
end QuantumZipper

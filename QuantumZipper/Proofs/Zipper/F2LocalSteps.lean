import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.B2Driver
import QuantumZipper.Proofs.Zipper.ESMLMeas

/-!
# F2 steps (2b)–(4), part 2: the chain wedge → log singularity → `Γ⁰` → all times

Theorem 1.3, node F2 (`blueprint/SECTION5_BLUEPRINT.md`, F2 steps (2)–(4), route R7), input
`F2LocalStmt := UnscaledLenAgree → GammaZeroLenAgree` (`F2Reduce.lean`). Source: Sheffield,
*Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4 (proof of Theorem 1.3,
pp. 70–72), with §5.1 (pp. 60–62: rule (5.1), the boundary measure of `h + φ` for continuous `φ`
is `e^{γφ/2}` times that of `h`) and §1.6 (the wedge inside `B₁` is a free field plus
`α(−log|·|)`).

With `γ = √κ` and `α₀ = γ − 2/γ` the paper's chain is:

* **(2b)** [`Step2bStmt`] lengths agree for the unscaled wedge field with an independent driver
  (`UnscaledLenAgree`) ⇒ lengths agree, for small times, for `X + α₀(−log|·|)` with an independent
  driver (`LogSingLocLenAgree`). Ingredients: B5 locality (for `t ≤ t₀` and `|W| ≤ M` on `[0,t]`
  the lengths read only the field on the dyadic circles in a ball of radius `< 1`;
  `B5.unzipLengths_eq_of_dyCircAgree_uniform`, with the side-image bound `B5.SideSmallStmt`), the
  restriction identity B4(b) (inside `B₁` the wedge field is `X − h₁(0) + α₀(−log|·|)` in law,
  `WedgeRes`), and the additive constant `h₁(0)` (both lengths are multiplied by `e^{γ h₁(0)/2}`).
* **(3)** [`Step3Stmt`] adding the deterministic `γ log|·|` turns `X + α₀(−log|·|)` into
  `h⁰ = (2/γ) log|·| + X` (`h0rev`), since `−α₀ + γ = 2/γ`; by rule (5.1) (B3(b)) both lengths
  of every sub-arc `η[r,s]` are integrals of the same density `|η|^{γ²/2}` (welded points have the
  same image), and `0` carries no atom, so agreement persists (`GammaZeroLocLenAgree`).
* **(4)** [`Step4Stmt`] scale invariance of `Γ⁰` (B3(d): `(h⁰ + X)(a·) + Q log a` is again
  `h⁰ + X` up to an additive constant, `W(a²·)/a` is again `√κ` times a Brownian motion, lengths
  scale by `e^{γc/2}` on both sides) removes the smallness condition: `GammaZeroFwdLenAgree`.
* **Time reversal**, proved in `F2LocalRev.lean` (`gammaZero_of_fwd`).

`f2Local_of_steps` chains these; each step is stated as an explicit implication between two
exactly stated probabilistic statements. The decomposition is the paper's; the chaining is our
own bookkeeping.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- Lengths agree at every small time: `L⁻_t = L⁺_t` for `(x, W)` at every `t ∈ [0, t₀]` such
that `|W| ≤ M` on `[0,t]` (the hull `η[0,t]` then lies in a small ball around `0`). -/
def SmallTimeAgree (γ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (t₀ M : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → (∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) →
    (unzipLengths γ (x, W) t).1 = (unzipLengths γ (x, W) t).2

/-- The deterministic log singularity `α₀(−log|·|)`, `α₀ = γ − 2/γ`, `γ = √κ`. -/
def logSingField (κ : ℝ) : FieldSample :=
  ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖

/-- `SmallTimeAgree` is monotone in the thresholds. -/
theorem SmallTimeAgree.mono {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ} {t₀ M t₁ M₁ : ℝ}
    (h : SmallTimeAgree γ x W t₀ M) (ht : t₁ ≤ t₀) (hM : M₁ ≤ M) :
    SmallTimeAgree γ x W t₁ M₁ := fun t h0 h1 h2 =>
  h t h0 (h1.trans ht) fun r hr => (h2 r hr).trans hM

end F2
end QuantumZipper

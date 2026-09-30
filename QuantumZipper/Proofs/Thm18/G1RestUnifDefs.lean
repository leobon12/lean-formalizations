import QuantumZipper.Proofs.Thm18.G1ProfileConv
import QuantumZipper.Proofs.LQG.GoodMeasurableReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST-UNIF: the two deterministic inputs of the uniform Cauchy property

`G1RestUnifStmt` (G1RestRC3Wire.lean) asks that, a.s., the smoothings
`k ↦ ∫ avgReg y k (ψ z) dfc(q)(z)` of the canonical wedge representative `y = rescale w₀ Q S`
along the selected map `ψ` be uniformly Cauchy at the dyadic points of each box. For a good
sample (`WedgeGood x F A`, `S > 0`) the integrand splits into a free-field part, a profile part
and a constant:

  `avgReg y k (ψ z) = F(S ψ z, S 2^{-k}) + smoothFun (rp g) (S ψ z) (S 2^{-k}) + Q log S`

for `fc(q)`-a.e. `z` (`G1RC.AvgRegPsiStmt`; `g = wg x A Q`, the wedge profile). The free part
converges uniformly on compact parameter sets by the joint continuity, down to smoothing radius
`0`, of the Kolmogorov–Čentsov modification (Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1; `G1RestUnifFree.lean`); the profile part converges uniformly on the compact boxes
`GoodMeas.kbox m` (`G1RC.UnifProfStmt`, a uniform version of `G1RC.tendsto_profile_psi`).

This file only states the two deterministic inputs.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open F1.RC3Two

/-- **Uniform convergence of the profile part** on the compact boxes: for `ψ` as in
`PsiGood`, `S > 0` and a radial profile `g` continuous on `(0,∞)` with `|g t| ≤ C (1 - log t)`
on `(0, 1]`, the circle-smoothed profile integrated along `ψ_* fc(q)` converges, uniformly in
`q ∈ kbox m`, to the unsmoothed one (pointwise: `tendsto_profile_psi`). -/
def UnifProfStmt : Prop :=
  ∀ (ψ : ℂ → ℂ), PsiGood ψ → ∀ (S : ℝ), 0 < S → ∀ (g : ℝ → ℝ) (C : ℝ), Measurable g →
    ContinuousOn g (Ioi 0) → (∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) →
    ∀ m : ℕ, TendstoUniformlyOn
      (fun (k : ℕ) (q : ℂ × ℝ) => ∫ z, GoodSample.smoothFun (rp g) ((S : ℂ) * ψ z)
        (S * radius k) ∂foldedCircle q.1 q.2)
      (fun q => ∫ z, rp g ((S : ℂ) * ψ z) ∂foldedCircle q.1 q.2) atTop (GoodMeas.kbox m)

/-- **Regularized circle averages of the rescaled wedge field along `ψ`.** For a good sample,
`S > 0` and `ψ` as in `PsiGood`, on every folded circle of positive radius, for `fc`-a.e. `z`
the regularized average `avgReg y k (ψ z)` of `y = rescale (wedgeField (lateralPart x) A Q) Q S`
is the free part plus the smoothed profile plus `Q log S` (`avgReg_rescale_wedge` off the
circle `‖w‖ = 2^{-k}`; on that circle the value still agrees except at the dyadic points of
the circle, which `ψ_* fc` does not charge). -/
def AvgRegPsiStmt : Prop :=
  ∀ (x : FieldSample) (F : ℂ × ℝ → ℝ) (A : ℝ → ℝ), WedgeGood x F A → ∀ (Q C : ℝ),
    (∀ t, 0 < t → t ≤ 1 → |wg x A Q t| ≤ C * (1 - Real.log t)) →
    ∀ (S : ℝ), 0 < S → ∀ (ψ : ℂ → ℂ), PsiGood ψ → ∀ (d : ℂ) (r : ℝ), 0 < r → ∀ k : ℕ,
      ∀ᵐ z ∂foldedCircle d r,
        avgReg (rescale (wedgeField (lateralPart x) A Q) Q S) k (ψ z) =
          F ((S : ℂ) * ψ z, S * radius k) +
            GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * ψ z) (S * radius k) +
            Q * Real.log S

end G1RC
end Thm18Asm
end QuantumZipper

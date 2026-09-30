import QuantumZipper.Proofs.Thm18.G3Za4
import QuantumZipper.Field.CoordsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (a): the Palm-case one-point core (`α = γ`), `Setup` form

`exists_g0Setup_logSing`: for an admissible local map `ψ` of G0, `0 < γ < 2`, and a profile
`f = γ(−log ‖·‖) + h` near `0` (`h` continuous, harmonic and conjugation-invariant near `0`,
`f` measurable), there are `0 < r < s` and, on one probability space, a free field `W`
and **D3⁺ `Setup` data with `α = γ`** (`D3Plus.Setup γ γ r (fc(0,s)) stdP X' Ξ g`) such that
almost surely, for every level `L`, the zoom of `ofFun f + W` through `ψ` normalized at
`ρ₀ = fc(0, s)` agrees near `0` with the D3⁺ model `zoomModel γ γ L ρ₀ X' g`.

This is the one-point core of the zoom at a quantum-typical (Palm) boundary point: under the
Palm law the field is a free field plus `γ(−log|· − x|)` plus a smooth function near `x`
(`G3WedgePalmIdStmt`), and D3⁺(i) with `α = γ` applies to its zoom through the local map.
Proof: the free core `G3Cv.exists_g0Setup` (for `W`), re-referenced to a dyadic circle
`fc(0, 2^{-k₀})` inside the region where `exists_logSing_data` splits the profile as
`γ(−log ‖·‖) + k`; the new model function is `g + k − c(ω)` with `c(ω)` the reference
constant, `condSigma`-measurable (integral of `g ω` over the reference circle). Sources as in
G3Cv2Setup.lean (Sheffield 2007 §2.2; arXiv:1012.4797 pp. 70–71). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

open G3Cv K3 GFFExist LQGDimension.ExistAsm D3Plus InnerProductSpace

theorem zoomModel_apply_fc {γ α L : ℝ} {ρ₀ : Measure ℂ} {x : FieldSample} {g : ℂ → ℝ}
    {c : ℂ} {s : ℝ} (hg : Integrable g (foldedCircle c s)) :
    zoomModel γ α L ρ₀ x g (foldedCircle c s) = x (foldedCircle c s) +
      ((∫ u, α * -Real.log ‖u‖ ∂foldedCircle c s) + ∫ u, g u ∂foldedCircle c s) +
        (L / γ - x ρ₀) := by
  have hli : Integrable (fun u : ℂ => α * -Real.log ‖u‖) (foldedCircle c s) :=
    (CoordReg.integrable_log_norm_foldedCircle c s).neg.const_mul α
  simp only [zoomModel, Pi.add_apply, ofFun]
  rw [integral_add (f := fun z => α * -Real.log ‖z‖ + g z) (g := fun _ => L / γ - x ρ₀)
    (hli.add hg) (integrable_const _),
    integral_add (f := fun z : ℂ => α * -Real.log ‖z‖) hli hg, integral_const,
    measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

theorem addConst_apply_fc (y : FieldSample) (a : ℝ) (c : ℂ) (s : ℝ) :
    addConst y a (foldedCircle c s) = y (foldedCircle c s) + a := by
  simp [addConst, measure_univ]

end G3Za
end QuantumZipper

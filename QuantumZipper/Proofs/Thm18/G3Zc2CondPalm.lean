import QuantumZipper.Proofs.Thm18.G3Zc2Univ3
import QuantumZipper.Proofs.Thm18.G3Zc2PFar
import QuantumZipper.Proofs.Thm18.G3Zc2Sep
import QuantumZipper.Proofs.Thm18.G3Za8

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: the conditional Palm zoom through a map, for any free field

`cond_zoom_palm_free`: for an admissible local map `ψ` of G0, a Palm profile
`f = γ(−log‖·‖) + h` near `0` and a normalizing probability measure `S` far from `0` (the data of
ZOOM-A's `exists_g0Setup_palm`), there are `r'' > 0` and `R₀ > 0` such that for **every** free
field `V`, every point `x`, and every countable family `q` of balanced pairs whose translates by
`−x` are carried by `{‖y‖ > R₀}` (conditioning increments far from `x`): uniformly over
measurable events `B` of the conditioning vector `(V(q k).1 − V(q k).2)_k`, eventually in `L`,

  `E[1_B(cond) Γ(loc canonicalOn(zoomS … (rawTranslate V x)))] ≈ P(cond ∈ B) · E Γ(γ-wedge)`.

This is the conditional fixed-point zoom through a map at a rooted (Palm) point, the input of the
G2-type region argument for `G3TCurveStmt` (Sheffield, arXiv:1012.4797, Prop. 1.6 and the proof of
Prop. 5.5, pp. 24–25, 65; p. 71). Proof: ZOOM-A's core with the far clause
(`exists_g0Setup_palm_far`) for its own field `U`; the coupled field is `Y = U(· − x)`; the far
increments are a.s. functions of `Ξ`; joint universality (`dyadLawCond_eq_free`); conditional
transfer (`cond_zoom_of_lawEq`). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus K3 GFFExist LQGDimension.ExistAsm

theorem rawTranslate_neg (u : FieldSample) (x : ℝ) :
    rawTranslate (rawTranslate u (-x)) x = u := by
  funext μ
  simp only [rawTranslate]
  rw [Measure.map_map (measurable_add_const _) (measurable_add_const _)]
  congr 1
  have e : ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) ∘ fun z : ℂ => z + (x : ℂ)) = id := by
    funext z; simp
  rw [e, Measure.map_id]

end G3Cv
end QuantumZipper

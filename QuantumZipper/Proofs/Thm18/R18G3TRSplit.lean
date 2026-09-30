import QuantumZipper.Proofs.Thm18.R18G3TSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, T5-R: the per-region transfer through a Cameron–Martin shift (D85)

`G3TProfMixTransferStmt` (R18G3TSplit) asks the fixed-region mixing body of scheme `C` (field
`normField + g`, `g = −γ log|·|`, singular at the root `0`) from that of the free scheme `A`.
It goes through scheme `B`, the free scheme of the field shifted by the cut-off profile
`g3wCut γ η = χ_η · g`. The cut-off `χ_η` is radial and smooth, vanishes on `‖z‖ ≤ η/4` and on
`‖z‖ ≥ 1`, and equals `1` on `η/2 ≤ ‖z‖ ≤ 7/8`. That annulus contains both half-discs of the
index `(δ, η, ·)`: region 1 lies in `‖z‖ > 3η/4` and region 2 in `‖z‖ < 1/2 + η/4`.

* **(R-a)** `G3TCMStmt` (open), `A → B`. `g3wCut γ η` is smooth, compactly supported, even
  across `ℝ`, and harmonic off the two cut-off annuli, which lie outside both half-discs. So
  the Cameron–Martin density of the shift is `exp(X(φ) − ½ Var)` with `φ = −Δ(g3wCut)/2π`
  supported outside both half-discs (`CMTV.cmPos`/`cmNeg`, `CameronMartin.integral_mul_tiltDensity`),
  hence measurable for the outside σ-algebra. The body of `A` is uniform over outside events,
  so it passes to `B` by reweighting with the truncated density. Sources: Sheffield,
  arXiv:1012.4797, p. 72 and Remark 5.7; Berestycki–Powell, arXiv:2004.04720, Lemma 3.12.
* **(R-bc)** `G3TCutToProfStmt` (open), `B → C`. The two fields agree on both half-discs, so
  the region zooms and the region Palm lengths coincide. On the `x`-side, substituting the
  region Palm length `ℓ − (gap length)`, which is outside-measurable, turns the body of `B` into
  that of `C`. On the `R(x)`-side the Palm constraint also involves region 1's boundary mass. That
  needs the positivity `P(ν₁ ≥ u | outside) > 0` (unbounded support of the region-1 boundary
  mass, again by a Gaussian tilt). Locality of the full-field zooms uses the area inputs.

`g3TProfMixTransferStmt_of : G3TCMStmt → G3TCutToProfStmt → G3TProfMixTransferStmt` is
composition.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The cut-off wedge profile `χ_η · (−γ log|·|)`: `χ_η` is radial and smooth, `0` on
`‖z‖ ≤ η/4` and on `‖z‖ ≥ 1`, and `1` on `η/2 ≤ ‖z‖ ≤ 7/8`. -/
def g3wCut (γ η : ℝ) : ℂ → ℝ := fun z =>
  Real.smoothTransition ((‖z‖ - η / 4) / (η / 4)) * Real.smoothTransition ((1 - ‖z‖) * 8) *
    g3wProf γ z

/-- The fixed-region mixing body of the free scheme `A`. -/
abbrev G3BodyA (γ : ℝ) (μ ν : Measure LawD) : Prop :=
  G3FixMixBody μ ν (g3PalmLaw γ) (g3X γ) (g3R γ) (g3Uf γ) (g3Vf γ)

/-- The fixed-region mixing body of scheme `B` (profile `g3wCut γ η` at the index `(δ, η, C)`). -/
abbrev G3BodyB (γ : ℝ) (μ ν : Measure LawD) : Prop :=
  G3FixMixBody μ ν (fun i => g3pPalmLaw γ (g3wCut γ i.η) i) (fun i => g3pX γ (g3wCut γ i.η) i)
    (fun i => g3pR γ (g3wCut γ i.η) i) (fun i => g3pUf γ (g3wCut γ i.η) i)
    (fun i => g3pVf γ (g3wCut γ i.η) i)

/-- The fixed-region mixing body of scheme `C` (profile `g3wProf γ`). -/
abbrev G3BodyC (γ : ℝ) (μ ν : Measure LawD) : Prop :=
  G3FixMixBody μ ν (g3pPalmLaw γ (g3wProf γ)) (g3pX γ (g3wProf γ)) (g3pR γ (g3wProf γ))
    (g3pUf γ (g3wProf γ)) (g3pVf γ (g3wProf γ))

end R18
end QuantumZipper

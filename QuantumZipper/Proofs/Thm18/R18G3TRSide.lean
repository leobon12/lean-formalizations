import QuantumZipper.Proofs.Thm18.R18G3TRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the analytic input of the `R(x)`-side of `B → C`

Route (decided 2026-09-29, helper G3-5T-A). On the `R(x)`-side the Palm constraint
`ℓ ≤ ν[−δ, 0] = ν₁[−δ, ·] + gapL` couples region 1 to the zoom at `R(x)`. After the change of
variables `u = ℓ − gapR` (outside-measurable, as on the `x`-side), and given the field outside
both half-discs and `u`, region 2 is conditionally independent of region 1 (`condIndepCE_g3p`,
Sheffield p. 71), so the `(outside, u)`-marginals of the Palm laws of `B` and `C` have densities
`∝ 1{u > −gapR} F(u − d)` with `F(v) = P(ν₁[−δ, ·] ≥ v | outside)` and `d = gapL − gapR`
(outside-measurable, different for `B` and `C`). The only analytic input of the transfer is that
the `C`-marginal is absolutely continuous w.r.t. the `B`-marginal, i.e. `F > 0` a.s.: the
node below. The rest (Radon–Nikodym ratio, truncation independent of the zoom level, as in
`R18G3TCM5`–`R18G3TCM7`) is bookkeeping.

`F > 0` is the positivity of the conditional tail of the region-1 boundary mass: given the
outside field, adding a Cameron–Martin bump in region 1 (Berestycki–Powell arXiv:2004.04720,
Lemma 3.12) multiplies `ν₁` on a sub-interval by an arbitrarily large factor with an equivalent
law (Sheffield p. 72, Remark 5.7).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Unbounded conditional support of the region-1 boundary mass** (node of (R-c)): for every
level `v`, almost surely the conditional probability, given the free field outside both
half-discs, that the region-1 boundary mass of `[−δ, 0]` exceeds `v` is positive. (Regions 1
of schemes `B` and `C` coincide, `g3pν₁_cut_eq`, so the profile is `g3wProf γ`.) -/
def G3TRegion1TailStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ i : G3Idx, ∀ v : ℝ,
    ∀ᵐ ω ∂gffBase.P, 0 < (gffBase.P[{ω' : gffBase.Ω | ENNReal.ofReal v ≤
      g3pν₁ γ (g3wProf γ) i ω' (Icc (-i.δ) 0)}.indicator (fun _ => (1 : ℝ)) |
        outsideSigma2 gffBase.X i.t₁ i.r₁ i.t₂ i.r₂]) ω

end R18
end QuantumZipper

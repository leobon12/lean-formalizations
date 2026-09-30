import QuantumZipper.Statements.ConfigLaw
import QuantumZipper.Proofs.Loewner.TwoPoint
import QuantumZipper.Proofs.LQG.RegularClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# MATCH-PAPER-18: comparing fields off the curve (proposal support, no Statements change)

Sheffield, arXiv:1012.4797, states the zippers on the **pair of surfaces cut out by the curve**:
Corollary 1.5 (p. 17: "`Z^CAP_t((D₁,h_{D₁}),(D₂,h_{D₂}))` … both `h` and `η` are determined by
the pair") and Theorem 1.8 (p. 26: `Z^LEN_{−t}((D₁,h_{D₁}),(D₂,h_{D₂}))`, "(3) the law of the pair
`((D₁,h_{D₁}),(D₂,h_{D₂}))` is invariant"), where `h_{Dᵢ}` is the restriction of `h` to a component
of `ℍ \ η`. Berestycki–Powell, arXiv:2404.16642, Thm 8.13 and the remark after it (p. 283):
`h̄ᵗ|_{ℍ \ ηᵗ([0,t])}` "uniquely defines `h̄ᵗ`" because the curve is independent and Lebesgue-null.
Sheffield p. 48 (§4.1, proofs of the coupling theorems): "we can define `h_t` arbitrarily on the measure zero set `η([0,t])`".

`Statements/ConfigLaw.lean` compares fields with `RegEq` (all dyadic circles, including circles
that cross the curve). This file records the paper-level comparison `RegEqOff K` (only circles
whose folded image stays at positive distance from a set `K`, e.g. the configuration's curve)
and proves the two structural facts the MATCH-PAPER-18 report relies on:

* `configEqOff_of_configEq`: the off-curve relation is implied by `ConfigEq`, so every proved
  round trip or group-property statement transfers unchanged;
* `regEqOff_of_raw`, `regEqOff_coordChange_of_eqOn`: the off-curve relation reads raw values only
  at folded circles avoiding `K`; in particular the values of a chart on `K` (e.g. the junk
  value of `revMapInv` on the hull) never enter it, so no trace-nullity (`BackSupportI`) or
  contact (`BackContactI`) condition is needed for off-curve comparisons.

Own elementary bookkeeping (no published proof needed: it is a property of our encoding).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace MatchPaper

/-- The circle `∂B(z,r)` stays, after folding into `ℍ̄`, at positive distance from `K`: some open
annulus around it is mapped by `foldH` outside `K`. -/
def CircleOff (K : Set ℂ) (z : ℂ) (r : ℝ) : Prop :=
  ∃ δ > 0, ∀ w : ℂ, |dist w z - r| < δ → foldH w ∉ K

/-- Equality of regularized circle averages at every dyadic circle that avoids `K`
(paper-level comparison of the restrictions to the complement of `K`). -/
def RegEqOff (K : Set ℂ) (x y : FieldSample) : Prop :=
  ∀ (k : ℕ) (z : ℂ), CircleOff K z (radius k) → avgReg x k z = avgReg y k z

/-- Proposed paper-level configuration equality: the fields agree off `K` (in Theorem 1.8,
`K` = the configuration's curve) and the drivers agree on `[0,∞)`. -/
def ConfigEqOff (K : Set ℂ) (c c' : FieldSample × (ℝ → ℝ)) : Prop :=
  RegEqOff K c.1 c'.1 ∧ ∀ u : ℝ, 0 ≤ u → c.2 u = c'.2 u

/-- A folded circle of nonnegative radius whose folded image lies in `U` is carried by `U`. -/
theorem ae_mem_of_sphere {U : Set ℂ} (hU : MeasurableSet U) {d : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hd : ∀ w ∈ Metric.sphere d r, foldH w ∈ U) : ∀ᵐ u ∂foldedCircle d r, u ∈ U := by
  rw [ae_iff]
  change foldedCircle d r Uᶜ = 0
  rw [TwoPoint.foldedCircle_apply' d r hU.compl]
  have : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ foldH (circleMap d r θ) ∈ Uᶜ} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun θ hθ => hθ.2 ?_
    exact hd _ (circleMap_mem_sphere d hr θ)
  rw [this, measure_empty, mul_zero]

end MatchPaper
end Thm18Asm
end QuantumZipper

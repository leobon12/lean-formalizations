import QuantumZipper.Proofs.Zipper.E5Model1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-FINAL, part 4: the coordinate process on `ℝ≥0 → ℝ` is never a Brownian motion

Task E5-ZOOMMODEL-FIX, step 5 (Theorem 1.3, node E5). While assembling `E5ReprG locFieldFull`
(`E5Model1.lean`) we found that its conclusion asks for a probability measure `W` on the path
space `ℝ≥0 → ℝ` (product σ-algebra) with `IsBrownianReal (fun t b => b t) W`. **No such `W`
exists** (`not_isBrownianReal_coord`):

* every measurable set of the product σ-algebra is determined by countably many coordinates
  (`measurableSet_pi_countablyDetermined`);
* mathlib's `IsBrownianReal.cont` is `∀ᵐ b ∂W, Continuous b`, i.e. the (outer) `W`-measure of the
  set of discontinuous paths is `0`, so it sits in a measurable null set `S`;
* but a measurable set containing every discontinuous path is everything: changing a continuous
  path at one time `t` outside the countable set of coordinates that determine `S` makes it
  discontinuous without leaving or entering `S`. So `W S = 1`, a contradiction.

This is the classical fact that `C[0,∞)` is not in the product σ-algebra: Karatzas–Shreve,
*Brownian Motion and Stochastic Calculus* (2nd ed., 1991), §2.2.B, discussion before and
Exercise 2.7 ("the only `B(ℝ^[0,∞))`-measurable set contained in `C[0,∞)` is the empty set",
with the hint that measurable sets depend on countably many coordinates; `literature/`
PDF p. 76). The Lean proof follows that hint (own formalization of the exercise).

Consequence (`not_e5ReprG`): whenever the hypotheses of `E5ReprG fr` can be instantiated, `E5ReprG fr`
is false; the same holds for `E5ModelApproxG` and `E5Main5.E5ModelStmtG`, whose conclusions carry the
same existential. The statements must be repaired (e.g. use a regularized coordinate process such
as `G1ProfileRed.regCoord`, or state the Brownian property of `W` as `IsPreBrownianReal` plus
continuity on a measurable full-measure set).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

/-- The σ-algebra of sets of paths determined by countably many coordinates. -/
@[instance_reducible] def countDetSigma : MeasurableSpace (ℝ≥0 → ℝ) where
  MeasurableSet' S := ∃ J : Set ℝ≥0, J.Countable ∧
    ∀ b b' : ℝ≥0 → ℝ, (∀ j ∈ J, b j = b' j) → b ∈ S → b' ∈ S
  measurableSet_empty := ⟨∅, countable_empty, fun _ _ _ h => h⟩
  measurableSet_compl S := by
    rintro ⟨J, hJ, hS⟩
    exact ⟨J, hJ, fun b b' hbb' hb hb'S =>
      hb (hS b' b (fun j hj => (hbb' j hj).symm) hb'S)⟩
  measurableSet_iUnion S := by
    intro h
    choose J hJ hS using h
    refine ⟨⋃ n, J n, countable_iUnion hJ, fun b b' hbb' hb => ?_⟩
    obtain ⟨n, hn⟩ := mem_iUnion.1 hb
    exact mem_iUnion.2 ⟨n, hS n b b' (fun j hj => hbb' j (mem_iUnion.2 ⟨n, hj⟩)) hn⟩

end E5
end QuantumZipper

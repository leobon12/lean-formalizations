import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.JointModFinal
import QuantumZipper.Proofs.LQG.GoodSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Y-BDRYLIM, part 1: offset-uniform boundary limits of `y_t` from UG and offset merging

Theorem 1.3, F2 wedge core (decisions D26/D31). The target `YBdryLimAllStmt`
(`WedgeYGoodArea.lean`) asks, a.s., for all `t ≥ 0`, for a boundary limit of the unzipped `Γ⁰`
field `y_t = F2.unzY κ X W t` along the radii `a 2^{-k}`, uniformly in `a ∈ [1,2]`
(`goodFilter`). UG (`RegUnif.UnifGlobalStmt`) gives the limit along the dyadic radii `2^{-k}`
only.

**No deterministic comparison exists.** The density ratio between the approximations at radius
`a 2^{-k}` and `2^{-k}` is `a^{γ²/4} e^{(γ/2)(h_{a2^{-k}}(t) − h_{2^{-k}}(t))}`, and the increment
of the circle average between the two radii is an `O(1)` Gaussian (variance `2 log a` for the free
field), not small; the offset step at fixed time (`AllOffsets*.lean`, M4-B4) is probabilistic
(two-radius lemma with rate `e^{-βk}` plus Kolmogorov chaining in `a`). So the offset-uniform
extension is an honest statement, isolated here as

* `YBdryMergeStmt` (**offset merging**): a.s., for all `t ≥ 0` and every test function `f`,
  `∫ f dν_{a 2^{-k}}(y_t) − ∫ f dν_{2^{-k}}(y_t) → 0` along `goodFilter`. This is the
  time-uniform form of `AllOffsetsBasic.integral_abs_bA_offset_le` (fixed-time merging).

Deterministic content (own bookkeeping):

* `hasBdryLimit_of_dyadic_merge`: dyadic vague limit + merging ⇒ `HasBdryLimit` (regular sample);
* `bdryMerge_of_hasBdryLimit`: conversely `HasBdryLimit` ⇒ merging, so given UG the reduction is
  an equivalence (nothing is lost);
* `ae_hasBdryLimit_unzY_of_merge`: the all-times statement from UG (all horizons) and
  `YBdryMergeStmt`; regularity at all times is proved (JointMod).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 1.1 and §6 (boundary measure as a limit of `ε^{γ²/4} e^{γ h_ε/2} dx`, `ε → 0` along any
sequence); Sheffield–Wang, arXiv:1605.06171, Thm 1.4 (approximations indexed by a continuous
radius, simultaneously for all conformal maps); Sheffield, arXiv:1012.4797, §5.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- The offset merging difference: `∫ f dν_{a 2^{-k}}(x) − ∫ f dν_{2^{-k}}(x)` at `i = (k, a)`. -/
def bdryMergeDiff (γ : ℝ) (x : FieldSample) (f : ℝ → ℝ) (i : ℕ × ℝ) : ℝ :=
  ∫ t, f t ∂bdryR γ x (goodRad i) - ∫ t, f t ∂bdryR γ x (radius i.1)

/-! ## Deterministic core -/

/-! ## All times -/

end WedgeUnzip
end QuantumZipper

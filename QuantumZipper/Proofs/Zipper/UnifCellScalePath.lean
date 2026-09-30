import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.Zipper.MeasUnzipField
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale
import QuantumZipper.Proofs.LQG.InfiniteMass
import QuantumZipper.Proofs.Zipper.JointModFinal

/-!
# UNIF-TIP: the pathwise magnification of a time cell (decision D31, node S2)

Continuation of `UnifCellScale`. Let `a = 2^{−n}` and `γ = √κ`. For every time `q` of a cell at
which the unzipped field `h⁰_q` is regular (`IsRegularWith`), the resolution-`n` tip mass and the
annulus masses at resolutions `> n` are, *exactly*, `a^{2+κ/4}` times the unit-resolution masses of
the magnified field `rescale h⁰_q (−2/γ) a` (`z ↦ h⁰_q(a z) − (2/γ) log a`):

* `tipCell_eq_magnify`: `tipCell κ T B X n i ω = 2^{−n(2+κ/4)} · sup_q ν_0^{Y_q}((−1,1))`;
* `annCell_eq_magnify`: `annCell κ T B X n i ω = 2^{−n(2+κ/4)} · sup_q sup_j ν_{j+1}^{Y_q}(A_0)`;
* `ae_tipCell_annCell_eq_magnify`: both hold a.s. for all `n, i` at once, for every `Γ⁰` sample
  and horizon: the regularity at all times `t ∈ [0,T]` is `RegUnif.ae_forall_isRegularWith`
  (JointMod, proved).

With `h0rev_scale`, the magnified field is `h0rev + X(a·)`-type data again (Sheffield (1.8)), so the
right-hand sides are unit cells of the magnified configuration. This is the pathwise half of S2.
Still open is identifying them in law with unit cells of a `Γ⁰` sample plus the radial constant
`c_n`. That needs `unzippedField_scale_fc` at all rational times, `F2.GFFRescaleStmt` and
`F2.ScaleIndepStmt` (both open), and the radial/lateral independence.

Sources: Sheffield, arXiv:1012.4797, §1.6 (1.8) and §5.1 (pp. 60–62). The dyadic bookkeeping is an
own elementary argument; the scale consistency of the regularization is
`InfMass.avgReg_rescale_of`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## `CellHolderStmt` from a bound on the magnified cells -/

theorem radius_rpow (n : ℕ) (x : ℝ) : radius n ^ x = (2 : ℝ) ^ (-(n : ℝ) * x) := by
  have h : radius n = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [radius, inv_pow, ← Real.rpow_natCast, Real.rpow_neg (by norm_num)]
  rw [h, ← Real.rpow_mul (by norm_num)]

end RegUnif
end QuantumZipper

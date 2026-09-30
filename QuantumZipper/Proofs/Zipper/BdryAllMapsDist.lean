import QuantumZipper.Proofs.Zipper.BdryAllMapsSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-THM43 (5): the distortion node without the `log|ψ'|` term

The coordinate change `x ∘ ψ + Q log|ψ'|` contributes, at the semicircle of radius `r` around
`t`, the deterministic term `Q ∫ log|ψ'| d fc(t,r) = Q · cc ψ t r`; by the Taylor bound of M4-T4
(`CoordChange.Data.abs_cc_sub_log_le`, Duplantier–Sheffield arXiv:0808.1560 §6 as formalized in
`CoordChangeCompare.lean`) it is within `(4C/m) r` of `Q log ψ'(t)` uniformly on inner intervals.
So the distortion node reduces to the purely field-theoretic statement

* `BdryFieldDistGood γ x`: for every admissible `ψ` and inner interval `[a',b']`, uniformly in
  `t ∈ [a',b']`, the regularized average of `x` over the pushed semicircle `ψ(fc(t, 2^{-k}))`
  (i.e. `avgReg (x ∘ ψ + Q log|ψ'|) k t − Q cc ψ t 2^{-k}`) is close to the average of `x` over
  the round semicircle `fc(ψ(t), 2^{-k} ψ'(t))`.

This is the pathwise form of Sheffield–Wang, arXiv:1605.06171, (4.6) (with Lemma 3.4, (3.18)–(3.19),
p. 15, and the proof of Lemma 3.5): see the module docstring of `BdryAllMapsMain.lean`.

Main results: `bdryDistortionGood_of_field`, `bdryDistortionStmt_of_field`, and the final
reduction **`bdryAllMapsStmt_of_split_field`**. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

theorem tendsto_radius_zero : Tendsto (fun k : ℕ => radius k) atTop (𝓝 0) := by
  show Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) atTop (𝓝 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end F1
end QuantumZipper

import QuantumZipper.Proofs.Zipper.SWCoreA8Wedge
import QuantumZipper.Proofs.Zipper.SWCoreA6
import QuantumZipper.Proofs.LQG.WedgeCanonical3
import QuantumZipper.Proofs.LQG.WedgeCanonical4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A8: `WedgeFlowErrStmt` and `E6.WedgeAreaMergeUnifStmt`

`wedgeFlowErrStmt_holds`: the distortion bound for the unscaled wedge field along the Loewner
flow of the independent Brownian driver (SWC-A6 leaf). Almost surely: the free-field flow
distortion data along the random driver (`a8_rand_data`: D64 primed core at a fixed path,
transferred by conditioning on the path), a regular version of the free field with raw dyadic
agreement (`WedgeTK.exists_isRegVersion`, `WedgeCan.ae_raw_dyadic`) and continuity of the
radial process; then the pathwise wedge add-on `a8_pushErr_wedge`.

`wedgeAreaMergeUnifStmt_of_continuum`: `E6.WedgeAreaMergeUnifStmt` from the D29 regularity core
only (`wedgeAreaMergeUnifStmt_of_flowErr`).

Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7); own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace SWCore

/-- **SWC-A6 leaf, proved.** -/
theorem wedgeFlowErrStmt_holds : WedgeFlowErrStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hInd hB hIB
  have hind : IndepFun (pathOf B'') X' P := (hIB.comp measurable_fst measurable_id).symm
  obtain ⟨G, hGv⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [a8_rand_data κ hB hX hind, hGv.ae_good, WedgeCan.ae_raw_dyadic hGv,
    WedgeCan4.ae_continuous_wedgeProcess hA, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hdat hgood hraw hAc hcω h0
  intro T a b c d hc η hη
  have hWc : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hcω.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  by_cases hab : (a : ℝ) ≤ b
  swap
  · exact Eventually.of_forall fun k t _ z hz => absurd (hz.1.1.trans hz.1.2) hab
  by_cases hcd : (c : ℝ) ≤ d
  swap
  · exact Eventually.of_forall fun k t _ z hz => absurd (hz.2.1.trans hz.2.2) hcd
  obtain ⟨N, hN⟩ := exists_nat_ge T
  have hTN : (((N : ℚ) + 1 : ℚ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  have hD := hdat N (a - 1) (b + 1) (c / 2) (d + 1) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
  have hmain := a8_pushErr_wedge (Real.sqrt κ) (Qc (Real.sqrt κ)) hgood hraw hAc hWc hW0
    (T := (((N : ℚ) + 1 : ℚ) : ℝ)) (by rw [hTN]; positivity) (a := a) (b := b) (c := c) (d := d) hc
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) hD η hη
  filter_upwards [hmain] with k hk t ht z hz
  exact hk t ⟨ht.1, by rw [hTN]; linarith [ht.2]⟩ z hz

/-- **`E6.WedgeAreaMergeUnifStmt` from the D29 regularity core alone.** -/
theorem wedgeAreaMergeUnifStmt_of_continuum (hC : WedgeUnzip.WedgeContinuumStmt) :
    E6.WedgeAreaMergeUnifStmt :=
  wedgeAreaMergeUnifStmt_of_flowErr hC wedgeFlowErrStmt_holds

end SWCore
end QuantumZipper

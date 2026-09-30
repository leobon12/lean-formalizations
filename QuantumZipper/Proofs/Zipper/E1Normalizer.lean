import QuantumZipper.Proofs.Zipper.E1Defs
import QuantumZipper.Proofs.GFF.K3.MixedRiesz

/-!
# E1: the hypotheses `IsNormalizer` are satisfiable (AUDIT10 Z10-1)

`handoff/E1-PLAN.md` and `E1Defs.IsNormalizer`: the folded circle `foldedCircle (3 i) 1` (the
normalizer named in AUDIT8) is a probability measure, admissible, carried by the compact set
`closedBall (3 i) 1 ⊆ ℍ`, and Frostman with exponent `1/3`.

Proof: existing lemmas (`isAdmissibleH_foldedCircle`, `foldedCircle_compl_eq_zero`, and the
Frostman bound `TwoPoint.isFrostman_revMap_foldedCircle` at time `0`, where `revMap` is the
identity on `ℍ`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set

namespace QuantumZipper
namespace E1

theorem three_I_mem_Hbar : (3 * Complex.I) ∈ Hbar := by
  show (0 : ℝ) ≤ (3 * Complex.I).im
  simp

theorem closedBall_three_I_subset_H : Metric.closedBall (3 * Complex.I) 1 ⊆ H := by
  intro z hz
  have h := Complex.abs_im_le_norm (z - 3 * Complex.I)
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have h2 := abs_le.1 (h.trans hz)
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one] at h2
  show 0 < z.im
  norm_num at h2
  linarith [h2.1]

/-- **AUDIT10 Z10-1.** `foldedCircle (3 i) 1` is an admissible normalizer. -/
theorem isNormalizer_foldedCircle : IsNormalizer (foldedCircle (3 * Complex.I) 1) := by
  have hz := three_I_mem_Hbar
  refine ⟨inferInstance, isAdmissibleH_foldedCircle hz one_pos,
    ⟨Metric.closedBall (3 * Complex.I) 1, isCompact_closedBall _ _,
      closedBall_three_I_subset_H, ?_⟩, ?_⟩
  · refine measure_mono_null (compl_subset_compl.2 (inter_subset_left (t := Hbar))) ?_
    exact K3.foldedCircle_compl_eq_zero hz zero_le_one
  · have hW : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
    have hF := TwoPoint.isFrostman_revMap_foldedCircle hW le_rfl (w := 3 * Complex.I)
      (r := 1) (r₀ := 1) (R := ‖3 * Complex.I‖ + 1) one_pos le_rfl le_rfl
    have hmap : (foldedCircle (3 * Complex.I) 1).map (revMap (fun _ : ℝ => (0 : ℝ)) 0) =
        foldedCircle (3 * Complex.I) 1 := by
      rw [Measure.map_congr (g := id) ?_, Measure.map_id]
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H (3 * Complex.I) one_pos] with z hz
      exact CharFun.revMap_zero_eq hW rfl hz
    rw [hmap] at hF
    exact ⟨1 / 3, _, by norm_num, fun p ρ hρ => hF p ρ hρ⟩

end E1
end QuantumZipper

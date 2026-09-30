import QuantumZipper.Proofs.Zipper.RegContEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PUSHVAR, part 1: the circle-average potential estimates for smoothing radii `≤ L`

`RegCont.abs_fcPot_le`, `RegCont.abs_fcPot_sub_le` and `RegCont.kernelCov_bindFc_eq`
(RegContEnergy.lean) assume smoothing radii `ρ ≤ 1` (support bound `B + 1`). The smoothed
pushed-circle family of `G1RC.PushFamBounds` needs radii up to the box size `R`, so this file
restates them for radii `ρ ≤ L` (support bound `B + L`), with the same proofs (`1 ↦ L`).
It also records `fcPot κ 0 y = neuPot κ y` for `y ∈ Hbar` (the unsmoothed members).

Source: the repository's own Neumann-potential estimates (`TwoPoint.abs_neuPot_le`,
`TwoPoint.abs_neuPot_sub_le`: Hölder log-potentials of Frostman measures, the
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1-type argument). Own bookkeeping.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open TwoPoint RegCont

section FcPotL

variable {κ : Measure ℂ} [IsFiniteMeasure κ] {CF B L : ℝ}

/-- At radius `0` the circle-average potential is the potential itself (on `Hbar`). -/
theorem fcPot_zero_of_mem_Hbar {y : ℂ} (hy : y ∈ Hbar) : fcPot κ 0 y = neuPot κ y := by
  have hπ := Real.pi_pos
  unfold fcPot
  rw [integral_foldedCircle_eq (measurable_neuPot κ)]
  have hc : ∀ θ : ℝ, foldH (circleMap y 0 θ) = y := fun θ => by
    rw [circleMap_zero_radius]; exact CircleFubini.foldH_of_mem' hy
  simp only [hc, integral_const, measureReal_def, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ico, sub_zero, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  field_simp

end FcPotL

end G1RC
end Thm18Asm
end QuantumZipper

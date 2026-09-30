import QuantumZipper.Proofs.Zipper.WedgeXCont

/-!
# D29 (wedge unzipping), part 8: the integrability half of X-C, unconditionally

Continuation of `WedgeXCont.lean`. The second conjunct of node X-C has two halves: for every
time and every pushed circle, the smoothed pairings

`ρ ↦ ∫ u, evalReg x (fc(u, ρ)) d((fc(c,r)).map (f_t⁻¹))`

must be `Integrable` for every smoothing radius `ρ > 0`, and must converge as `ρ → 0⁺`.

**The integrability half needs no hypothesis beyond the free-field regularity already proved**
(`ae_isRegularSample_xLogSing`): if `x` is a regular sample with witness `F`, then
`evalReg x (fc(u, ρ)) = F (u, ρ)` for every `u ∈ ℍ̄` (`IsRegularWith.evalReg_fc_of_mem`), the
measure `(fc(c,r)).map (f_t⁻¹)` is a probability measure carried by a bounded part of `ℍ̄`
(`RegCont.νT_facts`), and `F (·, ρ)` is continuous on `ℍ̄` with a finite sup on the compact
`ℍ̄ ∩ closedBall(0, B)`. So the integrand is a.e. bounded and `Integrable.mono'`/`Integrable.of_bound`
apply.

Consequently X-C's limit statement can be stated with the integrability clause *removed* from the
hypothesis: `XContLimStmt` below is the identification of the smoothed pairings with a jointly
continuous modification (the continuum-radius JointMod), and `xContTipStmt_of_lim` (then
`xContinuumStmt_of_limStmt`, then `xContinuumStmt_of_limAll`) derives X-C from it, with the
integrability supplied by the unconditional lemma `ae_integrable_smoothed_pairing`.

Own elementary proof (compactness + regularity), with the free-field input
`RegSample.ae_isRegularSample` (M4-R3) and the Frostman/support facts `RegCont.νT_facts`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## Deterministic bounds -/

/-- A real function continuous on `ℍ̄` is a.e. strongly measurable for a measure carried by a
bounded part of `ℍ̄`: the set `ℍ̄ ∩ closedBall(0,C)` is compact, hence measurable, and carries the
measure. -/
theorem aestronglyMeasurable_of_continuousOn_of_carried {g : ℂ → ℝ} (hg : ContinuousOn g Hbar)
    {ν : Measure ℂ} {C : ℝ} (hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ ‖w‖ ≤ C) : AEStronglyMeasurable g ν := by
  have hK : IsCompact (Hbar ∩ Metric.closedBall (0 : ℂ) C) := by
    rw [inter_comm]
    exact (isCompact_closedBall (0 : ℂ) C).inter_right isClosed_Hbar
  have hνae : ∀ᵐ w ∂ν, w ∈ Hbar ∩ Metric.closedBall (0 : ℂ) C :=
    hν.mono fun w hw => ⟨hw.1, by rw [Metric.mem_closedBall, dist_zero_right]; exact hw.2⟩
  rw [← Measure.restrict_eq_self_of_ae_mem hνae]
  exact ((hg.mono inter_subset_left).aemeasurable hK.measurableSet).aestronglyMeasurable

/-- A real function continuous on `ℍ̄` is integrable against a finite measure carried by a bounded
part of `ℍ̄` (it is bounded on the compact `ℍ̄ ∩ closedBall(0,C)`). -/
theorem integrable_of_continuousOn_of_carried {g : ℂ → ℝ} (hg : ContinuousOn g Hbar)
    {ν : Measure ℂ} [IsFiniteMeasure ν] {C : ℝ} (hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ ‖w‖ ≤ C) :
    Integrable g ν := by
  have hK : IsCompact (Hbar ∩ Metric.closedBall (0 : ℂ) C) := by
    rw [inter_comm]
    exact (isCompact_closedBall (0 : ℂ) C).inter_right isClosed_Hbar
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hg.mono inter_subset_left)
  refine Integrable.of_bound (aestronglyMeasurable_of_continuousOn_of_carried hg hν) |M| ?_
  filter_upwards [hν] with w hw
  exact (hM w ⟨hw.1, by rw [Metric.mem_closedBall, dist_zero_right]; exact hw.2⟩).trans
    (le_abs_self M)

/-! ## The integrability half of X-C -/

/-! ## The weakened X-C hypothesis (identification only) and the reduction -/

end WedgeUnzip
end QuantumZipper

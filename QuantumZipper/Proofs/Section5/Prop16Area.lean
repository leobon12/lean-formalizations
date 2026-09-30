import QuantumZipper.Proofs.Section5.Prop16AreaEval

/-!
# Proposition 1.6, sub-node D4-a: TV-local convergence implies `AreaConvergesInLawOn`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Proposition 1.6
(p. 25 of the PDF: the zoomed laws converge "in total variation sense" locally, and the quantum
area measure on a bounded set is a function of the field near that set); `handoff/S5-PLAN.md`
D4-a, blueprint `SECTION5_BLUEPRINT.md` D4.

`areaConvergesInLawOn_of_tvLocal`: if the laws of the pre-limit fields `Y c` converge to the law
of `Y'` TV-locally on the local coordinates `TV.locField R`, the pre-limit samples are good on
their (random) local domains `U c ω` with probability tending to `1` (`AreaGoodOn`: `U c ω ⊆ ℍ`,
`U c ω ⊇ ball 0 R ∩ ℍ`, and `areaApprox` has a vague limit on `U c ω`), the limit samples are
a.s. good on `ℍ`, and the pre-limit area pairings are random variables, then the area measures
converge in the sense of `AreaConvergesInLawOn`.

Proof: pick `R` with all test functions supported in `ball 0 R`; on good samples each pairing is
`locArea γ R f x = (locArea γ R f ∘ locRecon (R+1)) (locField (R+1) x)`
(`Prop16AreaLocal`, `Prop16AreaEval`), a measurable function of the local coordinates; the error
is `≤ 2C·P(bad) + 2C·d_TV` (bounded duality `TV.abs_integral_sub_le`). Own elementary proof.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

open TV

theorem integral_qAreaMeasure_eq_locArea {γ : ℝ} {R : ℕ} {x : FieldSample}
    (hg : ∃ μ, IsVagueLimitOn H (areaApprox γ x) μ) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfR : ∀ z, f z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R) :
    ∫ z, f z ∂qAreaMeasure γ x = locArea γ R f x := by
  have hq : IsVagueLimitOn H (areaApprox γ x) (qAreaMeasure γ x) := by
    unfold qAreaMeasure; rw [dif_pos hg]; exact hg.choose_spec
  exact integral_eq_locArea subset_rfl inter_subset_right hq hf hfc hfR

/-- Bounded duality with a general bound `C`. -/
theorem abs_integral_sub_le_mul {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : α → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ y, |g y| ≤ C) :
    |∫ y, g y ∂μ - ∫ y, g y ∂ν| ≤ 2 * max C 1 * (tvDist μ ν).toReal := by
  have hC1 : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h := abs_integral_sub_le (μ := μ) (ν := ν) (g := fun y => g y / max C 1)
    (hg.div_const _) (fun y => by
      rw [abs_div, abs_of_pos hC1, div_le_one hC1]; exact (hC y).trans (le_max_left _ _))
  rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hC1, div_le_iff₀ hC1] at h
  linarith

end Prop16Area

end QuantumZipper

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2RetainZero
import InteractingSLE.Spec.Supplement.GW2aPieceChart

/-!
# The actual conditional launch word and its zero/positive lifetime split

R51 supplies conformality of the launch chart. The staged-history clause gives
one explicit conditional GFF word and its actual flow driver. Its lifetime is
almost surely positive, or almost surely zero with exactly the same conditional
measure after the launch. No relative-tail identity is asserted here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Exist.Staged Exist.StagedLaw GW2aCont

/-- The zero-lifetime event of a flow driver is exactly the deterministic
threshold condition of its initial force word. This uses the existing GW0
pathwise lifetime criterion, with no probability-measure premise. -/
theorem ae_lifetime_eq_zero_iff_seed {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ Q h W ζ) :
    ∀ᵐ ω ∂Q, ζ ω = 0 ↔
      ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
        (flowLineXL b J 0) (flowLineXR b J 0) := by
  obtain ⟨_, _, _, _, _, _, hC⟩ := hfl
  exact hC.1.2.2.2.2.mono fun _ hp => GW0.lifetime_eq_zero_iff hp

/-- An admissible conditional seed supplies the positive-lifetime premise in
the canonical tail construction; it need not be assumed separately. -/
theorem ae_lifetime_pos_of_seed_admissible {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ Q h W ζ)
    (hadm : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
      (flowLineXL b J 0) (flowLineXR b J 0)) :
    ∀ᵐ ω ∂Q, 0 < ζ ω :=
  (ae_lifetime_eq_zero_iff_seed hfl).mono fun _ hω => pos_iff_ne_zero.2 (mt hω.1 hadm)

/-- The conditional field and the lifetime alternative at every actual launch.
The zero alternative preserves the complete conditional measure, rather than
merely its field marginal. This holds for the original R51 family. -/
theorem ae_launch_word_cases {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      c.IsConformal ∧ ∃ (bc : ℝ → ℝ) (jc : Finset ℝ)
        (hl : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        IsPiecewiseConstantBoundaryData bc jc ∧
        (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hl ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) hl bc jc ∧
        IsFlowLineDriver κ bc jc θ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) hl
          (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) ∧
        ((∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
          (E k ω).2 = 0 ∧ condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω =
            condExpKernel P (pastSigma κ b jumps spec E k) ω₀) ∨
          ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), 0 < (E k ω).2) := by
  filter_upwards [hE.2.2.2 k, hR.ae_pieceRegular, ae_zero_stop_kernel_eq hb hE hR k]
    with ω₀ hlaunch hreg hzero c θ hcθ
  have hconf := (isConformal_runChart spec (fun j => E j ω₀) k (fun j _ => hreg j)).1
  have hc := (eq_launch_of_launches spec (fun j => E j ω₀) hcθ).2.2
  obtain ⟨bc, jc, hl, hbc, hct, hfl⟩ := hlaunch c θ hcθ
  refine ⟨hc.symm ▸ hconf, bc, jc, hl, hbc, hct,
    GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hbc hfl, hfl, ?_⟩
  rcases ae_lifetime_eq_zero_or_ne hfl with hz | hp
  · left
    filter_upwards [hz, hzero c θ hcθ] with ω hω hkω
    exact ⟨hω, hkω (by rw [hω]; exact min_eq_right zero_le)⟩
  · exact Or.inr (hp.mono fun _ hω => pos_iff_ne_zero.2 hω)

/-- Every property of the complete conditional realization is preserved after
a launched zero stop. This can be instantiated with a GFF law, a marked tail
law, or a property retaining an exterior field projection. -/
theorem ae_zero_stop_preserves_measure_property
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ)
    (F : Measure Ω → Prop) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        min (instrTime spec k) (E k ω).2 = 0 →
          (F (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω) ↔
            F (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)) := by
  filter_upwards [ae_zero_stop_kernel_eq hb hE hR k] with ω₀ hω₀ c θ hcθ
  exact (hω₀ c θ hcθ).mono fun _ hω hstop => by rw [hω hstop]

end InteractingSLE.Theorem14.SB.Retain

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2RetainWord
import InteractingSLE.Spec.Supplement.SBTail2SideLaunch

/-!
# The remaining SB4 tail construction after the actual lifetime split

All measurable readout, conditional GFF, conformality and lifetime data are
proved from the original hypotheses. The named inputs below are precisely the
remaining zero-seed sewing geometry and positive-lifetime relative lower tail.
This conditional helper is not a provider of either assigned source leaf.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Leaf FlowDilate

/-- The actual-tail construction is needed only on the positive-lifetime
branch. `hzero` and `htail` are still unproved geometric/conditional-law inputs;
no source statement is replaced by this conditional helper. -/
theorem hasScheduleLaunchTail_of_seed_cases
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E)
    (hR : StagedPiecesRegular κ b jumps P ⟨x, true, scheduleProgram 0 l⟩ E)
    {specL : ExplSpec} (hELm : ∀ j, Measurable (EL j))
    (hRL : StagedPiecesRegular κ b jumps P specL EL)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) {original : Set ℝ}
    (hzero : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
        (E k ω).2 = 0) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
        ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
          HasActualTailSewing (schedulePiece κ b jumps x l (fun j => E j ω) k)
            (rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))))
    (htail : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ (bc : ℝ → ℝ) (jc : Finset ℝ) (hl : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        c.IsConformal → IsPiecewiseConstantBoundaryData bc jc →
        (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hl ω)) →
        IsGFFWithBoundaryData (condExpKernel P
          (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀) hl bc jc →
        IsFlowLineDriver κ bc jc θ (condExpKernel P
          (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀) hl
          (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) →
        (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
          0 < (E k ω).2) →
        ∃ (m : ℝ) (ER : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), m ≤ 0 ∧
          (IsBoundaryContinuedProgram
              (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true).2.2 →
            IsStagedHistory κ (affData 1 m bc) (affJumps 1 m jc)
                (condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀)
                (fun ω => affField m one_pos (hl ω))
                (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true) ER ∧
              StagedPiecesRegular κ (affData 1 m bc) (affJumps 1 m jc)
                (condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀)
                (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true) ER) ∧
          (∀ y ∈ Ioo m 0, y ∉ affJumps 1 m jc →
            (∃ p ∈ l, affData 1 m bc y = sleLambda κ - p.1 * chiC κ ∨
                affData 1 m bc y = -sleLambda κ - p.1 * chiC κ) ∨
              affData 1 m bc y ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨
              affData 1 m bc y ∈ original) ∧
          ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
            ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
            HasRelTailGeometry (schedulePiece κ b jumps x l (fun j => E j ω) k)
              (rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω)))
              (relWalkSet κ (affData 1 m bc) (affJumps 1 m jc) ER ω) m
              (fun t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E k ω).1 t)
                (fun ω => (E k ω).2) ω t)) (E k ω).2) :
    HasScheduleLaunchTail κ b jumps P h x l E k original
      (fun ω => schedulePiece κ b jumps x l (fun j => E j ω) k)
      (fun ω => rightSideOf (ExplState.physSet κ b jumps specL (fun j => EL j ω))) := by
  apply Side.hasScheduleLaunchTail_of_canonical_physSet hκ hb hE hR hELm hRL hk
  filter_upwards [ae_launch_word_cases hκ hb hE hR k, hzero, htail]
    with ω₀ hword hz ht c θ hlaunch
  obtain ⟨hc, bc, jc, hl, hbc, hct, hG, hfl, hcases⟩ := hword c θ hlaunch
  rcases hcases with h0 | hpos
  · exact Or.inl (hz c θ hlaunch (h0.mono fun _ hω => hω.1))
  · obtain ⟨m, ER, hm, hER, hclass, hgeo⟩ :=
      ht c θ hlaunch bc jc hl hc hbc hct hG hfl hpos
    exact Or.inr ⟨hc, bc, jc, hl, hbc, hct, hG, m, ER, hm, hER, hclass, hpos, hgeo⟩

end InteractingSLE.Theorem14.SB.Retain

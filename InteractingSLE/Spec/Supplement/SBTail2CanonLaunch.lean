/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2CanonState
import InteractingSLE.Spec.Supplement.SBLeafLaunchWire

/-!
# One conditional word suffices for SB4's launch construction

Packet PROVE-T14-SBTAIL2, continuation. The actual relative-tail identification is kept
as explicit mathematical data for one conditional GFF word. No new comparison premise
is introduced. Equivalent boundary-data representatives give exactly the same runs and
regular lower walk, and the previous height adapter removes extra jump candidates.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Leaf.Canon

open FlowDilate

/-- The actual-tail construction for one explicit word of the conditional field. It still
requires proof for the histories in SB4: regularity of the relative lower walk, the surviving
heights and its exact identity with the actual lifted tail are substantive fields. -/
def CanonicalLaunchData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (l : List (ℝ × ℝ≥0))
    (original : Set ℝ) (A S : Ω → Set ℂ) (ω₀ : Ω) (c : Chart) : Prop :=
  c.IsConformal ∧ ∃ (bc : ℝ → ℝ) (jc : Finset ℝ) (hl : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData bc jc ∧
    (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hl ω)) ∧
    IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) hl bc jc ∧
    ∃ (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), m ≤ 0 ∧
      (IsBoundaryContinuedProgram
          (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true).2.2 →
        IsStagedHistory κ (affData 1 m bc) (affJumps 1 m jc)
            (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
            (fun ω => affField m one_pos (hl ω))
            (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true) EL ∧
          StagedPiecesRegular κ (affData 1 m bc) (affJumps 1 m jc)
            (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
            (boundaryWalkSpec (affData 1 m bc) (affJumps 1 m jc) (-(Real.pi / 2)) true) EL) ∧
      (∀ x ∈ Ioo m 0, x ∉ affJumps 1 m jc →
        (∃ p ∈ l, affData 1 m bc x = sleLambda κ - p.1 * chiC κ ∨
            affData 1 m bc x = -sleLambda κ - p.1 * chiC κ) ∨
          affData 1 m bc x ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨
          affData 1 m bc x ∈ original) ∧
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), 0 < (E k ω).2) ∧
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        ω ∈ launchEvent κ b jumps spec E k →
        HasRelTailGeometry (A ω) (S ω)
          (relWalkSet κ (affData 1 m bc) (affJumps 1 m jc) EL ω) m
          (fun t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E k ω).1 t)
            (fun ω => (E k ω).2) ω t)) (E k ω).2

/-- The canonical word's actual-tail data give the launch data for every witness. In
particular the same `EL` and translation work; no new relative walk is selected per witness. -/
theorem launchRelData_of_canonical {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ} {A S : Ω → Set ℂ}
    {ω₀ : Ω} {c : Chart} (θ : ℝ)
    (hcanon : CanonicalLaunchData κ b jumps P h spec E k l original A S ω₀ c) :
    LaunchRelData κ b jumps P h spec E k l original A S ω₀ c θ := by
  obtain ⟨hc, bc, jc, hl, hbc, hct, hG, m, EL, hm, hEL, hclass, hpos, hgeo⟩ := hcanon
  intro b' J' hl' hb' hct' hfl
  have he : hl' = hl := funext fun ω => IsChartTransport.unique hc (hct' ω) (hct ω)
  subst hl'
  have hbM := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hbc
  have hbM' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hGM := hG.affine_finset (m := m) one_pos
  have hGM' := (GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl).affine_finset
    (m := m) one_pos
  obtain ⟨hS, hL, hR⟩ := data_eq_of_same_gff hbM hbM' hGM hGM'
  have hs := boundaryWalkSpec_eq hS (-(Real.pi / 2)) true
  refine ⟨m, EL, hm, ?_, launch_height_classification hκ hb' hfl m hbM hGM hclass, hpos, ?_⟩
  · intro hp
    obtain ⟨hE, hreg⟩ := hEL (by rw [hs]; exact hp)
    rw [hs] at hE hreg
    exact ⟨(isStagedHistory_iff hS hL hR _ EL).1 hE,
      (stagedPiecesRegular_iff hS hL hR _ EL).1 hreg⟩
  · filter_upwards [hgeo] with ω hω hlaunch
    rw [← relWalkSet_eq hS hL hR EL ω]
    exact hω hlaunch

/-- The schedule form needs a canonical construction only at actual launches. The
parametrization/incidence data are separate named hypotheses; conditional null launches
are handled by the already proved `hasLaunchRelativeTail_of_schedule`. -/
theorem hasScheduleLaunchTail_of_canonical {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {x : ℝ} {l : List (ℝ × ℝ≥0)}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {original : Set ℝ} {A S : Ω → Set ℂ}
    (hparam : ∃ a : Ω → ℝ≥0 → ℂ,
      (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
      ∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
        Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω))
    (hcanon : ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      (∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k) ω₀),
        ω ∈ launchEvent κ b jumps ⟨x, true, scheduleProgram 0 l⟩ E k →
          HasActualTailSewing (A ω) (S ω)) ∨
      CanonicalLaunchData κ b jumps P h ⟨x, true, scheduleProgram 0 l⟩ E k l
        original A S ω₀ c) :
    HasScheduleLaunchTail κ b jumps P h x l E k original A S := by
  obtain ⟨a, hm, hr⟩ := hparam
  refine ⟨a, hm, hr, ?_⟩
  filter_upwards [hcanon] with ω₀ hω c θ hlaunch
  exact (hω c θ hlaunch).imp id (launchRelData_of_canonical hκ θ)

end InteractingSLE.Theorem14.SB.Leaf.Canon

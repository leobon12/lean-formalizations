/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AdvanceCuts
import InteractingSLE.Spec.Supplement.SBS3AdvanceAnalytic

/-!
# Lemma S3 reduced to its protected comparison at rational compact arcs

Packet PROVE-T14-S3, continuation authorized by the orchestrator. The remaining
new mathematics is explicitly named `RationalJointComparisonStatement` below.
The theorem `s3RegStatement_of_rationalJointComparison` has the original S3
conclusion and makes this remaining hypothesis visible.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

/-- The local side-limit comparison configuration: one nontrivial approach in
the joint unbounded domain, an old-side label, and the four comparison limits.
The definition records analytic limits; it does not assert a conditional law. -/
def HasJointSideComparison (κ ϑ : ℝ) (l : List (ℝ × ℝ≥0)) (A : Set ℂ)
    (β : ℝ≥0 → ℂ) (a b : ℝ≥0) : Prop :=
  ∃ (p : ℂ) (F : Filter ℂ) (v₁ v₂ u₀ L₁ L₂ : ℂ → ℝ) (v : ℝ),
    p ∈ β '' Ioo a b ∧ F.NeBot ∧
    F ≤ 𝓝[H \ fillH (A ∪ β '' Icc 0 b)] p ∧ Lh.SideH κ l v ∧
    Tendsto (fun z => v₁ z - v₂ z) F (𝓝 0) ∧
    Tendsto (fun z => L₁ z - L₂ z) F (𝓝 0) ∧
    Tendsto (fun z => v₁ z + u₀ z + chiC κ * L₁ z) F (𝓝 v) ∧
    Tendsto (fun z => v₂ z + u₀ z + chiC κ * L₂ z) F
      (𝓝 (-sleLambda κ - ϑ * chiC κ))

/-- The two possible old-side labels contradict the upper-left side value in
a protected comparison configuration. -/
theorem HasJointSideComparison.false {κ ϑ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, p.1 < ϑ) {A : Set ℂ}
    {β : ℝ≥0 → ℂ} {a b : ℝ≥0} (h : HasJointSideComparison κ ϑ l A β a b) : False := by
  obtain ⟨p, F, v₁, v₂, u₀, L₁, L₂, v, -, hF, -, hv, hmean, hphase, hold, hupper⟩ := h
  let _ : F.NeBot := hF
  exact false_of_side_limits hκ hκ4 hθ hv hmean hphase hold hupper

/-- **Remaining new mathematics of S3.** Under its unchanged hypotheses, at
each fixed rational compact common arc in the physical half-plane, the
protected joint comparison exists almost surely. The own-history path premise
is discharged by `OwnHistoryPath.ownHistoryPathRegStatement` below.

This statement is a named hypothesis, not a proved source result. Its producer
must prove the joint-collar geometry, the old-word label, the nested marked
comparison and the zero inherited phase before constructing a relative driver. -/
def RationalJointComparisonStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ) (ϑ : ℝ),
      l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ p.1 < ϑ) →
      ϑ ≤ Real.pi / 2 →
    ∀ (β : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 ϑ P h β ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (schedulePrefix κ b jumps E l k ω) (β ω) a) →
    ∀ q₁ q₂ : ℚ, ∀ᵐ ω ∂P,
      (∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
        schedulePrefix κ b jumps E l k ω = p '' Icc 0 1) →
      firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) <
        ((q₁ : ℝ).toNNReal : ℝ≥0∞) →
      (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal →
      ((q₂ : ℝ).toNNReal : ℝ≥0∞) < ζ ω →
      β ω '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆
        schedulePrefix κ b jumps E l k ω ∩ H →
      HasJointSideComparison κ ϑ l (schedulePrefix κ b jumps E l k ω) (β ω)
        (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal

/-- Lemma S3 for regular families, conditional only on the explicitly named
rational protected-comparison input. The continuous own-history parametrization,
real-arc and terminal-time reductions are discharged here. -/
theorem s3RegStatement_of_rationalJointComparison (hJ : RationalJointComparisonStatement.{u}) :
    S3RegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR l k ϑ hl hθ hϑ β ζ hβ hS1
  have hpath := OwnHistoryPath.ownHistoryPathRegStatement κ hκ hκ4 b jumps hb P h hh
    E hE hR l k hl (fun p hp => (hθ p hp).1)
  have hcomp := hJ κ hκ hκ4 b jumps hb P h hh E hE hR l k ϑ hl hθ hϑ β ζ hβ hS1
  obtain ⟨_, _, W, _, _, _, -, hcoup, htrace⟩ := hβ
  filter_upwards [hpath, ae_all_iff.2 fun q₁ => ae_all_iff.2 (hcomp q₁),
    htrace, hcoup.1.2.2.2.2] with ω hp hJω ht hw
  have ht' : IsGeneratingTrace (fun t => W t ω) (ζ ω) (β ω) := by
    simpa only [Complex.ofReal_zero, sub_zero] using ht
  exact no_common_arc_of_rational_compact ht' hw.2.2.2.1 hw.1
    (fun q₁ q₂ hτ hqq hqζ hA =>
      HasJointSideComparison.false hκ hκ4 (fun p hp => (hθ p hp).2)
        (hJω q₁ q₂ hp hτ hqq hqζ hA))

end InteractingSLE.Theorem14.SB.S3

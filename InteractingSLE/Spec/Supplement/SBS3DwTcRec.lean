/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2TcRec
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBLwReg

/-!
# Successor of `SB2TcRec` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2TcRec` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_lineGeomLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Tc

open Lv Exist.Staged Exist.StagedLaw

/-! ### The real-vanishing lift of the shifted chart -/

/-! ### The chart clause at a launch -/

/-! ### The arc conditions from open time intervals -/

/-! ### Lemma S3 in SB2(1)'s configuration (named input) -/

/-! ### The record almost surely -/

/-- **SB2(1)'s chain record almost surely, geometric and chart clauses** (Theorem 1.3 and Lemma S3 as hypotheses):
almost surely at a launch, for every horizon `T ≤ ζ` after the entrance `T_L` and every `0 < S₁` with
`T_L + S₁ < T`, in the coordinates shifted by `u`: the prefix path, the shifted launch chart as a left entry chart
with boundary map (finite fibres) and real-vanishing lift, the S1 witness with `t_L = T_L` and the S2 lift, the
agreement before `t_L + S₁`, one relative chain for every `S₀ < S₁`, and no real arc on `(0, S₁)`. -/
theorem ae_lineGeomLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : SB2EntranceNoCommonArcLeStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ∀ T : ℝ≥0, (T : ℝ≥0∞) ≤ ζ ω →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < T →
      ∀ S₁ : ℝ, 0 < S₁ →
        (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toReal + S₁ < T →
      ∃ (p : ℝ → ℂ) (g : ℂ → ℂ) (β' γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
        (ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
          (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
          p '' Icc 0 1 = (fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω) ∧
        (IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1))
            (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)) ∧
          ContinuousOn g {z | 0 ≤ z.im} ∧
          EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
            (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
          (∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧
          FinRel.LiftRealOn (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
            (launchEntry κ b jumps E (k + 1) u ω))) ∧
        (Supp9B.IsProperCurve β' ∧ β' 0 = 0 ∧ p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' ∧
          β' tL = realMin (p '' Icc 0 1) ∧
          ((tL : ℝ≥0) : ℝ≥0∞) = firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) ∧
          Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s, g (γ s) = β' (tL + s)) ∧
        (∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S₁ → β' t = η ω t - u) ∧
        ((∀ S₀ : ℝ, 0 ≤ S₀ → S₀ < S₁ → FinRel.IsSB2RelChain (p '' Icc 0 1)
            (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω))
            β' γ tL S₀ Wr ηr) ∧
          interior {r ∈ Ioo (0 : ℝ) S₁ | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hwp
  filter_upwards [ae_isPrefixPath_launch HP, hR.ae_pieceRegular, HP.one_sided,
    Lw.ae_flowLine_regular h13 HP.kappa_pos HP.flow, hS3 κ b jumps P h E k u ψ η ζ HP]
    with ω hpath hpr hS1 hfl hno hF T hTζ hvis S₁ hS₁ hS₁T
  obtain ⟨p, hp⟩ := hpath hF
  have hreg : ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hlj => hpr j c θ' hlj
  obtain ⟨hc, g, hgc, hgi, hLR⟩ := chartClause_of_launch (u := u) hreg hF
  set A := lowerPrefix κ b jumps E (k + 1) u ω with hAdef
  obtain ⟨hpc, hp0, hpf, hpH, hpA⟩ := hp
  have hAcpt : IsCompact A := Lx.isCompact_lowerPrefix (u := u) hreg hF
  have huA : ((u : ℝ) : ℂ) ∈ A := hpA ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
  have hbdd : BddBelow {x : ℝ | (x : ℂ) ∈ A} := by
    obtain ⟨R, hR⟩ := hAcpt.isBounded.subset_closedBall 0
    refine ⟨-R, fun x hx => ?_⟩
    have h1 := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [neg_abs_le x]
  have hp'c : ContinuousOn (fun s => p s - u) (Icc 0 1) := hpc.sub continuousOn_const
  have hp'f : ∀ z, ((fun s => p s - u) ⁻¹' {z} ∩ Icc 0 1).Finite := fun z => by
    have e : (fun s => p s - u) ⁻¹' {z} = p ⁻¹' {z + u} := by
      ext s; simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩
    rw [e]; exact hpf (z + u)
  have hp'A : (fun s => p s - u) '' Icc 0 1 = (fun z => z - (u : ℂ)) '' A := by
    rw [← hpA, image_image]
  have hmin : realMin ((fun s => p s - u) '' Icc 0 1) = realMin A - u := by
    rw [hp'A]; exact Lw.realMin_image_sub u ⟨u, huA⟩ hbdd
  have hc' : IsLeftEntryChart ((fun s => p s - u) '' Icc 0 1) (realMin ((fun s => p s - u) '' Icc 0 1))
      (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)) := by
    rw [hmin, hp'A]; exact hc
  have hgf := finite_fibre_of_isLeftEntryChart hp'c (by simp [hp0]) hp'f hc' hgc hgi
  -- the arc conditions on `(T_L, T)`
  set TL := firstVisit (η ω) (ζ ω) (realMin A) with hTL
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hvis
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hle : ∀ s₂ : ℝ≥0, (s₂ : ℝ) ≤ (TL.toNNReal : ℝ) + ((T : ℝ) - TL.toReal) → (s₂ : ℝ≥0∞) ≤ ζ ω := by
    intro s₂ hs₂
    have h1 : (s₂ : ℝ) ≤ T := by
      have : ((TL.toNNReal : ℝ≥0) : ℝ) = TL.toReal := rfl
      linarith
    exact (ENNReal.coe_le_coe.2 (NNReal.coe_le_coe.1 h1)).trans hTζ
  have hnA : interior {r ∈ Ioo (0 : ℝ) ((T : ℝ) - TL.toReal) |
      η ω (TL.toNNReal + r.toNNReal) ∈ closure A} = ∅ :=
    interior_mem_eq_empty_of_noArc hAcpt.isClosed fun s₁ s₂ h1 h12 h2 =>
      hno hF s₁ s₂ (hTLc ▸ ENNReal.coe_le_coe.2 h1) h12 (hle s₂ h2)
  have hnR : interior {r ∈ Ioo (0 : ℝ) ((T : ℝ) - TL.toReal) |
      (η ω (TL.toNNReal + r.toNNReal)).im = 0} = ∅ :=
    interior_im_eq_zero_of_dense fun a c hac hc => hfl.2.2.2.1 a c hac (hle c hc)
  obtain ⟨β', γ, tL, Wr, ηr, h1, h2, h3, h4⟩ :=
    exists_geomRecord ⟨hpc, hp0, hpf, hpH, hpA⟩ hc' hgc hgi (hS1 hF T hTζ) hfl.2.1 hvis hnA hnR hS₁ hS₁T
  exact ⟨_, g, β', γ, tL, Wr, ηr, h1, ⟨hc', hgc, hgi, hgf, hLR⟩, h2, h3, h4⟩

end InteractingSLE.Theorem14.SB.Tc

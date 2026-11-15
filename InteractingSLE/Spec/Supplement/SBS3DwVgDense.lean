/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VgDense
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SB2VgBad
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SB2VfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVhLife

/-!
# Successor of `SB2VgDense` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VgDense` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_good_ratLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vg

open Lv Exist.Staged Exist.StagedLaw

/-- **Good rational readings are dense after the entrance**, almost surely at a launch on the entrance event. -/
theorem ae_good_ratLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ a c : ℝ, (Ve.entT κ b jumps E k u η ζ ω).toReal ≤ a → a < c → ENNReal.ofReal c < ζ ω →
        ∃ q : ℚ≥0, a < ((q : ℝ≥0) : ℝ) ∧ ((q : ℝ≥0) : ℝ) < c ∧ Vh.etaRead D q ω ∈ (I.chart ω).dom := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hwp
  filter_upwards [ae_bad_interior_emptyLe h13 hS3 HP, Lw.ae_flowLine_regular h13 HP.kappa_pos HP.flow,
    I.chart_eq, Vh.ae_etaRead_eq D, hR.ae_pieceRegular] with ω hbadω hfl hch hη hpr hF hT a c ha hac hcζ
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  set S₁ : ℝ := c - TL.toReal with hS₁
  have hS₁pos : 0 < S₁ := by rw [hS₁]; linarith
  have hS₁ζ : ENNReal.ofReal (TL.toReal + S₁) < ζ ω := by rw [hS₁, add_sub_cancel]; exact hcζ
  have hbad := hbadω hF hT S₁ hS₁pos hS₁ζ
  -- the flow is continuous before `c`
  have hc : ∀ x : ℝ≥0, (x : ℝ) < TL.toNNReal + S₁ → ContinuousAt (η ω) x := by
    intro x hx
    have hxc : ((x : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      refine lt_of_le_of_lt ?_ hcζ
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by rw [hS₁, hTLr] at hx; linarith)
    obtain ⟨y, hxy, hyζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hxc
    have hnhds : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} ∈ 𝓝 x :=
      mem_of_superset (Iio_mem_nhds (ENNReal.coe_lt_coe.1 hxy)) fun t ht =>
        (ENNReal.coe_lt_coe.2 ht).le.trans hyζ.le
    exact hfl.1.continuousAt hnhds
  -- the chart glue at a launch
  have hreg : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c', θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c' θ' hlj => hpr j c' θ' hlj
  obtain ⟨hcl, -⟩ := Tc.chartClause_of_launch (u := u) hreg hF
  have hconf := Vf.isConformal_of_shift hcl.1.1
  have hD'open : IsOpen (H \ fillH ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) := by
    rw [← hcl.1.coe_dom]; exact (Lw.shiftChart _ u _).dom.isOpen
  obtain ⟨q, hq1, hq2, hqg⟩ := exists_good_rat hD'open hc hbad (a := a - TL.toReal) (b := c - TL.toReal)
    (by linarith) (by linarith) (by rw [hS₁])
  rw [hTLr] at hq1 hq2
  refine ⟨q, by linarith, by linarith, ?_⟩
  have hqζ : ((q : ℝ≥0) : ℝ≥0∞) ≤ ζ ω := by
    refine (lt_of_le_of_lt ?_ hcζ).le
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact (Vf.relGood_iff D I hconf hcl.1 (hch hF) (hη q hqζ)).2 hqg

end InteractingSLE.Theorem14.SB.Vg

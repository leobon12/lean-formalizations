/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VdAe
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SB2VcAe
import InteractingSLE.Spec.Supplement.SBS3DwTcRec

/-!
# Successor of `SB2VdAe` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VdAe` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `ae_chain_liftOfLe`;
* `ae_clockDataLe`;
* `ae_continuous_clockOfLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vd

open Lv Vc Exist.Staged Exist.StagedLaw

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The flow's lift carries a relative chain below every horizon before the lifetime**, almost surely. -/
theorem ae_chain_liftOfLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      ∀ T₁ : ℝ≥0, (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal ≤ T₁ →
        (T₁ : ℝ≥0∞) < ζ ω →
        ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (β' : ℝ≥0 → ℂ),
          FinRel.IsSB2RelChain ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)
            (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)) β'
            (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω))
            (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
            ((T₁ : ℝ) - (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toReal)
            Wr ηr := by
  filter_upwards [ae_lineGeom_liftOfLe h13 hS3 HP] with ω hrec hF hT T₁ hT₁ hT₁ζ
  set TL := firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) with hTL
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  obtain ⟨T, hT₁T, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hT₁ζ
  have hT₁T' : (T₁ : ℝ) < T := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hT₁T)
  have hTL₁ : (TL.toNNReal : ℝ) ≤ T₁ := NNReal.coe_le_coe.2 hT₁
  have hvis : TL < T := by
    rw [← hTLc]; exact ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 (lt_of_le_of_lt hTL₁ hT₁T'))
  set S₁ : ℝ := ((T₁ : ℝ) - TL.toNNReal + ((T : ℝ) - TL.toNNReal)) / 2 with hS₁
  have hS₁pos : 0 < S₁ := by rw [hS₁]; linarith
  have hS₁T : TL.toReal + S₁ < T := by rw [hTLr, hS₁]; linarith
  obtain ⟨p, g, β', γ, tL, Wr, ηr, hp, -, hw, -, hrc, hγeq⟩ := hrec hF T hTζ.le hvis S₁ hS₁pos hS₁T
  obtain ⟨-, -, -, -, hpA⟩ := hp
  obtain ⟨-, -, -, -, htL, -, -, -⟩ := hw
  have htt : tL = TL.toNNReal := by
    rw [← ENNReal.coe_inj, hTLc]; exact htL
  subst htt
  rw [hpA] at hrc
  have hS₀ : (0 : ℝ) ≤ (T₁ : ℝ) - TL.toReal := by rw [hTLr]; linarith
  have hS₀S₁ : (T₁ : ℝ) - TL.toReal < S₁ := by rw [hTLr, hS₁]; linarith
  refine ⟨Wr, ηr, β', IsSB2RelChain.congr_lift (hrc.1 _ hS₀ hS₀S₁) fun r hr => hγeq r ?_⟩
  have := (Real.le_toNNReal_iff_coe_le hS₀).1 hr
  linarith

/-- **The capacity clock of the flow's lift vanishes at `0` and is continuous and monotone below every horizon
before the lifetime**, almost surely. -/
theorem ae_clockDataLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      Sec7.Lemma71C.capClock (fun r : ℝ => (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) r.toNNReal) 0 = 0 ∧
      ∀ T₁ : ℝ≥0, (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal ≤ T₁ →
        (T₁ : ℝ≥0∞) < ζ ω →
        ContinuousOn (Sec7.Lemma71C.capClock fun r : ℝ =>
          (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) r.toNNReal)
            (Icc 0 ((T₁ : ℝ) - (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal)) ∧
          MonotoneOn (Sec7.Lemma71C.capClock fun r : ℝ =>
            (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)) r.toNNReal)
            (Icc 0 ((T₁ : ℝ) - (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal)) := by
  filter_upwards [ae_chain_liftOfLe h13 hS3 HP] with ω hch hF hT
  refine ⟨?_, fun T₁ hT₁ hT₁ζ => ?_⟩
  · obtain ⟨Wr, ηr, β', hc⟩ := hch hF hT _ le_rfl (by rw [ENNReal.coe_toNNReal (ne_top_of_lt hT)]; exact hT)
    exact hc.2.2.2.1
  · obtain ⟨Wr, ηr, β', hc⟩ := hch hF hT T₁ hT₁ hT₁ζ
    exact ⟨hc.2.2.2.2.2.1, hc.2.2.2.2.1.monotoneOn⟩

/-- **The relative clock of the flow's lift is continuous**, almost surely at a launch on the entrance event. -/
theorem ae_continuous_clockOfLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)] :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      Continuous (clockOf (liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u
          (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
          (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal
          ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω))
        (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))).toNNReal (ζ ω)) := by
  filter_upwards [ae_clockDataLe h13 hS3 HP] with ω hd hF hT
  obtain ⟨h0, hloc⟩ := hd hF hT
  exact continuous_clockOf h0 hloc

end

end InteractingSLE.Theorem14.SB.Vd

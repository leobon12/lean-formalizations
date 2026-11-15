/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.GW1Later
import InteractingSLE.Spec.Supplement.WalkContinuum
import InteractingSLE.Spec.Supplement.BR3Ref

/-!
# Lemma GW1: the later pieces of the walks under ruling R51

Packet PROVE-T14-GW1X. PROVE-T14-GW1W proved GW1's active-word classification and its two pathwise consequences — no
later piece of the right walk ends at a new left record, and every nontrivial real connector of the right (left) walk
is in `[0, ∞)` (`(−∞, 0]`) — for staged histories whose drivers are regular at **every** sample
(`GW1W.WalkLaterRecordRegStatement`, `GW1W.WalkConnectorSideRegStatement`). The version-2 Theorem 1.4 anchors assume
only R51's `StagedPiecesRegular`. The regularized family `StagedReg.regFam E` (`StagedRegularize.lean`) is a staged
history, regular at every sample, with almost surely the same runs, so the statements transfer:

* **`walkLaterRecordR51Statement_of_gw0`**: `GW1Conn.WalkLaterRecordStatement` with R51's hypothesis
  (`WalkLaterRecordR51Statement`);
* **`walkConnectorSideRegStatement_of_gw0`**: `WalkCont.WalkConnectorSideRegStatement` (PROVE-T14-GW7's R51 form of
  `GW3Word.WalkConnectorSideStatement`), from GW0's forward implication;
* `walkLaterRecordR51Statement_of_theorem13`, `walkConnectorSideRegStatement_of_theorem13`: the same from Theorem 1.3
  (frozen type, at universe `0`) through `BR3Ref.gw0ForwardStatement_of_theorem13`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1X

open Exist Exist.StagedLaw StagedReg

/-- The two walk programs are boundary-continued. -/
theorem isBoundaryContinuedProgram_walkR (b : ℝ → ℝ) (jumps : Finset ℝ) :
    IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 := by
  have hpi := Real.pi_pos
  exact isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true

theorem isBoundaryContinuedProgram_walkL (b : ℝ → ℝ) (jumps : Finset ℝ) :
    IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2 := by
  have hpi := Real.pi_pos
  exact isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false

/-- **`GW1Conn.WalkLaterRecordStatement` under ruling R51** (its binders verbatim, plus the hypothesis of the
version-2 anchors that every staged family is `StagedPiecesRegular`): almost surely no instruction after the first ends
the right walk at a new left record, and none ends the left walk at a new right record. -/
def WalkLaterRecordR51Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω₀ ∂P, ∀ k : ℕ, 0 < k →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.2.2.1 ≠
          GW1Conn.stThr (some false) ∧
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun j => E (boundaryWalkSpec b jumps (Real.pi / 2) false) j ω₀) (k + 1)).2.2.2.2.2.1 ≠
          GW1Conn.stThr (some true)

/-- **`WalkLaterRecordR51Statement` from GW0's forward implication**: GW1W's statement for the regularized family,
transferred along the almost surely equal runs. -/
theorem walkLaterRecordR51Statement_of_gw0 (hGW0 : GW0.GW0ForwardStatement.{u}) :
    WalkLaterRecordR51Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR
  obtain ⟨hE', hreg', hrun⟩ := regFam_spec hb hE hR
  filter_upwards [GW1W.walkLaterRecordRegStatement_of_gw0 hGW0 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
      (regFam E) hE' hreg', hrun _ (isBoundaryContinuedProgram_walkR b jumps),
    hrun _ (isBoundaryContinuedProgram_walkL b jumps)] with ω h1 hR1 hL1 k hk
  rw [← hR1 (k + 1), ← hL1 (k + 1)]
  exact h1 k hk

/-- **`WalkCont.WalkConnectorSideRegStatement` from GW0's forward implication** (Lemma GW1: "Every nontrivial real
connector is rightward"; reflection for `L`), for the families of the version-2 anchors. -/
theorem walkConnectorSideRegStatement_of_gw0 (hGW0 : GW0.GW0ForwardStatement.{u}) :
    WalkCont.WalkConnectorSideRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR
  obtain ⟨hE', hreg', hrun⟩ := regFam_spec hb hE hR
  filter_upwards [GW1W.walkConnectorSideRegStatement_of_gw0 hGW0 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
      (regFam E) hE' hreg', hrun _ (isBoundaryContinuedProgram_walkR b jumps),
    hrun _ (isBoundaryContinuedProgram_walkL b jumps)] with ω h1 hR1 hL1
  obtain ⟨h1R, h1L⟩ := h1
  rw [hR1, hL1] at *
  exact ⟨h1R, h1L⟩

/-- `WalkLaterRecordR51Statement` from Theorem 1.3 (frozen type). -/
theorem walkLaterRecordR51Statement_of_theorem13 (hT13 : Exist.Theorem13Statement.{0}) :
    WalkLaterRecordR51Statement.{u} :=
  walkLaterRecordR51Statement_of_gw0 (BR3Ref.gw0ForwardStatement_of_theorem13 hT13)

/-- `WalkCont.WalkConnectorSideRegStatement` from Theorem 1.3 (frozen type). -/
theorem walkConnectorSideRegStatement_of_theorem13 (hT13 : Exist.Theorem13Statement.{0}) :
    WalkCont.WalkConnectorSideRegStatement.{u} :=
  walkConnectorSideRegStatement_of_gw0 (BR3Ref.gw0ForwardStatement_of_theorem13 hT13)

end GW1X

end Theorem14

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DuMain

/-!
# SB2(2)'s joint stage induction: the lower walk's prefixes are pinch-invariant, almost surely

Packet PROVE-SB2-LIFTSET (round 20). **`ae_pinv_walk`**: P-almost surely, every not-yet-completed prefix of the
lower walk is pinch-invariant from `0` (`LuM.pinv_prefix_walk` for CORNER's regularized family, with injective
traces and the walk's tip coordinates; the regularized family runs like the walk). This is the step of CORNER's F2a
proof (`Dv.sb2LowerStageDrivenStatement_of_thm12_thm13`) that the joint induction needs under the retained kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Restart LuM

/-- **The lower walk's prefixes are pinch-invariant, almost surely** (Theorem 1.3). -/
theorem ae_pinv_walk (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec)) :
    ∀ᵐ ω ∂P, ∀ n, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n) ≠ GW1Conn.stDone →
      LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n) := by
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hT := GW1WalkFinish.walkTipCoordinatesStatement_of_d4 h13 hD4
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Ew := StagedReg.regFam E w with hEwdef
  have hEw := hE' w hwbc
  have hregw := hreg' w
  have hRw : StagedPiecesRegular κ b jumps P w Ew := stagedPiecesRegular_of_regular h13 hκ hb hEw hregw
  have hTip := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg' true
  have hInj := ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk hκ hκ4 hb hEw hregw hRw j
  filter_upwards [hTip, hInj, GW1W.regLaunches_of_stagedPiecesRegular hRw, hrun w hwbc] with ω htipω hinjω hRLω
    hrunω
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set Dw : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => Ew i ω with hDw
  intro n hn
  have hpre : SB.prefixPhysSet κ b jumps w D n = SB.prefixPhysSet κ b jumps w Dw n := by
    unfold SB.prefixPhysSet; rw [hrunω n]
  have hn' : stStatus (ExplState.run κ b jumps w Dw n) ≠ GW1Conn.stDone := by rw [hrunω n]; exact hn
  have h1 := (LuM.pinv_prefix_walk hRLω hinjω htipω le_rfl n hn').1
  have h0 : ((↑) : ℝ → ℂ) '' Icc 0 0 ⊆ SB.prefixPhysSet κ b jumps w Dw n := by
    rw [Icc_self, image_singleton, singleton_subset_iff]
    exact WalkIntRunChron.prefixPhysSet_mono w Dw (Nat.zero_le n)
      (show ((0 : ℝ) : ℂ) ∈ SB.prefixPhysSet κ b jumps w Dw 0 from Or.inl (Or.inl (by simp [hw, boundaryWalkSpec])))
  rw [union_eq_left.2 h0] at h1
  rw [hpre]; exact h1

end InteractingSLE.Theorem14.SB.Lk

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JqStage
import InteractingSLE.Spec.Supplement.SB2LjStart
import InteractingSLE.Spec.Supplement.SB2TwLock
import InteractingSLE.Spec.Supplement.SB2MeRel
import InteractingSLE.Spec.Supplement.GW1WalkFinishRun

/-!
# SB2(2): the arc start of the data clause, almost surely (option-independent part of D6)

Packet PROVE-SB2-LIFTSET (round 15). At a zero root (an arc entry whose connector does not end at a mark) the v2
data clause needs `ArcStartData` at `relOff`. `SB2LjStart.arcStartData_of_zeroRoot` gives it from GW1's stage data,
`AllowedSt`, `PtRec` and `nz₁`; here the stage data are replaced by their run-only part, which transfers from the
regularised family to the original one, and `PtRec` is proved:

* `RunExitData` (the classified exits of the launches — a function of the run only), `runExitData_of_stageData`,
  `runExitData_of_run_eq`; `low_at_threshold'`, `arcStart_actual'`, **`arcStartData_of_zeroRoot'`** (the landed
  proofs with `RunExitData` in place of `WalkStageData`);
* `stay_of_done`, **`not_done_before_entry`** (a finished walk adds nothing, so no stage before `R`'s entry is done),
  **`recInv_ptRec_upto_entry`** (`RecInv` and `PtRec` up to the entry stage: lifetimes before it are finite);
* **`sb2LowerRunExit`**: `RunExitData` almost surely under the retained kernel (Theorem 1.3 at universe `0`);
* **`arcStartData_of_zeroRoot_ae`**: the deterministic assembly from the almost-sure actual-walk facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The classified exits of a walk's launches** (the run-only part of GW1's stage data). -/
def RunExitData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → Drv) : Prop :=
  ∀ k, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none →
    GW1WalkExit.ClassifiedExit κ b true (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1))

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

theorem runExitData_of_stageData (h : GW1WalkExit.WalkStageData κ b jumps θ true D) :
    RunExitData κ b jumps θ D :=
  fun k hl => (h k hl).2.2.2

theorem runExitData_of_run_eq {D' : ℕ → Drv}
    (hrun : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' n)
    (h : RunExitData κ b jumps θ D') : RunExitData κ b jumps θ D := by
  intro k hl
  simp only [hrun] at hl ⊢
  exact h k hl

theorem low_at_threshold' (hS : RunExitData κ b jumps θ D) {o : ℕ} (ho : o % 2 = 0)
    (hlen : o < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hthr : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) = stThr (some true) ∨
      (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) = stThr none ∧
        rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))) +
          stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) * QuantumZipper.chiC κ ≤
          -sleLambda κ)) :
    rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))) +
      θ * QuantumZipper.chiC κ ≤ -sleLambda κ := by
  have hθ := stAngle_run_walk (κ := κ) (b := b) (jumps := jumps) (θ := θ) (D := D) (right := true) (o + 1)
    (by omega)
  have hlow' : rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))) +
      stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) * QuantumZipper.chiC κ ≤
      -sleLambda κ := by
    rcases hthr with h | ⟨-, hlow⟩
    · have hl := launched_of_thrTrue ho hlen h
      have hex := (hS o hl).2 (by rw [h]; intro e; cases e)
      simpa [GW1WalkExit.BadOutwardHeight] using hex
    · exact hlow
  rwa [hθ] at hlow'


/-- **The actual side of an arc start at the first stage adding `R`**: with GW1's stage data, `AllowedSt` and `PtRec`
at the connector stage `o + 1`, the fields `move`, `angle`, `pt`, `recLe` of `ArcStartData` hold, every restart mark
is beyond `R` or `R` is the mark, and given the gap the outward height at `R` is low (`low`). -/
theorem arcStart_actual' (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hS : RunExitData κ b jumps θ D) {o : ℕ} {R : ℝ} (ho : o % 2 = 0)
    (hlen : o + 1 < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hA : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)))
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)))
    (hn : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)))
    (hn1 : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1 + 1))) :
    (ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) none true =
      if hC : (restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).Nonempty then
        ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true
          ((restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true) ∧
    stAngle (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) = θ ∧
    stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) ≤ R ∧
    stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) ≤ R ∧
    ((∀ y ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)), R < y) ∨
      R ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))) ∧
    ((∀ y ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)), R < y) →
      rightLim b R + θ * QuantumZipper.chiC κ ≤ -sleLambda κ) := by
  obtain ⟨hmove, hptR, hrec, hgap⟩ := arc_fields_of_first_stage hlen (by omega) hA hpt hn hn1
  have hθ := stAngle_run_walk (κ := κ) (b := b) (jumps := jumps) (θ := θ) (D := D) (right := true) (o + 1)
    (by omega)
  refine ⟨hmove, hθ, hptR, hrec, hgap, fun hg => ?_⟩
  -- the walk is at an outward right threshold (a mark, done or dead adds nothing)
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1) with hs
  have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1 + 1) =
      ExplState.contStep κ b jumps s none true := GW1W.run_succ_walk_cont hlen (by omega)
  rw [heq] at hn1
  have hthr : stStatus s = stThr (some true) ∨
      (stStatus s = stThr none ∧ rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ) := by
    rcases hA with h | h | h | h | ⟨h, hlow⟩
    · rw [contStep_of_arcM h] at hn1; exact absurd hn1 hn
    · rw [contStep_of_done' h] at hn1; exact absurd hn1 hn
    · rw [statePhysicalSet_congr (contStep_pieces b jumps s none true) (contStep_of_dead h true).2.2.2.2] at hn1
      exact absurd hn1 hn
    · exact Or.inl h
    · exact Or.inr ⟨h, by simpa using hlow⟩
  have hlow := low_at_threshold' hS ho (by omega) hthr
  exact rightLim_add_le_of_gap hb hθ hptR hlow hg

variable {R : ℝ}

/-- **The arc start at a zero root, at offset `relOff`**: from GW1's stage data, `AllowedSt` and `PtRec` at the
connector stage and the actual positivity `nz₁`, every relative family with a regular zero root at stage `0` has
`ArcStartData` at `relOff` (the gap: `R` is not a mark). -/
theorem arcStartData_of_zeroRoot' (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hS : RunExitData κ b jumps θ D)
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hZ : ZeroRoot κ θ b jumps R D)
    (hA : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)))
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)))
    {D₂ : ℕ → Drv} (hreg : IsRegularDriver (D₂ 0)) (hz : D₂ 0 = zeroDrv)
    (hnz : ∀ k, 2 + relOff κ θ b jumps R D ≤ k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none → (D k).2 ≠ 0) :
    ArcStartData κ θ b jumps R D D₂ (relOff κ θ b jumps R D) := by
  have ho := relOff_of_not_mark κ θ b jumps hZ.2
  obtain ⟨hn, hn1⟩ := entry_arc hex hZ.1
  have hlen := arc_len hex hZ.1
  obtain ⟨hmove, hθ, hptR, hrec, hgap, hlow⟩ :=
    arcStart_actual' hb hS (startOff_even κ θ b jumps R D) hlen hA hpt hn hn1
  have hgap' : ∀ y ∈ restartSet κ b jumps
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (startOff κ θ b jumps R D + 1)), R < y := by
    rcases hgap with h | h
    · exact h
    · exact absurd ⟨hZ.1, h⟩ hZ.2
  rw [ho] at hnz ⊢
  exact { even := startOff_even κ θ b jumps R D, len := hlen, move := hmove, angle := hθ, pt := hptR,
          recLe := hrec, gap := hgap', low := hlow hgap', reg₀ := hreg, zero₀ := by rw [hz]; exact zeroDrv_snd,
          nz₁ := hnz }

/-! ### `PtRec` up to the entry -/

/-- A finished walk stays as it is. -/
theorem stay_of_done {n : ℕ}
    (hd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = stDone) :
    ∀ m, n ≤ m → ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D m =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [GW1WalkFinish.done_run_succ _ D (by rw [ih]; exact hd), ih]

/-- **No stage before `R`'s entry is finished** (a finished walk adds nothing). -/
theorem not_done_before_entry
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    {j : ℕ} (hj : j < entryStage κ θ b jumps R D) :
    stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)) ≠ stDone := by
  intro hd
  obtain ⟨hin, hmin⟩ := entryStage_spec κ θ b jumps hex
  rw [stay_of_done hd _ (by omega : j + 1 ≤ entryStage κ θ b jumps R D + 1)] at hin
  exact hmin j hj hin

/-- **`RecInv` and `PtRec` up to the entry stage** (the lifetimes launched before it are finite). -/
theorem recInv_ptRec_upto_entry (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1))) :
    ∀ n, n ≤ entryStage κ θ b jumps R D →
      RecInv κ b jumps θ D n ∧ PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) :=
  recInv_ptRec_run_le' hP (fun _ hj hl => fin_of_not_done (not_done_before_entry hex hj) hl)
    (fun j _ => hlm j) (fun j _ => hlh j)

/-! ### Almost surely -/

/-- **The classified exits of the lower walk, almost surely under the retained kernel** (Theorem 1.3 at universe `0`,
through the regularised family). -/
theorem sb2LowerRunExit (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀),
        RunExitData κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hlwp : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hS := GW1WalkExit.walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hE' hreg' true
  have hP : ∀ᵐ ω ∂P, RunExitData κ b jumps (-(Real.pi / 2))
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := by
    filter_upwards [hS, hrun _ hlwp] with ω hω hr
    exact runExitData_of_run_eq (fun n => (hr n).symm) (runExitData_of_stageData hω)
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hP] with ω₀ hω₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  exact hω₀

/-- **The arc start of the data clause at a zero root** (deterministic, from the almost-sure actual-walk facts):
for any relative family with a regular zero root at stage `0`. -/
theorem arcStartData_of_zeroRoot_ae (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hX : RunExitData κ b jumps θ D) (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hpos : ∀ n, 0 < n → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none →
      (D n).2 ≠ 0)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hZ : ZeroRoot κ θ b jumps R D) {D₂ : ℕ → Drv} (hreg : IsRegularDriver (D₂ 0)) (hz : D₂ 0 = zeroDrv) :
    ArcStartData κ θ b jumps R D D₂ (relOff κ θ b jumps R D) := by
  have he := (startOff_eq κ θ b jumps R D).1 hZ.1
  have hpt := (recInv_ptRec_upto_entry hP hlm hlh hex (startOff κ θ b jumps R D + 1) (by omega)).2
  exact arcStartData_of_zeroRoot' hb hX hex hZ (hallow _ (by omega)) hpt hreg hz
    (fun k hk hl => hpos k (by omega) hl)

end InteractingSLE.Theorem14.SB.Lk

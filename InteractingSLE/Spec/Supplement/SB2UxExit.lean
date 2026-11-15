/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2UxHit

/-!
# Right hits at the actual launches (the input `hexit₁` of `stCorr_run_strong2`)

Packet PROVE-T14-SB2LIFT (round 21). GW1's classified exit says that after every launch of the right walk the walk is
done, at a right threshold, or at a threshold without a hit with a low right height. A finite positive launch does
not finish the walk (`stStatus_launch_ne_done`), and a threshold without a hit only comes from a zero lifetime. So the
walk is at a right threshold, which needs a right hit:

* **`rightHit_of_stageData`**: under GW1's stage data, every finite positive launch hits a point right of the record;
* **`sb2LowerRightHits`**: almost surely under the retained kernel of every retained launch (SB2(2)'s setting), for
  the original staged family (through the regularized family as in round 15: same runs, same retained data at the
  launches, `lHit_canonDrv`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkExit GW1WalkFinish

variable {κ θ : ℝ}

/-- **Every finite positive launch hits a point right of the record** under GW1's stage data. -/
theorem rightHit_of_stageData {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : WalkStageData κ b J θ true D) {k : ℕ}
    (hl : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k ≠ none) (hT : (D k).2 ≠ ⊤)
    (h0 : (D k).2 ≠ 0) :
    ∃ x : ℝ, stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) < x ∧
      lHit (stChart (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k)) ⊤ (D k) x := by
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := J) _ D hl'
  rw [Lx.instrTime_boundaryWalk_of_launch hl'] at he
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) k
    (D k) θ' ⊤ (min_top_ne_top hT)
  by_contra hR
  have hnlt : ¬ (⊤ : ℝ≥0∞) < (D k).2 := not_lt.2 le_top
  have hstat : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)) ≠ stThr (some true) ∧
      stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)) ≠ stThr none ∧
      stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)) ≠ stDone := by
    rw [he, hst]
    unfold lStatus
    simp only [hnlt, h0, hR, ↓reduceIte]
    split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h
  rcases (hS k hl).2.2.2.1 with hd | ⟨-, h | ⟨h, -⟩⟩
  · exact hstat.2.2 hd
  · exact hstat.1 h
  · exact hstat.2.1 h

/-- **Right hits at every finite positive launch of the actual lower walk, almost surely under the retained kernel**
(SB2(2)'s setting; Theorem 1.3 at universe `0`). -/
theorem sb2LowerRightHits (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀), ∀ n,
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (n + 1)).2.2.2.1 n ≠ none →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ ⊤ →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ 0 →
        ∃ x : ℝ, stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n) < x ∧
          lHit (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)) ⊤
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω) x := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hlwp : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hS := walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hE' hreg' true
  have hPa : ∀ᵐ ω ∂P, ∀ n,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (n + 1)).2.2.2.1 n ≠ none →
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ ⊤ →
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n) < x ∧
        lHit (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)) ⊤
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω) x := by
    filter_upwards [hS, hrun _ hlwp, hER _ hlwp] with ω hω hr hpr n hl hT h0
    have hl' := hl
    rw [← hr] at hl'
    have hT' : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ ⊤ := by
      rwa [StagedReg.regFam, StagedReg.regHist_snd]
    have h0' : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ 0 := by
      rwa [StagedReg.regFam, StagedReg.regHist_snd]
    obtain ⟨x, hx₀, hhit₀⟩ := rightHit_of_stageData hω hl' hT' h0'
    have hx : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n) < x := hx₀
    have hhit : lHit (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)) ⊤
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω) x := hhit₀
    -- the retained data of the launch agree
    obtain ⟨⟨c, θ'⟩, hlc⟩ := Option.ne_none_iff_exists'.1 hl
    have hspec := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ _ hlc).1
    obtain ⟨hd0, hcont, -⟩ := hpr n θ' _ c hspec hlc
    have ht := Lx.instrTime_boundaryWalk_of_launch hlc
    have hcanon : canonDrv ⊤ (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω) =
        canonDrv ⊤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω) := by
      change canonDrv ⊤ (StagedReg.regularize (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω)) = _
      rw [ht] at hcont ⊢
      exact StagedReg.canonDrv_regularize hd0 hcont
    refine ⟨x, by rw [← hr]; exact hx, ?_⟩
    rw [hr, ← lHit_canonDrv] at hhit
    rw [hcanon, lHit_canonDrv] at hhit
    exact hhit
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hPa] with ω₀ hω₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  exact hω₀

end InteractingSLE.Theorem14.SB.Lk

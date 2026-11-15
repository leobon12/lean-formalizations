/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwHead
import InteractingSLE.Spec.Supplement.SB2JwAS
import InteractingSLE.Spec.Supplement.SB2JqRun
import InteractingSLE.Spec.Supplement.SB2LdMark
import InteractingSLE.Spec.Supplement.SB2MeRel
import InteractingSLE.Spec.Supplement.SB2MeInputs
import InteractingSLE.Spec.Supplement.SB2XvProper

/-!
# SB2(2): the start piece's head before `R` at every entry kind (`StageFactsAll`, stage `0`)

Packet PROVE-SB2-LIFTSET (round 18). `Mn.StageFactsAll` asks at relative stage `0` that the start piece's points up to
its visit time of `R` lie in `hullK A`. Round 17 proved this deterministically (`head_before_visit`) under the side
condition "`R` old at the start stage ⇒ the launch starts at `R`", and at a pure piece entry. Here the remaining mark
entry and the launch itself:

* **`launch_seed_of_not_zeroRoot`**: off a zero root the actual walk launches at `relOff`, and `R` old there forces
  `stPt = R` (a pure piece entry by `piece_launch`/the first launch; a mark entry by `markStart`, with its run-only
  inputs `RunExitData`, `AllowedSt`, `PtRec` up to the entry and the walk's completion);
* `sb2LowerLaunchRelOff`: the launch at `relOff`, almost surely;
* **`head_of_not_zeroRoot`**: hence the head clause off a zero root with positive actual lifetime;
* **`sb2LowerHeadClause`**: almost surely under the retained kernel (Theorems 1.2–1.3).
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

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **Off a zero root the walk launches at `relOff`, from `R` when `R` is already there.** -/
theorem launch_seed_of_not_zeroRoot (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hX : RunExitData κ b jumps θ D) (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (boundaryWalkSpec b jumps θ true).2.2.length) = stDone) {R : ℝ}
    (hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hZ : ¬ ZeroRoot κ θ b jumps R D) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D + 1)).2.2.2.1
        (relOff κ θ b jumps R D) ≠ none ∧
      ((R : ℂ) ∈ statePhysicalSet 0
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) →
        stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) = R) := by
  classical
  have hex := exists_mem_statePhysicalSet_succ hR
  by_cases hM : MarkEntry κ θ b jumps R D
  · have ho := relOff_of_mark κ θ b jumps hM
    have hev := startOff_even κ θ b jumps R D
    obtain ⟨hn, hn1⟩ := entry_arc hex hM.1
    have hlen1 := arc_len hex hM.1
    have he := (startOff_eq κ θ b jumps R D).1 hM.1
    have hpt := (recInv_ptRec_upto_entry hP hlm hlh hex (startOff κ θ b jumps R D + 1) (by omega)).2
    have hA := hallow (startOff κ θ b jumps R D + 1) (by omega)
    obtain ⟨hmove, -, -, hrec, -, -⟩ := arcStart_actual' hb hX hev hlen1 hA hpt hn hn1
    set o := startOff κ θ b jumps R D with hodef
    have hlen2 : o + 2 < (boundaryWalkSpec b jumps θ true).2.2.length := by
      by_contra hge
      push Not at hge
      have heq : o + 2 = (boundaryWalkSpec b jumps θ true).2.2.length := by omega
      have hC : (restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).Nonempty :=
        ⟨R, hM.2⟩
      have hstep : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2) =
          ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true
            ((restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).min' hC)
            true := by
        rw [show o + 2 = o + 1 + 1 by omega, GW1W.run_succ_walk_cont (κ := κ) (D := D) hlen1 (by omega), hmove]
        simp only [hC, ↓reduceDIte]
      have hd := hdone
      rw [← heq, hstep, stStatus_moveAlong'] at hd
      exact absurd hd (by simp [stDone])
    obtain ⟨hlaunch, -, hptR, -, -⟩ := markStart hW hev hlen2 hdone hlen2.le hmove hM.2 hrec hn hn1
    refine ⟨?_, fun _ => by rw [ho]; exact hptR⟩
    rw [ho, hlaunch, launches_launch, Function.update_self]
    exact Option.some_ne_none _
  · have hA : ¬ ArcEntry κ θ b jumps R D := fun hA => hZ ⟨hA, hM⟩
    have ho : relOff κ θ b jumps R D = startOff κ θ b jumps R D := relOff_of_not_mark κ θ b jumps hM
    refine ⟨?_, seed_of_not_arc hex hA hM⟩
    rw [ho]
    by_cases h0 : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0)
    · have h1 : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = {0} :=
        statePhysicalSet_init
      have hs0 : startOff κ θ b jumps R D = 0 := by
        rw [(startOff_eq κ θ b jumps R D).2 hA]
        obtain ⟨-, hmin⟩ := entryStage_spec κ θ b jumps hex
        by_contra hne
        exact hmin 0 (Nat.pos_of_ne_zero hne) (statePhysicalSet_mono (Nat.zero_le _) h0)
      rw [hs0, GW1.launches_run_one_boundaryWalkSpec]
      exact Option.some_ne_none _
    · exact (piece_launch hex hA h0).1

/-- **The start piece's head before `R` lies in `hullK A`** off a zero root, at a positive actual lifetime. -/
theorem head_of_not_zeroRoot (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hX : RunExitData κ b jumps θ D) (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (boundaryWalkSpec b jumps θ true).2.2.length) = stDone)
    {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0} {A : Set ℂ}
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) {R : ℝ} (hβL : β₀ tL = R) (hZ : ¬ ZeroRoot κ θ b jumps R D)
    (hpos : (D (relOff κ θ b jumps R D)).2 ≠ 0) :
    ∀ r ≤ shiftD κ θ b jumps R D 0,
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D))
        (D (relOff κ θ b jumps R D)) r ∈ hullK A := by
  have hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D := by
    rw [← hβL, ← hβr]; exact mem_range_self tL
  obtain ⟨hl, hseed⟩ := launch_seed_of_not_zeroRoot hb hX hP hW hlm hlh hallow hdone hR hZ
  rw [shiftD_zero]
  exact head_before_visit hP hW hl hpos hβ hβ0 hβr hK hβL (mem_succ_of_not_zeroRoot hR hZ) hseed

/-- **The head clause of `StageFactsAll`, almost surely** under the retained kernel (Theorems 1.2–1.3): off a zero root
and at a positive actual lifetime at `relOff`, the start piece's points up to its visit of `R` lie in `hullK A`. -/
theorem sb2LowerHeadClause (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 ≠ 0 →
        ∀ r ≤ shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0,
          pcPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))) r ∈
            hullK (upperPrefix κ b jumps E u l k ω₀) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  filter_upwards [hβex,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRunExit h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerCompletion h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft]
    with ω₀ hβ₀ hT₀ hK₀ hA₀ hX₀ hD₀ hI₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' _ rfl, hK₀ c θ hlaunch b' J' h' hb' hT' hG',
    hA₀ c θ hlaunch b' J' h' hb' hT' hG', hX₀ c θ hlaunch b' J' h' hb' hT' hG',
    hD₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG']
    with ω hβω hTω hKω hAω hXω hDω hIω
  intro hZ hpos
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
  obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  exact head_of_not_zeroRoot hb hXω hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hAω hDω hβ hβ0 hβr
    (hKω β₀ hβ hβ0 hβr tL hγ.1) hγ.1 hZ hpos

/-- **Off a zero root the lower walk launches at `relOff`, almost surely** under the retained kernel (Theorems
1.2–1.3). -/
theorem sb2LowerLaunchRelOff (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
        (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
          (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
            (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  filter_upwards [hβex,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRunExit h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerCompletion h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft]
    with ω₀ hβ₀ hT₀ hA₀ hX₀ hD₀ hI₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' _ rfl,
    hA₀ c θ hlaunch b' J' h' hb' hT' hG', hX₀ c θ hlaunch b' J' h' hb' hT' hG',
    hD₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG']
    with ω hβω hTω hAω hXω hDω hIω
  intro hZ
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
  obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hR : ((lR κ b jumps E u l k ω₀ : ℝ) : ℂ) ∈ ExplState.physSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω) := by
    rw [← hγ.1, ← hβr]; exact mem_range_self tL
  exact (launch_seed_of_not_zeroRoot hb hXω hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hAω hDω hR hZ).1

end InteractingSLE.Theorem14.SB.Lk

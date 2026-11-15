/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YhAE
import InteractingSLE.Spec.Supplement.SB2YiCongr

/-!
# D51 item 3: the root S2 clause of F2b′, in the post-head chart, almost surely

Packet PROVE-T14-SB2LIFT (round 33). **`Sx.ae_isStageS2_root`**: for every relative version `V` of B's root stage
`ℓ = relOff` (`Na.StageVersionG` over the canonical chart `Mo.hullChart (fill K) x₀`, tail start `t_L = τE` the B-time
of the first visit of `R`, `τE = Na.rootEntry`, clock `0` at `τE`), at every B-time `t` and cell type `w`, almost
surely on the seed cell, at a positive relative clock below the lifetime,
`Om.IsStageS2 ((Mi.sb2StageChart … ℓ ω).loewner (Mi.sb2StopDrv … ℓ τE ω) (Mi.sb2StopTime … ℓ τE ω))
(Mo.hullChart (fill (K ω)) (x₀ ω)) (A₁ t ω) (shiftDrive (Mi.sb2StopDrv … ℓ t ω) τE)
(Mi.sb2StopTime … ℓ t ω − τE) W (a t)` — the post-head chart (B's stage chart followed by the Loewner map of the
head `B[0, τE]`), the driver and time shifted to start at `τE` (decision D51, item 3).

Inputs besides Theorems 1.2–1.3 (NOJUMP's root objects, D51 item 4, and the consumer's `hfill`): the live event lies in
`stageEvent ℓ ∩ {relOff = ℓ} ∩ {¬ ZeroRoot}`; `A₁ t = fill K`; `fill K = fill X` (`X = A ∪ P_ℓ`); `x₀` the right entry
value of `X`'s canonical chart at `realMax X = R`; `pc = Nc.bPc`; `t_L = τE`; the clock vanishes at `τE`. The proof is
the tail clause's (`Sx.ae_isStageS2_tail_of`) with the sample `Sx.isStageS2_root_all`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Sx

open Exist Exist.Staged Exist.StagedLaw Restart Lk LuM Lv Ms GW1Bookkeep Supp8.Q3Stop

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **D51 item 3: F2b′'s S2 clause at the root, in the post-head chart**, for a relative driver `W` with clock `a`
(zero at the entrance time `τE = Na.rootEntry`) and lifetime `Λ` on an event `C` of the root event. -/
theorem ae_isStageS2_root_of (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {ℓ : ℕ} {F C : Set Ω} {A₁ : ℝ≥0 → Ω → Set ℂ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {pc : Ω → ℝ≥0 → ℂ}
    {tL : Ω → ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {a : ℝ≥0 → Ω → ℝ≥0∞} {Λ : Ω → ℝ≥0∞}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (hac : ∀ ω, Continuous fun t => a t ω)
    (ham : ∀ ω, Monotone fun t => a t ω) (ha0 : ∀ ω, a 0 ω = 0) (hCF : C ⊆ F)
    (hzero : ∀ᵐ ω ∂P, ω ∈ F → a (Na.rootEntry κ b jumps E u l k ℓ ω) ω = 0)
    (htr : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ C → a t ω < Λ ω →
      ∃ ηr : ℝ → ℂ, IsLoewnerTrace (fun s : ℝ => W s.toNNReal ω) ηr ∧
        ∀ s : ℝ≥0, s ≤ t → tL ω ≤ s → pc ω s ∈ ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) →
          ηr (a s ω).toReal = (Mo.hullChart (fillH (K ω)) (x₀ ω)).1 (pc ω s))
    (hal : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ C → a t ω < Λ ω → (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      ℓ ω).2)
    (hF : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E (boundaryWalkSpec b
        jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
      ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))
    (hA₁ : ∀ t, ∀ᵐ ω ∂P, ω ∈ F → A₁ t ω = fillH (K ω))
    (hK : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = fillH (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i
      ω) ℓ))
    (hx₀ : ∀ᵐ ω ∂P, ω ∈ F →
      IsRightEntryChart (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps
        (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) (realMax
        (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2))
        true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) ((Mo.hullChart (fillH
        (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2))
        true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) 0).recenter (x₀ ω)))
    (hpc : ∀ ω, pc ω = pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun i => E
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))
    (htL : ∀ ω, tL ω = Na.rootEntry κ b jumps E u l k ℓ ω) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ C → a t ω < Λ ω → 0 < a t ω →
      Om.IsStageS2 ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
          (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (Na.rootEntry κ b jumps E u l k ℓ ω) ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (Na.rootEntry κ b jumps E u l k ℓ ω) ω))
        (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω)
        (shiftDrive (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω) (Na.rootEntry κ b jumps E u l k ℓ ω))
        (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω - (Na.rootEntry κ b jumps E u l k ℓ ω)) (fun s : ℝ => W
          s.toNNReal ω)
        (a t ω).toNNReal := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht0
  · exact Eventually.of_forall fun ω _ _ hpos => absurd (ha0 ω ▸ hpos) (lt_irrefl _)
  have ht0' : 0 < t := pos_iff_ne_zero.2 ht0
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  -- GW1's walk statements (as in CORNER's `Dv.sb2LowerStageDrivenStatement_of_thm12_thm13`)
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hGB6 := Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀) (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  have hS := GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 h13 h13₀ hClock
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hT := GW1WalkFinish.walkTipCoordinatesStatement_of_d4 h13 hD4
  have hC := GW1WalkFinish.walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 h13₀) hD4
  set w := (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hEu := hE _ hsu
  have hRu := hER _ hsu
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Ew := StagedReg.regFam E w with hEwdef
  have hEw := hE' w hwbc
  have hregw := hreg' w
  have hRw : StagedPiecesRegular κ b jumps P w Ew := stagedPiecesRegular_of_regular h13 hκ hb hEw hregw
  have hWC := Lk.ae_walkChainFacts_of_reg hS h13 hT hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    (StagedReg.regFam E) hE' hreg'
  have hTip := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg' true
  have hInj := ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk hκ hκ4 hb hEw hregw hRw j
  have hprop := (Wire.walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀).1 κ hκ hκ4 b jumps hb P h hh W' ζ'
    hcf hζ' E hE hER
  have hS3 := S3.Asm.ae_lowerTail_noArc_H h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft
  have hTipB := ae_traceAt_mem_H_stage h13 hκ hκ4 hb hh hEw hRw hregw ℓ ht0'
  filter_upwards [hWC, hTip, hInj, GW1W.regLaunches_of_stagedPiecesRegular hRw,
    GW1W.regLaunches_of_stagedPiecesRegular (hER w hwbc), hrun w hwbc, hRu, Lk.ae_injLaunches h13 hκ hκ4 hb hEu hRu,
    Lk.ae_walkInputs_of_theorem13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER, hprop, hS3, hleft, hTipB, htr t,
    hal t, hF, hA₁ t, hK, hx₀, hzero] with ω hWCω htipω hinjω hRLω hRLEω hrunω hRuω hinjuω hinpω hpropω hS3ω
    hleftω hTipBω htrω halω hFω hA₁ω hKω hx₀ω hzeroω
  intro hseed hlt hpos
  have hωF : ω ∈ F := hCF hseed
  specialize hKω hωF
  specialize hx₀ω hωF
  specialize hA₁ω hωF
  specialize hzeroω hωF
  obtain ⟨⟨hup, hlaunch⟩, hoff, hzr⟩ := hFω hωF
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set Dw : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => Ew i ω with hDw
  set Du : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E (Lu.upperSpec u l) i ω with hDu
  -- the walk at `ω`
  have hWω : WalkChainFacts κ b jumps (-(Real.pi / 2)) D := walkChainFacts_of_run_eq hrunω hWCω
  have hpinv : ∀ n, stStatus (ExplState.run κ b jumps w D n) ≠ GW1Conn.stDone →
      LuM.PInv 0 (SB.prefixPhysSet κ b jumps w D n) := by
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
  -- the upper prefix
  have hreg₀ : ∀ (i : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (Lf.sspec u l) Du (i + 1)).2.2.2.1 i = some (c', θ') →
      GW1P.PieceRegular (Du i).1 (min (instrTime (Lf.sspec u l) i) (Du i).2) :=
    fun i c' θ' hl' => hRuω i θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ := Lf.exists_path_upperPrefix hu l Du hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω := hpA
  have hpv : LuM.PInv 0 (pA '' Icc 0 1) := by rw [hpA]; exact Lk.pinv_schedule hu l Du hreg₀ hinjuω k
  -- the proper parametrization and S1
  obtain ⟨β, hβ, hβ0, hβr⟩ := hpropω
  have hav := hleftω hup
  have hav' : SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) Du k ∩ rightSideOf (range β) = ∅ := by
    rw [hβr]
    exact eq_empty_of_subset_empty ((inter_subset_inter_left _ subset_union_left).trans hav.subset)
  have hAL : upperPrefix κ b jumps E u l k ω ⊆ closedLeftSide β := Lf.subset_closedLeftSide_of_avoid hβ hβ0 hcl hav'
  have hS3β := hS3ω hup β hβ hβ0 hβr
  have hτEeq : Na.rootEntry κ b jumps E u l k ℓ ω =
      visitTime (ExplState.run κ b jumps w D ℓ) (D ℓ) (realMax (pA '' Icc 0 1)) := by rw [hpA']; rfl
  rw [hτEeq] at hzeroω
  rw [← hpA'] at hAL hS3β hoff hzr hKω hx₀ω
  -- the launch, the record and the lifetime
  have hlD : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ ≠ none := hlaunch
  have htζ : (t : ℝ≥0∞) < (D ℓ).2 := halω hseed hlt
  have hatop : a t ω ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hlD
  have hnd : stStatus (ExplState.run κ b jumps w D ℓ) ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hPR : GW1P.PieceRegular (D ℓ).1 (D ℓ).2 := by
    have h := hRLEω ℓ c' θ' hl'
    rwa [Lx.instrTime_boundaryWalk_of_launch hl', min_eq_right le_top] at h
  -- the regularized piece agrees with the piece
  have hsnd : (Dw ℓ).2 = (D ℓ).2 := StagedReg.regularize_snd _ _
  have hagree : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (D ℓ).2 → (Dw ℓ).1 r = (D ℓ).1 r := fun r hr => by
    show (StagedReg.regularize (instrTime w ℓ) (E w ℓ ω)).1 r = (E w ℓ ω).1 r
    rw [Lx.instrTime_boundaryWalk_of_launch hl']
    exact StagedReg.regularize_eq_of_le hPR.1
      (hPR.2.1.mono fun s (hs : (s : ℝ≥0∞) ≤ min ⊤ (D ℓ).2) => (show (s : ℝ≥0∞) ≤ (D ℓ).2 from
        hs.trans (min_le_right _ _))) (le_min le_top hr)
  have hlDw : (ExplState.run κ b jumps w Dw (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hrunω (ℓ + 1)]; exact hlD
  -- B's tip at `t`
  have htipD : LP.traceAt t (D ℓ).1 ∈ H := by
    have h1 := hTipBω hlDw (by rw [hsnd]; exact htζ)
    have hfr : LP.freezeAt t (Dw ℓ).1 = LP.freezeAt t (D ℓ).1 := by
      funext r
      exact hagree (min r t) ((ENNReal.coe_le_coe.2 (min_le_right r t)).trans htζ.le)
    unfold LP.traceAt at h1 ⊢
    rw [hfr] at h1
    exact h1
  -- the version at `ω`
  obtain ⟨ηV, hηV, hlinkV⟩ := htrω hseed hlt
  have hlink : ∀ s : ℝ≥0, s ≤ t → visitTime (ExplState.run κ b jumps w D ℓ) (D ℓ) (realMax (pA '' Icc 0 1)) ≤ s →
      pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) s ∈
      ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps w D ℓ)) (x₀ ω)).dom : Set ℂ) →
      ηV (a s ω).toReal = (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps w D ℓ)) (x₀ ω)).1
        (pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) s) := fun s hs hτs hd => by
    have h1 := hlinkV s hs (by rw [htL, hτEeq]; exact hτs) (by rw [hpc, hKω]; exact hd)
    rw [hpc, hKω] at h1
    exact h1
  have hmain := isStageS2_root_all hRLEω hWω (fun n => (hinpω n).1) (fun n => (hinpω n).2.1) hlD (hpinv ℓ hnd)
    hp hp0 hpH hpv hβ hβ0 hβr hAL hoff hzr hS3β htζ htipD hx₀ω (hWc ω) (hW0 ω) (hac ω)
    (ham ω) hzeroω hpos hatop hηV hlink
  -- the regularized stage chart, stopped driver and stop time
  have hchart : Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω = stChart (ExplState.run κ b jumps w D ℓ) := by
    unfold Mi.sb2StageChart
    rw [hrunω ℓ]
  have hstop : ∀ τ' : ℝ≥0, Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ' ω = headDrv (D ℓ) τ' := by
    intro τ'
    funext x
    unfold Mi.sb2StopDrv
    show (Dw ℓ).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ' : ℝ≥0∞) (Dw ℓ).2)).toNNReal = _
    rw [hsnd]
    apply hagree
    have hne : min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ' : ℝ≥0∞) (D ℓ).2) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    rw [ENNReal.coe_toNNReal hne]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have htime : ∀ τ' : ℝ≥0, Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ' ω = headTime (D ℓ) τ' := by
    intro τ'
    unfold Mi.sb2StopTime
    show ((min (τ' : ℝ≥0∞) (Dw ℓ).2).toNNReal : ℝ) = _
    rw [hsnd]
    rfl
  rw [hchart, hstop, hstop, htime, htime, hA₁ω, hKω, hτEeq]
  exact hmain

/-- **D51 item 3: F2b′'s S2 clause at the root**, for every relative version `V` of the root stage (`Na.StageVersionG`,
`pc` B's piece, `t_L = τE`, clock `0` at `τE`), in the post-head chart with driver and time shifted to start at `τE`. -/
theorem ae_isStageS2_root (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {ℓ : ℕ} {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    {ψ : ℝ} {β₁ : Ω → BoundaryWord} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    (V : Na.StageVersionG κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
    (hF : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E (boundaryWalkSpec b
        jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
      ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))
    (hA₁ : ∀ t, ∀ᵐ ω ∂P, ω ∈ F → A₁ t ω = fillH (K ω))
    (hK : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = fillH (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i
      ω) ℓ))
    (hx₀ : ∀ᵐ ω ∂P, ω ∈ F →
      IsRightEntryChart (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps
        (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) (realMax
        (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2))
        true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) ((Mo.hullChart (fillH
        (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2))
        true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) 0).recenter (x₀ ω)))
    (hpc : ∀ ω, pc ω = pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun i => E
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))
    (htL : ∀ ω, tL ω = Na.rootEntry κ b jumps E u l k ℓ ω)
    (hzero : ∀ᵐ ω ∂P, ω ∈ F → V.a (Na.rootEntry κ b jumps E u l k ℓ ω) ω = 0) :
    ∀ w ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → V.a t ω < V.Λ w ω → 0 < V.a t ω →
      Om.IsStageS2 ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
          (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (Na.rootEntry κ b jumps E u l k ℓ ω) ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (Na.rootEntry κ b jumps E u l k ℓ ω) ω))
        (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω)
        (shiftDrive (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω) (Na.rootEntry κ b jumps E u l k ℓ ω))
        (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω - (Na.rootEntry κ b jumps E u l k ℓ ω)) (fun s : ℝ =>
          V.W s.toNNReal ω)
        (V.a t ω).toNNReal := fun wt hwt =>
  ae_isStageS2_root_of h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft V.W_cont V.W_zero V.clock_cont
    V.clock_mono V.clock_zero (fun _ hω => hω.1.1) hzero (V.trace wt hwt) (V.alive wt hwt) hF hA₁ hK hx₀ hpc htL

end InteractingSLE.Theorem14.SB.Sx

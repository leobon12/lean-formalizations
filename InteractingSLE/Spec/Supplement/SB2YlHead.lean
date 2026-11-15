/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QuHead
import InteractingSLE.Spec.Supplement.SB2JqArc
import InteractingSLE.Spec.Supplement.SB2FpSeed

/-!
# The head inclusion at a zero root, two stages after the offset

Packet PROVE-T14-SB2LIFT (round 36, decision D80: the zero-root step of F3LAW's (P1), its handoff R5.4 item 5). At a
zero root (`Lk.ZeroRoot`: `R = max (A ∩ ℝ)` is first added by the connector at `relOff + 1`, and is not a restart
mark there), B's prefix through that connector lies in `hullK A`. A connector adds only real points, so B's
retained union at stage `relOff + 2` has the same part in `ℍ` as at the base.

* **`zeroRoot_facts`** (deterministic): at a sample with GW1's run facts and a proper parametrization `β₀` of the walk
  whose head up to `R` lies in `hullK A`:
  * the physical part of the walk at `relOff + 2` meets `ℍ` only inside `fill A`;
  * when B launches at `relOff + 2`, its point there is the first restart mark `m > R`, and the original heights on
    `(R, m)` are low (`GW1W.add_le_neg_of_connector` from the low height at `R`; the jumps in `(R, m)` are not
    restart marks).

  The head is `Lk.head_of_arcStart` with `Lk.arcStart_actual'`'s connector facts.
* **`ae_head_zeroRoot`**: almost surely on B's stage event at `ℓ = relOff + 2` at a zero root, the head inclusion
  `stageSet (capSpec walk ℓ (−π/2) 0) ℓ+1 ⊆ fill (upper prefix)`. This is `Qt.SB2LowerBaseHeadStatement`'s
  conclusion at that stage; the proof is `Qu.sb2LowerBaseHeadStatement`'s, with `zeroRoot_facts` in place of the
  `ℓ ≤ relOff` prefix lemma.
* **`SB2LowerBaseHeadStatementZ`**, **`sb2LowerBaseHeadStatementZ`**: the head inclusion on
  `{ℓ ≤ relOff} ∪ {relOff + 2 = ℓ, zero root}` (Theorems 1.2–1.3), combining REVIEW-FABLE-T14's
  `Qu.sb2LowerBaseHeadStatement` with `ae_head_zeroRoot`.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Sx

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P Lk Ms
  WalkSide
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

section Det

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {R : ℝ}

/-- **The walk at a zero root, two stages after the offset** (deterministic). See the module docstring. -/
theorem zeroRoot_facts (hb : IsPiecewiseConstantBoundaryData b jumps) (hX : RunExitData κ b jumps θ D)
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (boundaryWalkSpec b jumps θ true).2.2.length) = stDone)
    {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {A : Set ℂ}
    (hK : ∀ tL : ℝ≥0, β₀ tL = R → β₀ '' Icc 0 tL ⊆ hullK A) (hZ : ZeroRoot κ θ b jumps R D) :
    statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
        (relOff κ θ b jumps R D + 2)) ∩ H ⊆ fillH A ∧
      ((ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D + 3)).2.2.2.1
          (relOff κ θ b jumps R D + 2) ≠ none →
        R < stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D + 2)) ∧
        ∀ x : ℝ, R < x →
          x < stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D + 2)) →
          x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ) := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  -- `R` is in the walk
  have hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D (n + 1)) := by
    by_contra hno
    have h0 : entryStage κ θ b jumps R D = 0 := by
      unfold entryStage
      split_ifs with hc
      · exact absurd hc hno
      · rfl
    have h1 := hZ.1
    unfold ArcEntry at h1
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  have ho : relOff κ θ b jumps R D = startOff κ θ b jumps R D := relOff_of_not_mark κ θ b jumps hZ.2
  set o := startOff κ θ b jumps R D with hodef
  obtain ⟨hn, hn1⟩ := entry_arc hex hZ.1
  have hlen : o + 1 < w.2.2.length := arc_len hex hZ.1
  have he : o + 1 = entryStage κ θ b jumps R D := (startOff_eq κ θ b jumps R D).1 hZ.1
  have hev : o % 2 = 0 := startOff_even κ θ b jumps R D
  have hpt := (recInv_ptRec_upto_entry hP hlm hlh hex (o + 1) he.le).2
  obtain ⟨hmove, hθ, hptR, -, hgap, hlow⟩ := arcStart_actual' hb hX hev hlen (hallow _ (by omega)) hpt hn hn1
  have hgap' : ∀ y ∈ restartSet κ b jumps (ExplState.run κ b jumps w D (o + 1)), R < y := by
    rcases hgap with h | h
    · exact h
    · exact absurd ⟨hZ.1, h⟩ hZ.2
  have hlow' := hlow hgap'
  -- `β₀` visits `R`
  have hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps w D := by
    obtain ⟨n, hn'⟩ := hex
    rw [physSet_walk_eq_of_done le_rfl hdone]
    rcases le_total (n + 1) w.2.2.length with hle | hle
    · exact statePhysicalSet_mono hle hn'
    · rw [← Lv.run_eq_of_length_le w D hle]
      exact hn'
  obtain ⟨tL, htL⟩ : ∃ tL, β₀ tL = R := by
    rw [← hβr] at hRphys
    exact hRphys
  have hhead := head_of_arcStart hW.1 hW.2 le_rfl hdone hβ hβ0 hβr htL hlen.le hlen (by omega) hmove hptR hgap'
  have hstep : ExplState.run κ b jumps w D (o + 1 + 1) =
      ExplState.contStep κ b jumps (ExplState.run κ b jumps w D (o + 1)) none true :=
    GW1W.run_succ_walk_cont hlen (by omega)
  rw [ho]
  refine ⟨fun z hz => ?_, fun hl2 => ?_⟩
  · obtain ⟨hz, hzH⟩ := hz
    have hz' : z ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D (o + 1 + 1)) := hz
    rw [hstep, hmove] at hz'
    have hreal : ∀ x : ℝ, z = (x : ℂ) → False := fun x hx => by
      have : (0 : ℝ) < z.im := hzH
      rw [hx, Complex.ofReal_im] at this
      exact lt_irrefl _ this
    have hold : z ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D (o + 1)) := by
      split_ifs at hz' with hC
      · rw [GW1WalkChain.statePhysicalSet_moveAlong] at hz'
        rcases hz' with h | ⟨x, -, hx⟩
        · exact h
        · exact (hreal x hx.symm).elim
      · rw [GW1WalkChain.statePhysicalSet_moveToEnd, GW1WalkChain.range_realRay] at hz'
        rcases hz' with h | ⟨x, -, hx⟩
        · exact h
        · exact (hreal x hx.symm).elim
    obtain ⟨t, ht, rfl⟩ := hhead hold
    rcases hK tL htL ⟨t, ⟨zero_le, ht⟩, rfl⟩ with h1 | ⟨x, -, hx⟩
    · exact h1
    · exact (hreal x hx.symm).elim
  · -- the connector ends at the first restart mark
    obtain ⟨⟨c₂, θ₂⟩, hlc₂⟩ := Option.ne_none_iff_exists'.1 hl2
    have hnd₂ := WalkIntRunChron.not_done_of_launch w D hlc₂
    have hst2 : ExplState.run κ b jumps w D (o + 2) =
        ExplState.contStep κ b jumps (ExplState.run κ b jumps w D (o + 1)) none true := hstep
    by_cases hC : (restartSet κ b jumps (ExplState.run κ b jumps w D (o + 1))).Nonempty
    swap
    · exfalso
      rw [dite_eq_right_iff.2 (fun h => absurd h hC)] at hmove
      exact hnd₂ (by rw [hst2, hmove]; exact SB.LuM.stStatus_moveToEnd _ true)
    rw [dite_eq_left_of_eq_true (eq_true hC)] at hmove
    have hp' : stPt (ExplState.run κ b jumps w D (o + 2)) =
        (restartSet κ b jumps (ExplState.run κ b jumps w D (o + 1))).min' hC := by
      rw [hst2, hmove, GW1W.stPt_moveAlong]
    rw [hp']
    refine ⟨hgap' _ (Finset.min'_mem _ hC), fun x hRx hxm hxJ => ?_⟩
    refine GW1W.add_le_neg_of_connector hb hlow' (fun z hz hRz hzm => ?_) hRx hxm hxJ
    by_contra hgt
    have hz' : z ∈ restartSet κ b jumps (ExplState.run κ b jumps w D (o + 1)) :=
      Finset.mem_filter.2 ⟨hz, lt_of_le_of_lt hptR hRz, by rw [hθ]; exact lt_of_not_ge hgt⟩
    exact (not_le.2 hzm) ((restartSet κ b jumps (ExplState.run κ b jumps w D (o + 1))).min'_le z hz')

end Det

section AE

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)}

/-- **The head inclusion two stages after a zero root**, almost surely (Theorems 1.2–1.3). -/
theorem ae_head_zeroRoot (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2 = ℓ →
      ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω ⊆
        fillH (SB.prefixPhysSet κ b jumps (Lu.upperSpec u l)
          (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) k) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hSD := GW1WalkExit.walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hE' hreg' true
  have hCo := GW1WalkExit.walkCompletionStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _
    hE' hreg' true
  filter_upwards [Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft, hSD, hCo,
    hrun _ hwbc, hrun _ hsp] with ω hg hSω hdω hrw hru hst hrel hZ
  have hgω := hg hst.1
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  have hr' : ∀ n, ExplState.run κ b jumps w D n =
      ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n := fun n => (hrw n).symm
  have hX : RunExitData κ b jumps θ D := runExitData_of_run_eq hr' (runExitData_of_stageData hSω)
  have hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps w D n) := fun n hn => by
    rw [hr' n]
    exact (allowedSt_run hSω n).1 hn
  have hdone : stStatus (ExplState.run κ b jumps w D w.2.2.length) = GW1Conn.stDone := by
    rw [hr']
    exact hdω
  -- the head lies in `hullK A` (Lemma S2)
  obtain ⟨pA, hpc, hp0, hpH, -, hpA⟩ := hgω.upath
  obtain ⟨β₀, hβ, hβ0, hβr, hS1, -⟩ := hgω.proper
  have hS1' : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β₀ := by rw [hpA]; exact hS1
  have hK : ∀ tL : ℝ≥0, β₀ tL = realMax (upperPrefix κ b jumps E u l k ω) →
      β₀ '' Icc 0 tL ⊆ hullK (upperPrefix κ b jumps E u l k ω) := by
    intro tL hβL
    obtain ⟨-, tR, htR, -, hKR, -⟩ := s2HullRight hpc hp0 hpH hβ hβ0 hS1'
    have e : tR = tL := hβ.2.1 (htR.trans (by rw [hβL, hpA]))
    subst e
    rw [← hpA]
    exact hKR
  obtain ⟨hpre, -⟩ := zeroRoot_facts hb hX hgω.reg hgω.chain hgω.noLeftMove hgω.noLeftHit hallow hdone hβ hβ0 hβr
    hK hZ
  rw [hrel] at hpre
  -- the target hull
  have hfill : fillH (upperPrefix κ b jumps E u l k ω) =
      fillH (SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) k) := by
    show fillH (prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪
      ((↑) : ℝ → ℂ) '' Icc u 0) = _
    rw [Lw.fillH_union_real]
    unfold SB.prefixPhysSet
    rw [hru k]
  rw [← hfill]
  -- the explored set through the start of stage `ℓ`
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hst.2
  have hℓlen := lt_length_of_launch _ _ hst.2
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  obtain ⟨-, hqP⟩ := prefix_facts hgω.chain.1 hgω.chain.2 ℓ
  obtain ⟨f, α, C, hf, -, -, -, -, hα, -, -, hs, -, -⟩ := hgω.chain.1 ℓ c θ' hcθ (hqP hnd)
  have hc := (eq_launch_of_launches _ _ hcθ).2.2
  intro z hz
  rw [WalkLaw.stageSet_succ] at hz
  rcases hz with hz | hz
  · rw [WalkInf.stageSet_capSpec_of_le hℓlen.le ω le_rfl, Qt.stageSet_eq_prefixPhysSet_inter_H] at hz
    refine hpre ⟨?_, hz.2⟩
    have hz1 := hz.1
    unfold SB.prefixPhysSet at hz1
    rw [hrw ℓ] at hz1
    exact hz1
  · -- the piece of stage `ℓ` run for time `0`
    unfold WalkLaw.pieceSet at hz
    split_ifs at hz with hlz
    · exact absurd hz (notMem_empty z)
    rw [WalkSide.run_capSpec_of_le hℓlen.le _ le_rfl, WalkSide.instrTime_capSpec hℓlen.le, ENNReal.coe_zero,
      min_eq_left zero_le] at hz
    have hW0 : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).1 0 = 0 :=
      (hreg' _ ℓ ω).2.1
    have hchart : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ).2.2.2.2.1 = c := by
      rw [hrw ℓ, hc]
    rw [hchart] at hz
    have hα0 : α 0 = 0 := hα.1
    have hf0 : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (f 0)) := hf 0 (by show (0 : ℝ) ≤ (0 : ℂ).im; simp)
    have hq : f 0 = ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) : ℝ) : ℂ) := by
      rw [← hα0]
      exact hs
    have := Qu.tipSet_zero_inter_H_eq_empty hf0 hq hW0
    exact absurd hz (by rw [this]; exact notMem_empty z)

end AE

end InteractingSLE.Theorem14.SB.Sx

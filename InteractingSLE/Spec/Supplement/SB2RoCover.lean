/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FpSeed
import InteractingSLE.Spec.Supplement.SB2CtStmt
import InteractingSLE.Spec.Supplement.SB2LjStart
import InteractingSLE.Spec.Supplement.SB2CkEntr
import InteractingSLE.Spec.Supplement.SB2JwAct
import InteractingSLE.Spec.Supplement.SB2JyTip
import InteractingSLE.Spec.Supplement.SB2JwOrder
import InteractingSLE.Spec.Supplement.SB2JqStage
import InteractingSLE.Spec.Supplement.SB2JtConc

/-!
# A positive relative root lies in the root event (D79 (3), for GEOM2's `RootCover`)

PROVE-GW2-ROOTX round 17 (D79 item 3). GEOM2's root identity (`Ct.SB2LowerRootIdentStatement`) needs `RootCover`, and
for it one walk fact (GEOM2's handoff, R16.3): **at a positive root whose `R` is already explored at `ℓ` (a mark
entry), piece `ℓ` starts at `R`, so it visits `R` and the sample is in `Ne.rootEv`**. Route as GEOM2 wrote it:

* `R` lies on B's walk (the proper curve passes through it: `Lk.s2HullRight`);
* an old `R` at `ℓ = relOff` is not a zero root (if it were, `ℓ = startOff` and `entryStage = startOff + 1`, against the
  entry stage's minimality); then the launch at `relOff` seeds at `R` (`launch_seed_of_not_zeroRoot`, through
  `markStart_concrete`, with the almost sure walk facts `WalkGood`, `RunExitData`, `AllowedSt`, the walk done at its
  program length), so the piece starts at `R`, visits it at time `0`, and `entrR = 0 < ζ_ℓ`.

The pure piece entry is also covered (`R` first explored at stage `ℓ`, even, so not an arc start; the launch at `ℓ`
adds `R` to its tip set, `piece_launch`, so `entrR` is its visit time `shiftD 0 < ζ_ℓ`). Results:

* `rootEv_of_posRootAt` (one sample), **`ae_rootEv_of_posRootAt`**: almost surely, an upper launch with a positive
  root at `ℓ` (`Ct.PosRootAt`) lies in `Ne.rootEv … ℓ`;
* **`ae_rootEv_of_posRootAt_old`**: the mark-entry form, exactly as GEOM2 names it (with `R` explored at `ℓ`);
* `rootCover_of_rootEv`: `Ct.RootCover ℓ G` for every `G` containing almost every point of `Ne.rootEv … ℓ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ro

open Exist Exist.Staged Exist.StagedLaw Lk GW1W GW1Bookkeep GW1Conn

/-- **A positive relative root at `ℓ` lies in the root event** (one sample, given the walk facts). -/
theorem rootEv_of_posRootAt {Ω : Type*} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ω : Ω}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hg : Nc.WalkGood κ b jumps E u l k ω)
    (hX : RunExitData κ b jumps (-(Real.pi / 2)) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n))
    (hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) = GW1Conn.stDone)
    (hup : ω ∈ Lu.upperLaunchSet κ b jumps E u l k) (hpos : Ct.PosRootAt (κ := κ) b jumps E u l k ℓ ω) :
    ω ∈ Ne.rootEv κ b jumps E u l k ℓ := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set R := realMax (upperPrefix κ b jumps E u l k ω) with hRdef
  obtain ⟨hlℓ, ⟨hent, hoff⟩, hlife⟩ := hpos
  change (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ ≠ none at hlℓ
  change (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D (ℓ + 1)) at hent
  change relOff κ θ b jumps R D = ℓ at hoff
  change (D ℓ).2 - (shiftD κ θ b jumps R D 0 : ℝ≥0∞) ≠ 0 at hlife
  -- `R` is on B's walk
  obtain ⟨pA, hpc, hp0, hpH, -, hpA⟩ := hg.upath
  obtain ⟨β, hβ, hβ0, hβr, hS1, -⟩ := hg.proper
  have hS1' : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by rw [hpA]; exact hS1
  obtain ⟨-, tR, htR, -⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1'
  have htR' : β tR = R := by rw [htR, hpA]
  have hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps w D := by rw [← hβr, ← htR']; exact mem_range_self tR
  have hex := exists_mem_statePhysicalSet_succ (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hRphys
  obtain ⟨hentry, hmin⟩ := entryStage_spec κ θ b jumps hex
  have hposD : (D ℓ).2 ≠ 0 := fun h0 => hlife (by rw [h0]; exact zero_tsub _)
  by_cases hold : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D ℓ)
  · -- a mark entry: the piece starts at `R`
    have hZ : ¬ ZeroRoot κ θ b jumps R D := by
      rintro ⟨hArc, hM⟩
      have ho := relOff_of_not_mark (κ := κ) (θ := θ) (b₁ := b) (J₁ := jumps) hM
      have he := (startOff_eq κ θ b jumps R D).1 hArc
      have hℓ : ℓ = startOff κ θ b jumps R D := hoff.symm.trans ho
      apply hmin (startOff κ θ b jumps R D) (by omega)
      rw [← hℓ]
      exact statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) (Nat.le_succ ℓ) hold
    have hs := (launch_seed_of_not_zeroRoot hb hX hg.reg hg.chain hg.noLeftMove hg.noLeftHit hallow hdone hRphys
      hZ).2
    rw [hoff] at hs
    have hst := hs hold
    have hP0 : pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) 0 = (R : ℂ) := by
      rw [pcPt_zero_launch hg.reg hg.chain hlℓ hposD, hst]
    have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 ∧ pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) t = (R : ℂ) :=
      ⟨0, by simp, hP0⟩
    have hentr : Nd.entrR κ b jumps E u l k ℓ ω = 0 := by
      show Ck.entrTime (ExplState.run κ b jumps w D ℓ) (D ℓ) R = 0
      rw [Ck.entrTime_eq_visitTime hvis, Lk.visitTime_eq_zero_of_old hg.reg hg.chain hlℓ hposD hold]
      rfl
    refine ⟨⟨hup, hlℓ⟩, hoff, hZ, ?_⟩
    rw [hentr]
    exact pos_iff_ne_zero.2 hposD
  · -- a pure piece entry: `R` is new at `ℓ`
    have hle : entryStage κ θ b jumps R D ≤ ℓ := by
      by_contra hlt
      exact hmin ℓ (not_le.1 hlt) hent
    have hstage : entryStage κ θ b jumps R D = ℓ := by
      rcases Nat.lt_or_ge (entryStage κ θ b jumps R D) ℓ with hlt | hge
      · exact absurd (statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D)
          (Nat.succ_le_of_lt hlt) hentry) hold
      · omega
    have hA : ¬ ArcEntry κ θ b jumps R D := by
      intro hArc
      have hev := relOff_even κ θ b jumps R D
      unfold ArcEntry at hArc
      omega
    have hZ : ¬ ZeroRoot κ θ b jumps R D := fun h => hA h.1
    have h0 : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps w D 0) := fun h0 =>
      hold (statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) (Nat.zero_le _) h0)
    obtain ⟨-, -, hmem⟩ := piece_launch hex hA h0
    have hso : startOff κ θ b jumps R D = ℓ := by rw [(startOff_eq κ θ b jumps R D).2 hA, hstage]
    rw [hso] at hmem
    obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hg.reg hlℓ
    rw [htip] at hmem
    obtain ⟨t, ht, hte⟩ := hmem
    have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 ∧ pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) t = (R : ℂ) :=
      ⟨t, ht, hte⟩
    have hentr : Nd.entrR κ b jumps E u l k ℓ ω =
        (visitTime (ExplState.run κ b jumps w D ℓ) (D ℓ) R : ℝ≥0∞) :=
      Ck.entrTime_eq_visitTime hvis
    have hsh : (shiftD κ θ b jumps R D 0 : ℝ≥0∞) = (visitTime (ExplState.run κ b jumps w D ℓ) (D ℓ) R : ℝ≥0∞) := by
      simp only [shiftD, ↓reduceIte, wRun, hoff]
      rfl
    refine ⟨⟨hup, hlℓ⟩, hoff, hZ, ?_⟩
    rw [hentr, ← hsh]
    exact tsub_pos_iff_lt.1 (pos_iff_ne_zero.2 hlife)

/-- **Almost surely, an upper launch with a positive relative root at `ℓ` lies in the root event `Ne.rootEv … ℓ`**
(both a mark entry and a pure piece entry). -/
theorem ae_rootEv_of_posRootAt (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k → Ct.PosRootAt (κ := κ) b jumps E u l k ℓ ω →
      ω ∈ Ne.rootEv κ b jumps E u l k ℓ := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hSD := GW1WalkExit.walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hE' hreg' true
  have hCo := GW1WalkExit.walkCompletionStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _
    hE' hreg' true
  filter_upwards [Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft, hSD, hCo,
    hrun _ hwbc] with ω hg hSω hdω hrω hup hpos
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  have hr' : ∀ n, ExplState.run κ b jumps w D n =
      ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n := fun n => (hrω n).symm
  have hX : RunExitData κ b jumps θ D := runExitData_of_run_eq hr' (runExitData_of_stageData hSω)
  have hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps w D n) := fun n hn => by
    rw [hr' n]
    exact (allowedSt_run hSω n).1 hn
  have hdone : stStatus (ExplState.run κ b jumps w D w.2.2.length) = GW1Conn.stDone := by
    rw [hr']
    exact hdω
  exact rootEv_of_posRootAt hb (hg hup) hX hallow hdone hup hpos

/-- **The mark-entry form** (GEOM2's walk fact for `RootCover`, its handoff R16.3): almost surely, at an upper launch
with a positive root at `ℓ` whose `R` is already explored at `ℓ`, the sample is in `Ne.rootEv … ℓ`. -/
theorem ae_rootEv_of_posRootAt_old (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k → Ct.PosRootAt (κ := κ) b jumps E u l k ℓ ω →
      ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈ statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) →
      ω ∈ Ne.rootEv κ b jumps E u l k ℓ := by
  filter_upwards [ae_rootEv_of_posRootAt h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft]
    with ω hω hup hpos _
  exact hω hup hpos

/-- **`RootCover` from the root event**: if `G` contains almost every point of `Ne.rootEv … ℓ`, it covers the
positive roots at `ℓ` (CONDFIN's `Ct.RootCover`). -/
theorem rootCover_of_rootEv (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {G : Set Ω} (hG : ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ → ω ∈ G) :
    Ct.RootCover (κ := κ) b jumps P E u l k ℓ G := by
  filter_upwards [ae_rootEv_of_posRootAt h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft, hG]
    with ω hω hGω hup hpos
  exact hGω (hω hup hpos)

end InteractingSLE.Theorem14.SB.Ro

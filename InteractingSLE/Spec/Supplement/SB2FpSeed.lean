/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvHead
import InteractingSLE.Spec.Supplement.SB2LoHead
import InteractingSLE.Spec.Supplement.SB2LuRange
import InteractingSLE.Spec.Supplement.SB2LzExit
import InteractingSLE.Spec.Supplement.SB2NcWalk
import InteractingSLE.Spec.Supplement.SB2NeRoot

/-!
# The root seed: B's point at the root stage is left of `R`

Worker PROVE-SB2-F3LAW (round 4). The root step of `hL` (`Fo.ae_leftAdm_succ_succ` at `ℓ = relOff` with seed
`p = R = realMax (upperPrefix …)`) needs `stPt (run relOff) ≤ R`. **`ae_stPt_le_root`**: almost surely on the root
event `Ne.rootEv … ℓ` (`relOff = ℓ`, not a zero root):

* if `R` is already in the walk at `relOff` (a mark entry), the walk launches from `R`
  (`Lk.launch_seed_of_not_zeroRoot`, with GW1's stage data, completion and NOJUMP's walk facts `Nc.WalkGood`);
* otherwise `R` is first added by the launch at `relOff = startOff` (`Lk.piece_launch`), the walk's physical set at
  `relOff` lies on the head `β '' [0, t_R]` of the walk's proper curve (`Lk.head_of_pieceStart`), whose real points
  are `≤ R` by Lemma S2 reflected (`Lk.head_real_le_of_s2`); B's point is in that set (`Nc.WalkGood.pinv`).

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fp

open Exist Exist.Staged Exist.StagedLaw Lk GW1W GW1Bookkeep GW1Conn

/-- **B's point at the root stage is left of `R`** (almost surely on the root event). See the module docstring. -/
theorem ae_stPt_le_root (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
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
    ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) ≤
        realMax (upperPrefix κ b jumps E u l k ω) := by
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
    hrun _ hwbc] with ω hg hSω hdω hrω hroot
  obtain ⟨hev, hoff, hZ, -⟩ := hroot
  have hgω := hg hev.1
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set R := realMax (upperPrefix κ b jumps E u l k ω) with hRdef
  have hr' : ∀ n, ExplState.run κ b jumps w D n =
      ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n := fun n => (hrω n).symm
  have hX : RunExitData κ b jumps θ D := runExitData_of_run_eq hr' (runExitData_of_stageData hSω)
  have hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps w D n) := fun n hn => by
    rw [hr' n]
    exact (allowedSt_run hSω n).1 hn
  have hdone : stStatus (ExplState.run κ b jumps w D w.2.2.length) = GW1Conn.stDone := by
    rw [hr']
    exact hdω
  -- `R` is in the walk: the proper curve passes through it
  obtain ⟨pA, hpc, hp0, hpH, -, hpA⟩ := hgω.upath
  obtain ⟨β, hβ, hβ0, hβr, hS1, -⟩ := hgω.proper
  have hS1' : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by rw [hpA]; exact hS1
  obtain ⟨-, tR, htR, -⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1'
  have htR' : β tR = R := by rw [htR, hpA]
  have hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps w D := by rw [← hβr, ← htR']; exact mem_range_self tR
  by_cases hin : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D ℓ)
  · -- `R` already in the walk: the walk launches from `R`
    have hs := (launch_seed_of_not_zeroRoot hb hX hgω.reg hgω.chain hgω.noLeftMove hgω.noLeftHit hallow hdone
      hRphys hZ).2
    rw [hoff] at hs
    exact (hs hin).le
  · -- `R` first added by the launch at `relOff`
    have hex := exists_mem_statePhysicalSet_succ (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hRphys
    have hA : ¬ ArcEntry κ θ b jumps R D := by
      intro hArc
      have hM : MarkEntry κ θ b jumps R D := by
        by_contra hM
        exact hZ ⟨hArc, hM⟩
      have ho := relOff_of_mark (κ := κ) (θ := θ) (b₁ := b) (J₁ := jumps) hM
      have he := (startOff_eq κ θ b jumps R D).1 hArc
      have hent := (entryStage_spec κ θ b jumps hex).1
      apply hin
      rw [← hoff, ho]
      rw [← he] at hent
      exact hent
    have h0 : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps w D 0) := fun h0 =>
      hin (statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) (Nat.zero_le _) h0)
    obtain ⟨hl, hlaunch, hmem⟩ := piece_launch hex hA h0
    have hM : ¬ MarkEntry κ θ b jumps R D := fun h => hA h.1
    have ho := relOff_of_not_mark (κ := κ) (θ := θ) (b₁ := b) (J₁ := jumps) hM
    have hoff' : startOff κ θ b jumps R D = ℓ := ho.symm.trans hoff
    have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
    have hhead := head_of_pieceStart hgω.chain.1 hgω.chain.2 le_rfl hdone hβ hβ0 hβr htR' hlen.le hlaunch hmem
    obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
    have hnd := WalkIntRunChron.not_done_of_launch w D hl'
    have hpt := (hgω.pinv _ hnd).2
    obtain ⟨t, ht, hte⟩ := hhead hpt
    have hle := head_real_le_of_s2 hpc hp0 hpH hβ hβ0 hS1' (by rw [htR', hpA]) t ht _ hte
    rw [hpA, hoff'] at hle
    exact hle

end InteractingSLE.Theorem14.SB.Fp

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2PqAE
import InteractingSLE.Spec.Supplement.SB2YiAE

/-!
# D66's (P) at the root: `hpb` on the root version's cells

Packet PROVE-GW2-NOTHR (round 8, decision D67 (3)). **`ae_hpb_root`**: for every relative version `V` of B's root stage
`ℓ = relOff` (the setting of SB2LIFT's `Sx.ae_isStageS2_root`), every cell type `w` and every B-time `t`, almost surely
on the seed cell at a positive relative clock below the lifetime, B's own stage pull-back holds in SB2LIFT's post-head
chart (CONDFIN's `hpb` of `Cr.ae_lineMean_pos_root` with `c` = the post-head chart, `wB t = shiftDrive (stopDrv t) τE`,
`sB t = stopTime t − τE`, `τE = Na.rootEntry`), for the line family's sets `(A₁, A₂)` with its stage-chart pull-back
(`Ml.exists_sb2LineFamily_cf`).

Every premise of `ae_isStagePullback_postHead` is discharged here: the capped launch event at `t` (the stage event and
the version's lifetime), `τE ≤ t` (the clock vanishes at `τE` and is positive at `t`), and the S2 record with `Φ` the
canonical hull chart of `fill K = A₁ t` (`Sx.ae_isStageS2_root`, `subset_image_hullChart`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Pq

open Exist Exist.Staged Exist.StagedLaw Restart Lk LuM Lv Ms GW1Bookkeep Supp8.Q3Stop WalkSide

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **D66's (P) at the root**: B's own stage pull-back in the post-head chart on the root version's cells. -/
theorem ae_hpb_root (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
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
    (hzero : ∀ᵐ ω ∂P, ω ∈ F → V.a (Na.rootEntry κ b jumps E u l k ℓ ω) ω = 0)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hpull : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
      (ExplState.run κ b jumps (Lu.upperSpec u l)
        (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none →
      ∃ g : ℂ → ℂ, Ln.IsStagePullback (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω) g (A₁ t ω) (A₂ t ω)
        {w | (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 w ∈ A₁ t ω}
        (fwdHull (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω))) :
    ∀ wt ∈ types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F wt → V.a t ω < V.Λ wt ω → 0 < V.a t ω →
      ∃ g' : ℂ → ℂ, Ln.IsStagePullback
        ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
          (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (Na.rootEntry κ b jumps E u l k ℓ ω) ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (Na.rootEntry κ b jumps E u l k ℓ ω) ω)) g' (A₁ t ω)
        (A₂ t ω)
        {w | ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
          (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (Na.rootEntry κ b jumps E u l k ℓ ω) ω)
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (Na.rootEntry κ b jumps E u l k ℓ ω) ω)).2.1 w ∈ A₁ t ω}
        (fwdHull (shiftDrive (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω) (Na.rootEntry κ b jumps E u l k ℓ ω))
          (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω - Na.rootEntry κ b jumps E u l k ℓ ω)) := by
  intro wt hwt t
  have hS2 := Sx.ae_isStageS2_root h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft V hF hA₁ hK hx₀ hpc htL
    hzero wt hwt t
  obtain ⟨-, -, hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hsu := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  set G : Set Ω := {ω | ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ∧
    (ExplState.run κ b jumps (Lu.upperSpec u l)
      (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none} with hG
  have hpb := ae_isStagePullback_postHead h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER ℓ t (G := G)
    ((hpull t).mono fun ω h hGω => h hGω.1 hGω.2) (fun ω => Na.rootEntry κ b jumps E u l k ℓ ω)
  filter_upwards [hS2, hpb, V.alive wt hwt t, hF, hA₁ t, hzero, hrun _ hw, hrun _ hsu]
    with ω hS2ω hpbω halω hFω hA₁ω hzeroω hrw hru hcell hlt hpos
  have hωF : ω ∈ F := hcell.1.1
  obtain ⟨⟨hup, hlaunch⟩, -, -⟩ := hFω hωF
  have hcap : ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t := by
    refine ⟨?_, ?_⟩
    · show (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j =>
        StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none
      rw [hrw (ℓ + 1)]
      exact hlaunch
    · have hsnd : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 =
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := StagedReg.regularize_snd _ _
      rw [hsnd]
      exact halω hcell hlt
  have hGω : ω ∈ G := ⟨hcap, by rw [hru (k + 1)]; exact hup⟩
  have hτt : Na.rootEntry κ b jumps E u l k ℓ ω ≤ t := by
    by_contra hcon
    have h1 : V.a t ω ≤ V.a (Na.rootEntry κ b jumps E u l k ℓ ω) ω := V.clock_mono ω (le_of_lt (not_le.1 hcon))
    rw [hzeroω hωF] at h1
    exact absurd (hpos.trans_le h1) (lt_irrefl _)
  refine hpbω hGω hcap hτt ⟨Mo.hullChart (fillH (K ω)) (x₀ ω), _, _, _, _, hS2ω hcell hlt hpos, ?_⟩
  rw [hA₁ω hωF]
  exact subset_image_hullChart (Mo.isHPHull_fillH hKc hKp ω) (x₀ ω)

end InteractingSLE.Theorem14.SB.Pq

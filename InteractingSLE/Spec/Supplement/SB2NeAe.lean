/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NePhys
import InteractingSLE.Spec.Supplement.SB2WfPi
import InteractingSLE.Spec.Supplement.GW1ExtWire
import InteractingSLE.Spec.Supplement.WalkCapBlockMain

/-!
# B's piece on the original real line, almost surely at every walk launch

Packet PROVE-AUX61-NOJUMP (round 22, component F). For the regularized family of the lower walk (angle `−π/2`), at
every launch `ℓ` with a positive lifetime, almost surely:

* the record `R = stRecR (run ℓ)` (which is the walk's point) is off the closure of the original right-bad points
  right of `R`;
* before the lifetime, B's piece never meets that closure right of `R`;
* at a finite lifetime it ends at an original right-bad point right of `R`.

Ingredients: SB2WORD's stage witness and its invariant (`Wf.exists_witness_right_lwoj`, GW1's `RInv`), the
forbidden set and seed (`Wf.ae_stage_avoid`), the tip and the marks (`Ne.ae_stage_tip`), GW1's exterior record and
record bound (`GW1WalkExit.walk_recordGeometry`, `GW1Ext.rawRecordBound_of_launch`), the run chart's domain
(`Lk.image_runChart_walk_eq`), and the deterministic `Ne.phys_facts`.

* `ball_disjoint_fillH_right`, `fin_of_later_launch`, **`ae_walk_phys`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Ne

open Exist Exist.StagedLaw Exist.Staged Restart GW1W LuM Lk

/-- **A real point right of every real point of a compact set has a ball missing its fill** (mirror of
`Lw.exists_ball_disjoint_fillH`; the argument of F3LAW's `Fm.exists_ball_disjoint_fillH_right`). -/
theorem ball_disjoint_fillH_right {A : Set ℂ} (hA : IsCompact A) {x : ℝ}
    (hx : ∀ y : ℝ, (y : ℂ) ∈ A → y < x) : ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH A) := by
  have hAc : IsCompact (LP.reflectC '' A) := hA.image (by unfold LP.reflectC; fun_prop)
  have hx' : ∀ y : ℝ, (y : ℂ) ∈ LP.reflectC '' A → -x < y := by
    rintro y ⟨z, hz, hzy⟩
    have hz' : z = ((-y : ℝ) : ℂ) := by
      apply LP.reflectC_injective
      rw [hzy, LP.reflectC_ofReal, neg_neg]
    rw [hz'] at hz
    have := hx _ hz
    linarith
  obtain ⟨ρ, hρ, hd⟩ := Lw.exists_ball_disjoint_fillH hAc hx'
  refine ⟨ρ, hρ, Set.disjoint_left.2 fun z hzb hzF => ?_⟩
  have h1 : LP.reflectC z ∈ ball (((-x : ℝ) : ℂ)) ρ := by
    rw [← LP.reflectC_ofReal, ← LP.image_reflectC_ball]
    exact mem_image_of_mem _ hzb
  have h2 : LP.reflectC z ∈ fillH (LP.reflectC '' A) := by
    rw [LP.fillH_image_reflectC]
    exact mem_image_of_mem _ hzF
  exact Set.disjoint_left.1 hd h1 h2

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Pieces launched before a later launch have finite lifetimes.** -/
theorem fin_of_later_launch {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ∀ j < ℓ, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤ := by
  intro j hj hlj
  refine Lk.fin_of_not_done (fun hd => ?_) hlj
  obtain ⟨⟨c, θ'⟩, hc⟩ := Option.ne_none_iff_exists'.1 hl
  exact WalkIntRunChron.not_done_of_launch _ _ hc (Lk.done_of_le hd (Nat.succ_le_of_lt hj))


section Ae

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **B's piece on the original real line, almost surely at a walk launch** (regularized family). -/
theorem ae_walk_phys (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none →
      0 < (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) =
        stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) ∧
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) ∉
        closure (origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ))) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        ∀ x : ℝ, pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) t = x →
          stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) < x →
          x ∉ closure (origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)))) ∧
      ((StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≠ ⊤ →
        ∃ x : ℝ, pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2.toNNReal = x ∧
          x ∈ origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ))) := by
  classical
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hprog : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  set Ew := StagedReg.regFam E w with hEwdef
  have hEw := hE' w hprog
  have hRw : StagedPiecesRegular κ b jumps P w Ew := WalkLaw.stagedPiecesRegular_regHist (hER _ hprog)
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ := by
    have := WalkCapBlock.ambientSideBound_of_counterflow h13₀ hκ hκ4 hb hh hcf hζ' true
    simpa [WalkCapBlock.AmbientSideBound] using this
  obtain ⟨β, Y, hW, hInv⟩ := Wf.exists_witness_right_lwoj hκ hκ4 (ψ := 0) (u := 0)
    (show -(Real.pi / 2) < (0 : ℝ) by linarith [Real.pi_pos]) hb hh hEw (hreg' w) hRw hamb ℓ
  filter_upwards [hInv, Wf.ae_stage_avoid hκ hκ4 hb hh hEw (hreg' w) hRw hW,
    ae_stage_tip hκ hκ4 hb hh hEw (hreg' w) hRw hW,
    GW1WalkExit.ae_walkStageData_right hκ hb hh hEw (hreg' w) hamb, hRw,
    GW1W.regLaunches_of_stagedPiecesRegular hRw] with ω hInvω hAvω hTipω hsω hrω hRLω hl hz
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => Ew j ω with hD
  set s := ExplState.run κ b jumps w D ℓ with hs
  have hP : ∀ j c θ', (ExplState.run κ b jumps w D (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (D j).1 (min (instrTime w j) (D j).2) :=
    fun j c θ' hl' => hrω j θ' _ c (eq_launch_of_launches _ _ hl').1 hl'
  have hX := (GW1WalkExit.walk_recordGeometry hκ hb D (fun j => hreg' w j ω) hsω hP).2 ℓ hl
  have hB := GW1Ext.rawRecordBound_of_launch hκ hb D (fun j => hreg' w j ω) hsω hP hl
  obtain ⟨hRP, hpt, hext⟩ : RProf s ∧ stPt s = stRecR s ∧
      ∀ x, stRecR s < x → extendFrom H (stChart s).2.1 ((stChart s).1 (x : ℂ)) = (x : ℂ) := hX.1
  obtain ⟨hleft, -, hO⟩ := (hInvω hl).1
  obtain ⟨hseed', havoid⟩ := hAvω hl
  have hseed := hseed' hz
  obtain ⟨htip, hmark⟩ := hTipω hl hz
  have hcc := isConformal_runChart_of_reg w hRLω ℓ
  have hcb := (GW1P.isClosed_pieces_run w D hRLω ℓ).1
  obtain ⟨g, hgc, hgi, ⟨C₁, C₂, -, hprop⟩, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hPR := pieceRegular_of_launch hRLω hl
  have hα := isGeneratingTrace_trOf hPR
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 → 0 ≤ (trOf (D ℓ) t).im := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hval : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 → pcPt s (D ℓ) t = g (trOf (D ℓ) t) := fun t ht =>
    bdVal_eq_of_tendsto (hαH t ht) (hgt _ (hαH t ht))
  have hg0 : g 0 = stRecR s := by
    have h1 := GW1WalkFinish.boundary_limit_of_exteriorRecord (GW1WalkFinish.hasBdryLimits_chart_run w D hP ℓ) hX.1
    have h2 := hgt 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp)
    have : (𝓝[H] (0 : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ (0 : ℂ).im by simp)
    rw [tendsto_nhds_unique h2 h1, hpt]
  have hrec : ∀ x : ℝ, stRecR s < x → g ((stChart s).1 x) = x := fun x hx => by
    have hmem : (0 : ℝ) ≤ ((stChart s).1 (x : ℂ)).im := by rw [hRP.1 x]
    have : (𝓝[H] ((stChart s).1 (x : ℂ))).NeBot := GW1P.neBot_nhdsWithin_H hmem
    have h1 : g ((stChart s).1 (x : ℂ)) = extendFrom H (stChart s).2.1 ((stChart s).1 (x : ℂ)) :=
      ((hgt _ hmem).limUnder_eq).symm
    rw [h1]
    exact hext x hx
  have hnd : stStatus s ≠ GW1Conn.stDone := by
    obtain ⟨⟨c₀, θ₀⟩, hc₀⟩ := Option.ne_none_iff_exists'.1 hl
    exact WalkIntRunChron.not_done_of_launch _ _ hc₀
  have hfree : ∀ x : ℝ, stRecR s < x → ∃ r > 0, ∀ z ∈ H, dist z (x : ℂ) < r → z ∈ (stChart s).2.1 '' H := by
    intro x hx
    rw [Lk.image_runChart_walk_eq hRLω (fin_of_later_launch hl)]
    have hpc : IsCompact (SB.prefixPhysSet κ b jumps w D ℓ) := Lx.isCompact_prefixPhysSet_run w D hP ℓ hnd
    obtain ⟨ρ, hρ, hd⟩ := ball_disjoint_fillH_right hpc fun y hy => lt_of_le_of_lt (by
      have := hB y hy
      simpa [GW1WalkFinish.sideCoord, GW1WalkExit.outwardRecord] using this) hx
    exact ⟨ρ, hρ, fun z hz hdz => ⟨hz, fun hzF => Set.disjoint_left.1 hd (mem_ball.2 hdz) hzF⟩⟩
  obtain ⟨h1, h2⟩ := phys_facts hκ hb hRP hO hseed hleft hcc hgc hgi hprop hg0 hrec hfree hαH havoid hmark hval
  exact ⟨hpt, record_notMem_closure hb hRP hO hseed, h1, fun htop => h2 htop (htip htop)⟩

end Ae

end InteractingSLE.Theorem14.SB.Ne

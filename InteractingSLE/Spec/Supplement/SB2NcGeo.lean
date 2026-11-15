/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcHull
import InteractingSLE.Spec.Supplement.SBS3DuMain
import InteractingSLE.Spec.Supplement.SB2QtBaseLaw

/-!
# F2b′'s retained hull: the geometry of the retained union at a launch

Packet PROVE-AUX61-NOJUMP (round 21, D34, component A). **`ae_retGeom`**: almost surely at a launch of B's stage `ℓ`,
the retained union `X = A ∪ B_{<ℓ}` (the upper prefix with B's physical prefix before `ℓ`) is compact, lies in `ℍ̄`,
and `X ∪ {im ≤ 0}` is preconnected; so `fill X` is a hull (`isHPHull_fillH_of_isPreconnected`), and the filled version
of the two stage sets (the set `A₁ 0` of F2b′'s line family) is `fill X`. The walk inputs are PROVE-R6-CORNER's
(`Dv.sb2LowerStageDrivenStatement_of_thm12_thm13`): pinch-invariant walk prefixes (`LuM.pinv_prefix_walk`) and the
upper prefix as a path image from `0` (`Lf.exists_path_upperPrefix`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf Supp8.Q3Stop WalkSide

/-- **The retained union at the start of B's stage `ℓ`**: the upper prefix and B's physical prefix before `ℓ`. -/
def retX {Ω : Type*} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (ω : Ω) : Set ℂ :=
  upperPrefix κ b jumps E u l k ω ∪
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The geometry of the retained union at a launch of B's stage `ℓ`.** -/
theorem ae_retGeom (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      IsCompact (retX κ b jumps E u l k ℓ ω) ∧ (∀ z ∈ retX κ b jumps E u l k ℓ ω, 0 ≤ z.im) ∧
      IsPreconnected (retX κ b jumps E u l k ℓ ω ∪ Restart.lowerHalf) ∧
      IsHPHull (fillH (retX κ b jumps E u l k ℓ ω)) ∧
      fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          ℓ ω) ω = fillH (retX κ b jumps E u l k ℓ ω) := by
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hT := GW1WalkFinish.walkTipCoordinatesStatement_of_d4 h13 hD4
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  set su := Lu.upperSpec u l with hsudef
  have hsu := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hRu := hER _ hsu
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Ew := StagedReg.regFam E w with hEwdef
  have hEw := hE' w hwbc
  have hregw := hreg' w
  have hRw : StagedPiecesRegular κ b jumps P w Ew := stagedPiecesRegular_of_regular h13 hκ hb hEw hregw
  have hTip := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg' true
  have hInj := ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk hκ hκ4 hb hEw hregw hRw j
  filter_upwards [hTip, hInj, GW1W.regLaunches_of_stagedPiecesRegular hRw,
    GW1W.regLaunches_of_stagedPiecesRegular (hER w hwbc), hrun w hwbc, hrun su hsu, hRu]
    with ω htipω hinjω hRLω hRLEω hrunω hrunuω hRuω hl
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set Dw : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => Ew i ω with hDw
  set Du : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E su i ω with hDu
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus (ExplState.run κ b jumps w D ℓ) ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  -- the walk prefix: pinch invariant and compact
  have hpre : SB.prefixPhysSet κ b jumps w D ℓ = SB.prefixPhysSet κ b jumps w Dw ℓ := by
    unfold SB.prefixPhysSet; rw [hrunω ℓ]
  have hnd' : stStatus (ExplState.run κ b jumps w Dw ℓ) ≠ GW1Conn.stDone := by rw [hrunω ℓ]; exact hnd
  have hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps w D ℓ) := by
    have h1 := (LuM.pinv_prefix_walk hRLω hinjω htipω le_rfl ℓ hnd').1
    have h0 : ((↑) : ℝ → ℂ) '' Icc 0 0 ⊆ SB.prefixPhysSet κ b jumps w Dw ℓ := by
      rw [Icc_self, image_singleton, singleton_subset_iff]
      exact WalkIntRunChron.prefixPhysSet_mono w Dw (Nat.zero_le ℓ)
        (show ((0 : ℝ) : ℂ) ∈ SB.prefixPhysSet κ b jumps w Dw 0 from
          Or.inl (Or.inl (by simp [hw, boundaryWalkSpec])))
    rw [union_eq_left.2 h0] at h1
    rw [hpre]; exact h1
  have hPc : IsCompact (SB.prefixPhysSet κ b jumps w D ℓ) := Lx.isCompact_prefixPhysSet_run w D hRLEω ℓ hnd
  have hPfacts : (∀ z ∈ SB.prefixPhysSet κ b jumps w D ℓ, 0 ≤ z.im) ∧
      IsPreconnected (SB.prefixPhysSet κ b jumps w D ℓ) ∧ (0 : ℂ) ∈ SB.prefixPhysSet κ b jumps w D ℓ := by
    rcases hpinv with h1 | ⟨p, hp⟩
    · rw [h1]
      refine ⟨fun z hz => ?_, isPreconnected_singleton, by simp⟩
      rw [mem_singleton_iff.1 hz]; simp
    · obtain ⟨hpc, hp0, -, hpH, hpA⟩ := hp
      refine ⟨?_, ?_, ?_⟩
      · rw [← hpA]; rintro _ ⟨s, hs, rfl⟩; exact hpH s hs
      · rw [← hpA]; exact isPreconnected_Icc.image _ hpc
      · rw [← hpA]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0]; simp⟩
  -- the upper prefix as a path image from `0`
  have hreg₀ : ∀ (i : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (Lf.sspec u l) Du (i + 1)).2.2.2.1 i = some (c', θ') →
      GW1P.PieceRegular (Du i).1 (min (instrTime (Lf.sspec u l) i) (Du i).2) :=
    fun i c' θ' hl'' => hRuω i θ' _ c' (eq_launch_of_launches _ _ hl'').1 hl''
  obtain ⟨pA, hp, hp0, hpH, hpA, -⟩ := Lf.exists_path_upperPrefix hu l Du hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω := hpA
  have hAc : IsCompact (upperPrefix κ b jumps E u l k ω) := hpA' ▸ isCompact_Icc.image_of_continuousOn hp
  have hAH : ∀ z ∈ upperPrefix κ b jumps E u l k ω, 0 ≤ z.im := by
    rw [← hpA']; rintro _ ⟨s, hs, rfl⟩; exact hpH s hs
  have hAp : IsPreconnected (upperPrefix κ b jumps E u l k ω ∪ Restart.lowerHalf) := by
    rw [← hpA']; exact Dv.isPreconnected_path_union_lower hp hp0
  -- the union
  have hXc : IsCompact (retX κ b jumps E u l k ℓ ω) := hAc.union hPc
  have hXH : ∀ z ∈ retX κ b jumps E u l k ℓ ω, 0 ≤ z.im := by
    rintro z (hz | hz)
    · exact hAH z hz
    · exact hPfacts.1 z hz
  have hPl : IsPreconnected (SB.prefixPhysSet κ b jumps w D ℓ ∪ Restart.lowerHalf) :=
    hPfacts.2.1.union 0 hPfacts.2.2 (show (0 : ℂ).im ≤ 0 by simp) isPreconnected_lowerHalf
  have hXp : IsPreconnected (retX κ b jumps E u l k ℓ ω ∪ Restart.lowerHalf) := by
    have e : retX κ b jumps E u l k ℓ ω ∪ Restart.lowerHalf =
        (upperPrefix κ b jumps E u l k ω ∪ Restart.lowerHalf) ∪
          (SB.prefixPhysSet κ b jumps w D ℓ ∪ Restart.lowerHalf) := by
      unfold retX; ext z; simp only [mem_union]; tauto
    rw [e]
    exact hAp.union (-Complex.I) (Or.inr (by show (-Complex.I).im ≤ 0; simp))
      (Or.inr (by show (-Complex.I).im ≤ 0; simp)) hPl
  have hhull : IsHPHull (fillH (retX κ b jumps E u l k ℓ ω)) :=
    isHPHull_fillH_of_isPreconnected hXc.isBounded hXp
  refine ⟨hXc, hXH, hXp, hhull, ?_⟩
  -- the filled version of the stage sets
  have hS : WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) Ew ℓ ω =
      retX κ b jumps E u l k ℓ ω ∩ H := by
    rw [WalkInf.stageSet_capSpec_of_le hℓ.le ω le_rfl, Qt.stageSet_eq_prefixPhysSet_inter_H,
      Qt.stageSet_eq_prefixPhysSet_inter_H]
    have hpu : SB.prefixPhysSet κ b jumps su (fun j => StagedReg.regFam E su j ω) k =
        SB.prefixPhysSet κ b jumps su Du k := by unfold SB.prefixPhysSet; rw [hrunuω k]
    have hpw : SB.prefixPhysSet κ b jumps w (fun j => Ew j ω) ℓ = SB.prefixPhysSet κ b jumps w D ℓ := hpre.symm
    rw [hpu, hpw]
    ext z
    simp only [retX, upperPrefix, mem_union, mem_inter_iff, mem_image]
    constructor
    · rintro (⟨hz, hzH⟩ | ⟨hz, hzH⟩)
      · exact ⟨Or.inl (Or.inl hz), hzH⟩
      · exact ⟨Or.inr hz, hzH⟩
    · rintro ⟨(hz | ⟨x, -, rfl⟩) | hz, hzH⟩
      · exact Or.inl ⟨hz, hzH⟩
      · exact absurd hzH (by show ¬ 0 < ((x : ℝ) : ℂ).im; simp)
      · exact Or.inr ⟨hz, hzH⟩
  have hbd : Bornology.IsBounded ((fun ω => WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) Ew ℓ ω) ω) := by
    show Bornology.IsBounded (_ ∪ _)
    rw [hS]; exact hXc.isBounded.subset inter_subset_left
  rw [fillVer_of_bounded (B := fun ω => WalkLaw.stageSet κ b jumps su (StagedReg.regFam E su) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) Ew ℓ ω) hbd]
  show fillH (closure (_ ∪ _)) = _
  rw [hS, Mo.fillH_closure_inter_H]

end

end InteractingSLE.Theorem14.SB.Nc

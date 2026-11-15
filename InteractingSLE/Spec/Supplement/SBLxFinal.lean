/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxSucc

/-!
# SB3's induction: from the stage claims to the whole walk

Packet PROVE-T14-SBLEAVES3 (second round). `ae_sb3_of_claims`: the claim at the last stage and the truncation claims
give SB3's conclusion for every proper parametrization of the completed lower walk ("The induction gives S1 for every
finite actual prefix of the proper lower walk"). If every launched piece is finite, the whole walk is the last
retained prefix. Otherwise the first infinite piece finishes the walk; a compact subarc of the walk meets that piece
only in a finite truncation (the piece's trace is transient and the chart's boundary map is proper), so the truncation
claim applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lx

open Lv Lw Sec4 Exist.Staged Exist.StagedLaw

/-- The chosen trace is transient wherever a transient generating trace exists. -/
theorem tendsto_chosenTrace {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hex : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
      (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) :
    ζ ω = ⊤ → Tendsto (fun t => ‖GW2aSingle.chosenTrace W ζ ω t‖) atTop atTop := by
  unfold GW2aSingle.chosenTrace
  split_ifs
  exact hex.choose_spec.2

/-- A generating trace of infinite lifetime stays in `ℍ̄`. -/
theorem im_nonneg_of_isGeneratingTrace_top {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤}) (hw0 : w 0 = 0) (t : ℝ≥0) : 0 ≤ (η t).im := by
  have h := Restart.IsGeneratingTrace.mem_closure_self hη hw hw0 (t := t) ENNReal.coe_lt_top
  have h2 : η t ∈ closure H := closure_mono sdiff_subset h
  rw [closure_H] at h2
  exact h2

/-- **From the stage claims to the whole walk.** Almost surely, if the claim holds at the last stage and the
truncation claims hold at every stage, then S1 holds for every compact subarc of every proper parametrization of the
completed lower walk (with the bridge) and every available upper stop. -/
theorem ae_sb3_of_claims {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hreg : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hN : ∀ᵐ ω ∂P, SB3StageClaim κ b jumps E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length u η ζ ω)
    (hT : ∀ᵐ ω ∂P, ∀ j, SB3TruncClaim κ b jumps E j u η ζ ω) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ → γ 0 = 0 → range γ = lowerWalkSet κ b jumps E ω →
      ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a := by
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec_def
  set N := spec.2.2.length with hN_def
  filter_upwards [hreg, hN, hT] with ω hregω hNω hTω
  intro γ hγ _ hrange s a ha
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => E spec j ω with hD
  have hW : lowerWalkSet κ b jumps E ω = SB.prefixPhysSet κ b jumps spec D N := rfl
  have hγs : γ '' Icc 0 s ⊆ SB.prefixPhysSet κ b jumps spec D N := by
    rw [← hW, ← hrange]; exact image_subset_range _ _
  by_cases hlive : LowerLive κ b jumps E N ω
  · refine (hNω hlive a ha).mono ?_
    unfold lowerPrefix
    exact union_subset_union hγs subset_rfl
  -- the first infinite piece
  classical
  have hex : ∃ j, j < N ∧ LowerLaunch κ b jumps E j ω ∧ (E spec j ω).2 = ⊤ := by
    unfold LowerLive at hlive
    push Not at hlive
    obtain ⟨j, hj, hl, htop⟩ := hlive
    exact ⟨j, hj, hl, htop⟩
  set j := Nat.find hex with hj_def
  obtain ⟨hjN, hlj, htopj⟩ := Nat.find_spec hex
  have hlivej : LowerLive κ b jumps E j ω := fun i hi hli htopi =>
    Nat.find_min hex hi ⟨hi.trans hjN, hli, htopi⟩
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlj
  change (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) at hcθ
  obtain ⟨-, -, hc_eq⟩ := eq_launch_of_launches spec D hcθ
  have hregrun : ∀ (i : ℕ) (c' : Chart) (θ' : ℝ), (ExplState.run κ b jumps spec D (i + 1)).2.2.2.1 i =
      some (c', θ') → GW1P.PieceRegular (D i).1 (min (instrTime spec i) (D i).2) := by
    intro i c' θ' hi
    obtain ⟨hii, -, -⟩ := eq_launch_of_launches spec D hi
    exact hregω i θ' _ c' hii hi
  have hcc : c.IsConformal := by
    rw [hc_eq]; exact (GW2aCont.isConformal_runChart spec D j fun i _ => hregrun i).1
  have hcb : GW1P.HasProperBdryExt c := by
    rw [hc_eq]; exact (GW1P.isClosed_pieces_run spec D hregrun j).1
  obtain ⟨g, hgc, hgi, ⟨C₁, C₂, hC₁, hprop⟩, -⟩ := exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hgi' : EqOn g (stChart (ExplState.run κ b jumps spec D j)).2.1 H := by
    rw [show stChart (ExplState.run κ b jumps spec D j) = c from hc_eq.symm]; exact hgi
  -- the infinite piece
  obtain ⟨hi, -, -⟩ := eq_launch_of_launches spec D hcθ
  rw [instrTime_boundaryWalk_of_launch hcθ] at hi
  obtain ⟨hW0, hWc, γ', hγ', hγt'⟩ := hregω j θ ⊤ c hi hcθ
  rw [min_top_left] at hWc hγ' hγt'
  set α := GW2aSingle.chosenTrace (fun t ω => (E spec j ω).1 t) (fun ω => (E spec j ω).2) ω with hα_def
  have hgen : IsGeneratingTrace (E spec j ω).1 (E spec j ω).2 α :=
    isGeneratingTrace_chosenTrace (W := fun t ω => (E spec j ω).1 t) (ζ := fun ω => (E spec j ω).2)
      (ω := ω) ⟨γ', hγ', hγt'⟩
  have htr : Tendsto (fun t => ‖α t‖) atTop atTop :=
    tendsto_chosenTrace (W := fun t ω => (E spec j ω).1 t) (ζ := fun ω => (E spec j ω).2) (ω := ω)
      ⟨γ', hγ', hγt'⟩ htopj
  have hgen' : IsGeneratingTrace (E spec j ω).1 ⊤ α := by rw [← htopj]; exact hgen
  have hαH : ∀ t : ℝ≥0, 0 ≤ (α t).im := im_nonneg_of_isGeneratingTrace_top hgen'
    (hWc.mono fun t _ => by show (t : ℝ≥0∞) ≤ (E spec j ω).2; rw [htopj]; exact le_top) hW0
  have hphys := prefixPhysSet_succ_eq_image (κ := κ) (b := b) (jumps := jumps) (θ := -(Real.pi / 2))
    (right := true) D (k := j) (by rw [hcθ]; exact Option.some_ne_none _) hgc hgi' hgen hWc hW0
    (fun t _ => hαH t)
  have hdone := stStatus_run_succ_of_launch_top spec D hcθ (instrTime_boundaryWalk_of_launch hcθ) htopj
  have hNj : SB.prefixPhysSet κ b jumps spec D N = SB.prefixPhysSet κ b jumps spec D (j + 1) := by
    unfold SB.prefixPhysSet
    rw [run_eq_of_done spec D hdone N (by omega)]
  -- a compact subarc meets the infinite piece in a finite truncation
  obtain ⟨R, hR⟩ := (isCompact_Icc.image hγ.1).isBounded.exists_norm_le
  obtain ⟨T, hT'⟩ := eventually_atTop.1 (htr.eventually (eventually_gt_atTop (C₁ * R + C₂)))
  have hsub : γ '' Icc 0 s ⊆ SB.prefixPhysSet κ b jumps spec D j ∪ g '' (α '' Icc 0 T) := by
    intro z hz
    have hz' := hγs hz
    rw [hNj, hphys] at hz'
    rcases hz' with hz' | ⟨_, ⟨t, -, rfl⟩, hzt⟩
    · exact Or.inl hz'
    · refine Or.inr ⟨α t, ⟨t, ⟨zero_le, ?_⟩, rfl⟩, hzt⟩
      by_contra hlt
      have h1 := hT' t (le_of_lt (not_le.1 hlt))
      have h2 := hprop (α t) (hαH t)
      have h3 : ‖z‖ ≤ R := hR z hz
      rw [← hzt] at h3
      nlinarith
  have htrunc := hTω j hlivej hlj T a (by rw [htopj]; exact le_top) ha
  have hlws : lowerWalkState κ b jumps E j ω = ExplState.run κ b jumps spec D j := rfl
  rw [pieceTrunc_eq_image hgc (by rw [hlws]; exact hgi') (fun t _ => hαH t)] at htrunc
  refine htrunc.mono ?_
  unfold lowerPrefix
  intro z hz
  rcases hz with hz | hz
  · rcases hsub hz with hz' | hz'
    · exact Or.inl (Or.inl hz')
    · exact Or.inr hz'
  · exact Or.inl (Or.inr hz)

/-- **The truncation claim at the first stage** (the first piece is the original-field flow line; SB1/S6). -/
theorem ae_truncClaim_zero (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    {u ψ : ℝ} (hu : u ≤ 0) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps u ψ P h η ζ) (hζ : ∀ᵐ ω ∂P, 0 < ζ ω)
    (hC0 : ∀ᵐ ω ∂P, SB3StageClaim κ b jumps E 0 u η ζ ω) :
    ∀ᵐ ω ∂P, SB3TruncClaim κ b jumps E 0 u η ζ ω := by
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec_def
  have hspec : IsBoundaryContinuedProgram spec.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨rest, hp⟩ := boundaryWalkSpec_prog_eq b jumps (-(Real.pi / 2)) true
  have hfl := (hE spec hspec).isFlowLineDriver_first hκ hb hh rfl hp
  have hα := Sec7.StripWall.isFlowLine_of_isFlowLineDriver hfl
    ((GW2aSingle.ae_chosenTrace h13 hκ hfl).mono fun _ hω => hω.1)
  have hgi : ∀ ω, EqOn (fun z : ℂ => z) (stChart (lowerWalkState κ b jumps E 0 ω)).2.1 H := fun ω w _ => by
    simp [lowerWalkState, stChart, ExplState.run, ExplState.init, Chart.recenter, Chart.id, boundaryWalkSpec]
  have h0mem : ∀ ω, (0 : ℂ) ∈ lowerPrefix κ b jumps E 0 u ω := fun ω =>
    Or.inr ⟨0, ⟨hu, le_rfl⟩, by simp⟩
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hα with h0 | hpos
  · filter_upwards [hC0, h0, ae_flowLine_regular h13 hκ hα] with ω hCω h0ω hαω
    intro hlive _ d a hd ha
    have hd0 : d = 0 := by
      have : (d : ℝ≥0∞) ≤ 0 := by rw [← h0ω]; exact hd
      exact_mod_cast le_antisymm this zero_le
    subst hd0
    rw [pieceTrunc_eq_image continuousOn_id (hgi ω) (fun t ht => hαω.2.2.1 t (by
      rw [h0ω]; exact_mod_cast ht))]
    refine (hCω hlive a ha).mono ?_
    rintro z (hz | ⟨_, ⟨t, ht, rfl⟩, rfl⟩)
    · exact hz
    · have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst ht0
      rw [hαω.2.1]
      exact h0mem ω
  · have hbase := Erase.ae_isOneSided_base_of_hybrid hSB1 hS6 hκ hκ4 hb hh hu hψ hL hH hα hη
      (hpos.mono fun _ hω => pos_iff_ne_zero.2 hω) hζ
    filter_upwards [hbase, ae_flowLine_regular h13 hκ hα] with ω hbω hαω
    intro _ _ d a hd ha
    rw [pieceTrunc_eq_image continuousOn_id (hgi ω) (fun t ht => hαω.2.2.1 t
      ((ENNReal.coe_le_coe.2 ht).trans hd)), image_id]
    refine (hbω d a hd ha).mono ?_
    unfold lowerPrefix
    rw [prefixPhysSet_zero]
    rintro z ((hz | hz) | hz)
    · refine Or.inr ⟨0, ⟨hu, le_rfl⟩, ?_⟩
      rw [hz]; simp [boundaryWalkSpec]
    · exact Or.inr hz
    · exact Or.inl hz

/-- **The claim before any instruction**: the upper flow's prefixes have proper completions with the bridge on their
right (the source: "the upper flow can be completed on its left"). -/
theorem stageClaim_zero_of_completion {Ω : Type u} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hu : u ≤ 0) (hcomp : ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a) :
    SB3StageClaim κ b jumps E 0 u η ζ ω := by
  intro _ a ha
  refine (hcomp a ha).mono ?_
  unfold lowerPrefix
  rw [prefixPhysSet_zero]
  rintro z (hz | hz)
  · refine ⟨0, ⟨hu, le_rfl⟩, ?_⟩
    rw [hz]; simp [boundaryWalkSpec]
  · exact hz

/-- **SB3's stage induction** (specification p. 633–634), at one setting, from SB2(1) in entry form at launch
samples, SB1, S6, Theorem 1.3 and the named inputs:
* `hcomp`: the upper flow's prefixes have proper completions (S1 for the bridge alone);
* `hpath`: every retained prefix after the first stage is the image of a path with finite fibres;
* `hadd`: the walk's connectors and zero-lifetime pieces add only real points `≥ 0` (right records);
* `hmeas`, `hmeasT`: the claim events are null-measurable (the S1 events are universally measurable, p. 577).
The lower walk's drivers are regular at every sample (use `StagedReg.regFam`). -/
theorem ae_sb3_of_inputs (hSB2 : SB2UpperLaunchEntryLStatement.{u}) (hSB1 : SB1Statement.{u})
    (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    (hEreg : ∀ j ω, IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω))
    {u ψ : ℝ} (hu : u ≤ 0) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps u ψ P h η ζ) (hζ : ∀ᵐ ω ∂P, 0 < ζ ω)
    (hcomp : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a)
    (hpath : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω →
      ∃ p : ℝ → ℂ, IsPrefixPath p u (lowerPrefix κ b jumps E k u ω))
    (hadd : ∀ᵐ ω ∂P, WalkRightAdds κ b jumps E ω)
    (hmeas : ∀ k, NullMeasurableSet {ω | SB3StageClaim κ b jumps E k u η ζ ω} P)
    (hmeasT : ∀ k, NullMeasurableSet {ω | SB3TruncClaim κ b jumps E k u η ζ ω} P) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ → γ 0 = 0 → range γ = lowerWalkSet κ b jumps E ω →
      ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a := by
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hC0 : ∀ᵐ ω ∂P, SB3StageClaim κ b jumps E 0 u η ζ ω :=
    hcomp.mono fun _ hω => stageClaim_zero_of_completion hu hω
  have hclaims : ∀ k, (∀ᵐ ω ∂P, SB3StageClaim κ b jumps E (k + 1) u η ζ ω) ∧
      ∀ᵐ ω ∂P, SB3TruncClaim κ b jumps E k u η ζ ω := by
    intro k
    induction k with
    | zero =>
      exact ⟨ae_stageClaim_one hSB1 hS6 h13 hκ hκ4 hb hh hE hreg hu hψ hL hH hη hζ hadd hC0,
        ae_truncClaim_zero hSB1 hS6 h13 hκ hκ4 hb hh hE hu hψ hL hH hη hζ hC0⟩
    | succ k ih =>
      exact ae_stageClaim_succ hSB2 hSB1 hS6 h13 hκ hκ4 hb hh hE hreg hEreg (k + 1) hu hψ hL hH hη
        (hpath (k + 1) (Nat.succ_pos k)) hadd (hmeas (k + 1 + 1)) (hmeasT (k + 1)) ih.1
  have hall : ∀ k, ∀ᵐ ω ∂P, SB3StageClaim κ b jumps E k u η ζ ω := fun k => by
    cases k with
    | zero => exact hC0
    | succ k => exact (hclaims k).1
  exact ae_sb3_of_claims (hreg _ hspec) (hall _) (ae_all_iff.2 fun j => (hclaims j).2)

end InteractingSLE.Theorem14.SB.Lx

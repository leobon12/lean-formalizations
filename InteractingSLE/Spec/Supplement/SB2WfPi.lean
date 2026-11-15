/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfPs
import InteractingSLE.Spec.Supplement.SB2WfJt
import InteractingSLE.Spec.Supplement.SB2WeInd
import InteractingSLE.Spec.Supplement.GB7aCmpPath
import InteractingSLE.Spec.Supplement.GW1LawsWitness

/-!
# The junction invariant at every launch of the lower walk

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). Round 2's witness induction
(`GW1W.exists_witness_right_lwo`) rerun carrying the junction invariant `JW` as well:
**`exists_witness_right_lwoj`**. The step is `jw_walk_step`; its trace inputs are the chosen trace of the launched
piece (`stage_trace_*`) and its touch inputs come from the almost sure avoidance of the forbidden set
(`ae_stage_avoid`, `hRT_of_avoid`, `hLT_of_avoid`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

universe u

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W LQGMetric
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-! ### The trace inputs of a stage -/

section Trace

variable {e : (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem rtime_recOf_top (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : rtime (recOf ⊤ e) = ((e.2.toNNReal : ℝ≥0) : ℝ) := by
  rw [rtime_recOf_coe, min_eq_right le_top]

theorem lt_of_lt_rtime (hfin : e.2 ≠ ⊤) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ < rtime (recOf ⊤ e)) :
    ((t₀.toNNReal : ℝ≥0) : ℝ≥0∞) < e.2 := by
  rw [rtime_recOf_top] at ht
  rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_lt_coe]
  exact (Real.toNNReal_lt_iff_lt_coe ht₀).2 ht

theorem stage_trace_lt (he : IsRegularDriver e) (hP : GW1P.PieceRegular e.1 e.2)
    (hgood : e.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ e))) (hfin : e.2 ≠ ⊤) :
    IsLoewnerTraceLT (rdrv (recOf ⊤ e)) (rtime (recOf ⊤ e)) (fun s : ℝ => LuM.trOf e s.toNNReal) := by
  rw [rtime_recOf_top]
  refine GB7a.isLoewnerTraceLT_of_agree (LuM.isGeneratingTrace_trOf hP) ENNReal.coe_toNNReal_le_self
    fun s _ hsT => ?_
  refine rdrv_recOf_eq he (hgood hfin) (min_top_ne_top hfin) ?_
  rw [rtime_recOf_top]
  exact hsT.le

theorem stage_trace_cont (hP : GW1P.PieceRegular e.1 e.2) (hfin : e.2 ≠ ⊤) :
    ContinuousOn (fun s : ℝ => LuM.trOf e s.toNNReal) (Icc 0 (rtime (recOf ⊤ e))) := by
  refine (LuM.isGeneratingTrace_trOf hP).2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
  show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e.2
  rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe]
  rw [rtime_recOf_top] at hs
  exact Real.toNNReal_le_iff_le_coe.2 hs.2

theorem pos_of_rtime_pos (h : 0 < rtime (recOf ⊤ e)) : 0 < e.2 := by
  rw [rtime_recOf_top] at h
  rw [pos_iff_ne_zero]
  intro h0
  rw [h0] at h
  simp at h

theorem stage_avoid_real {κ θ : ℝ} {c : BoundaryWord} (hfin : e.2 ≠ ⊤)
    (hav : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → LuM.trOf e t ∉ forb κ θ c) :
    ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < rtime (recOf ⊤ e) → (fun s : ℝ => LuM.trOf e s.toNNReal) t₀ ∉ forb κ θ c :=
  fun _ ht₀ ht => hav _ (lt_of_lt_rtime hfin ht₀ ht)

end Trace

/-! ### The induction -/

section Induction

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Round 2's classification with the junction invariant** (`exists_witness_right_lwo` and `JW`). -/
theorem exists_witness_right_lwoj (hκ : 0 < κ) (hκ4 : κ < 4) {ψ u : ℝ} (hθψ : θ < ψ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hRS : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps θ true) E)
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + θ * chiC κ < sleLambda κ) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ true) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
          none →
        RInv κ θ b jumps (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) ∧
        RReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) ∧
        (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) = .inl () →
          leftLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k)) +
            θ * chiC κ < sleLambda κ) ∧
        LWO κ θ b jumps (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) ∧
        JW κ θ ψ u b (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hRL := regLaunches_of_stagedPiecesRegular hRS
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => flowField spec.1 0 (h ω),
        isStageWitness_zero hh hc₀J hc₀, Eventually.of_forall fun ω _ => ?_⟩
      have h0 := rInv_root (κ := κ) (θ := θ) hb hamb hc₀J hc₀
      exact ⟨h0.1, h0.2.1, fun _ => h0.2.2, lwo_root hc₀, jw_root hκ hκ4 hθψ hc₀⟩
    have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ β Y ∧
        ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          RInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
            leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ) ∧
          LWO κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          JW κ θ ψ u b (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, hW, hI⟩ := ih ℓ hℓ
        exact ⟨β, Y, fun _ => ⟨hW, hI⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
    choose β Y hWI using H
    obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
      hk (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y fun ℓ hℓ => (hWI ℓ hℓ).1
    refine ⟨βk, Yk, hWk, ?_⟩
    have hstage : ∀ ℓ, ℓ < k → ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some false) ∧
          ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
            rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ ≤
              -sleLambda κ) := fun ℓ hℓ =>
      ae_stage_right hκ hb hh hE hreg (hWI ℓ hℓ).1 ((hWI ℓ hℓ).2.mono fun ω hω hl => (hω hl).1)
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          RInv κ θ b jumps (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
            leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ) ∧
          LWO κ θ b jumps (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          JW κ θ ψ u b (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) ∧
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some false) ∧
          ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
            rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ ≤
              -sleLambda κ)) ∧
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          (0 < (E ℓ ω).2 → SeedOK κ θ (β ℓ ω)) ∧
            ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E ℓ ω).2 → LuM.trOf (E ℓ ω) t ∉ forb κ θ (β ℓ ω)) := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · filter_upwards [(hWI ℓ hℓ).2, hstage ℓ hℓ, ae_stage_avoid hκ hκ4 hb hh hE hreg hRS (hWI ℓ hℓ).1]
          with ω h1 h2 h3 _ using ⟨h1, h2, h3⟩
      · exact Eventually.of_forall fun ω h' => absurd h' hℓ
    filter_upwards [hall, hRL] with ω hω hRLω hlk
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ'', hl'⟩, -, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
    have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hl']; simp
    obtain ⟨hinv, hst, hav⟩ := hω ℓ hℓk
    obtain ⟨hI, hR, hroot, hLW, hJW⟩ := hinv hl
    obtain ⟨hnoL, hgood, hF2⟩ := hst hl
    obtain ⟨hsd, havd⟩ := hav hl
    obtain ⟨hInv, hReady, ha⟩ := rInv_walk_step (D := fun j => E j ω) hκ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω)
      hgood hnoL hF2
    have hcc := SB.LuM.isConformal_runChart_of_reg spec hRLω ℓ
    have hPr : GW1P.PieceRegular (E ℓ ω).1 (E ℓ ω).2 := by
      have := hRLω ℓ c' θ'' hl'
      rwa [instrTime_walk hl, min_eq_right le_top] at this
    have hP : (E ℓ ω).2 ≠ ⊤ → GW1P.PieceRegular (E ℓ ω).1 (E ℓ ω).2 := fun _ => hPr
    obtain ⟨g, hgc, hgi, -, -⟩ := SB.Lw.exists_bdryMap_of_hasProperBdryExt hcc
      (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hRLω ℓ).1
    have hLWk := lwo_walk_step (D := fun j => E j ω) hκ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω) hgood hnoL hF2
      hLW.1 hcc hP hLW.2.1 hLW.2.2 hgc hgi
    have hJWk := jw_walk_step (u := u) (D := fun j => E j ω) hκ hκ4 hθψ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω)
      hgood hnoL hLW.1 hcc hLW.2.1 hgc hgi hJW (GW1Laws.zero_le_stRecR_run κ b jumps spec _ le_rfl ℓ)
      (GW1Laws.zero_le_stRecR_run κ b jumps spec _ le_rfl (ℓ + 1))
      (γ := fun s : ℝ => LuM.trOf (E ℓ ω) s.toNNReal) (stage_trace_lt (hreg ℓ ω) hPr hgood)
      (stage_trace_cont hPr) (fun _ hpos => hsd (pos_of_rtime_pos hpos))
      (fun hfin => hRT_of_avoid (stage_avoid_real hfin havd))
      (fun hfin => hLT_of_avoid (stage_avoid_real hfin havd))
    have hβ := hexpl ℓ ω hℓk hlk hl hn
    rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl, ← ha] at hβ
    rw [hβ]
    refine ⟨hInv, hReady, fun hroot' => ?_, hLWk, hJWk⟩
    obtain ⟨-, -, r, hr⟩ := run_eq_of_last_launch (D := fun j => E j ω) hℓk hlk hl hn
    rw [hr] at hroot'
    exact absurd hroot' (by simp [stArcM])

end Induction

end InteractingSLE.Theorem14.SB.Wf

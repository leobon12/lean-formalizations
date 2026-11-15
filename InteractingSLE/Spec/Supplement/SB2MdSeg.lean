/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2McFill
import InteractingSLE.Spec.Supplement.WalkIntRunChronRun
import InteractingSLE.Spec.Supplement.WalkIntChronoHistory
import InteractingSLE.Spec.Supplement.WalkIntRunChronPrefixArc
import InteractingSLE.Spec.Supplement.SB2LgChain

/-!
# The prefixes are walk segments: GW1's chronological arc histories

Packet PROVE-T14-SB2LIFT (round 18; the preconnectedness in `IsWalkSeg`, handoff §R17.2 1). GW1's chain construction
(`GW1WalkChain`, `WalkIntRunChron`) carries every prefix of the walk before it is done by a chronological arc history
from the root (`ArcHistory`). The inputs are GW1's per-step facts `WalkChainFacts` (piece simplicity at the launches,
connector clearance). PROVE-SB2-LIFTSET proved them almost surely under the retained kernel for the actual lower walk
(`sb2LowerChainStatement_of_thm12_thm13`). Hence:

* `isWalkSeg_of_arcHistory`: an arc history from `0` inside the walk and containing `β₀ t_L` is a walk segment
  (`WalkIntChrono.arcHistory_compact_preconnected_seed`);
* **`arcHistory_prefix_of_chain`**: the prefix at every stage before done has an arc history ending at the current
  point (`WalkIntRunChron.stateRepresented_run`);
* `stStatus_launch_ne_done`: a launch with a finite lifetime does not finish the walk;
* **`isWalkSeg_prefix_succ_of_chain`**: the prefix after a finite launch is a walk segment;
* **`arcHistory_partPrefix_of_chain`**, **`isWalkSeg_partPrefix_of_chain`**: the prefix with the new piece up to a time
  `r ≤` its stop has an arc history (`WalkIntRunChron.arcHistory_append_finite_tipSet`), hence is a walk segment;
* `bdVal_trace_subset_tip`: the new piece up to a time of the piece lies in its tip set;
* **`sb2LowerWalkSegInputs`**: almost surely under the retained kernel of every retained launch (SB2(2)'s setting), the
  inputs of these lemmas (`WalkChainFacts`, regular launches) hold for the actual lower walk (Theorems 1.2–1.3, both
  universes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkChain GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **An arc history from `0` inside the walk and containing `β₀ t_L` is a walk segment.** -/
theorem isWalkSeg_of_arcHistory {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} {A : Set ℂ} {q : ℂ} (h : ArcHistory (0 : ℂ) A q)
    (hr : A ⊆ range β₀) (hβ0 : β₀ 0 = 0) (hL : β₀ tL ∈ A) : IsWalkSeg β₀ tL A := by
  obtain ⟨hc, hp, h0⟩ := WalkIntChrono.arcHistory_compact_preconnected_seed h
  exact ⟨hc, hp, hr, by rw [hβ0]; exact h0, hL⟩

/-- **The prefix before done has an arc history from the root to the current point.** -/
theorem arcHistory_prefix_of_chain {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hW : WalkChainFacts κ b jumps θ D) (n : ℕ)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone) :
    ArcHistory (0 : ℂ) (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℂ) := by
  rcases WalkIntRunChron.stateRepresented_run hW.1 hW.2 n with ⟨hd, _⟩ | ⟨_, hh⟩
  · exact absurd hd hst
  · exact hh

/-- A launch with a finite lifetime does not finish the walk. -/
theorem stStatus_launch_ne_done {s : ExplState} {k : ℕ} {d : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ' : ℝ} (hfin : d.2 ≠ ⊤) :
    stStatus (ExplState.launch s k d θ' ⊤) ≠ stDone := by
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top s k d θ' ⊤ (min_top_ne_top hfin)
  rw [hst]
  have hnlt : ¬ (⊤ : ℝ≥0∞) < d.2 := not_lt.2 le_top
  unfold lStatus
  simp only [hnlt, ↓reduceIte]
  split_ifs
  · split <;> (intro h; cases h)
  all_goals (intro h; cases h)

/-- **The prefix after a launch with a finite lifetime is a walk segment** (within the program). -/
theorem isWalkSeg_prefix_succ_of_chain {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hn : n + 1 ≤ (boundaryWalkSpec b jumps θ true).2.2.length) {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) (hβ0 : β₀ 0 = 0)
    (hL : β₀ tL ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) :
    IsWalkSeg β₀ tL (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) := by
  have hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) ≠ stDone := by
    obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl
    rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
    rw [he]
    exact stStatus_launch_ne_done hfin
  refine isWalkSeg_of_arcHistory (arcHistory_prefix_of_chain hW (n + 1) hst) ?_ hβ0 hL
  rw [hβr, ← SB.prefixPhysSet_length]
  exact WalkIntRunChron.prefixPhysSet_mono _ D hn

/-- **The prefix with the new piece up to a time of the piece has an arc history.** -/
theorem arcHistory_partPrefix_of_chain {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) {r : ℝ} (hr0 : 0 ≤ r) (hrT : r ≤ stopTime ⊤ (D n)) :
    ∃ q : ℂ, ArcHistory (0 : ℂ) (partPrefix κ b jumps θ D n r) q := by
  have hst := WalkIntRunChron.not_done_of_launch _ D hl
  have hHist := arcHistory_prefix_of_chain hW n hst
  have hpiece := hW.1 n c θ' hl hHist.endpoint_mem
  have hlne : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none := by
    rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl, min_top_left] at hpiece
  have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 := by
    obtain ⟨-, -, htime⟩ := stopDrv_eq_and_isGeneratingTrace hPR hfin
    rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
    rw [htime] at hrT
    exact hrT
  obtain ⟨f, α, C, hf, -⟩ := id hpiece
  have hf' : ∀ p ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1
      (𝓝[H] p) (𝓝 (f p)) := fun p hp => by
    have h1 := hf p hp
    rw [hc] at h1
    exact h1
  obtain ⟨q, hq⟩ := WalkIntRunChron.arcHistory_append_finite_tipSet hHist hpiece hrle
  refine ⟨q, ?_⟩
  -- the tip set up to `r` is the boundary image of the trace up to `r`
  have hα := isGeneratingTrace_trOf hPR
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → trOf (D n) t ∈ Hbar := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hgen := isGeneratingTrace_mono hα hrle
  have hWr : ContinuousOn (D n).1 {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ((r.toNNReal : ℝ≥0) : ℝ≥0∞)} :=
    hPR.2.1.mono fun _ ht => le_trans ht hrle
  have hset : c.tipSet (fun r' : ℝ≥0 => (D n).1 (min (r' : ℝ≥0∞) ((r.toNNReal : ℝ≥0) : ℝ≥0∞)).toNNReal)
      (r.toNNReal : ℝ≥0) =
      bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ''
        (trOf (D n) '' Icc 0 r.toNNReal) := by
    rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hgen hWr hPR.1
      (fun t ht => hf _ (hαH t (le_trans ht hrle)))]
    have hIcc : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ((r.toNNReal : ℝ≥0) : ℝ≥0∞)} = Icc 0 r.toNNReal := by
      ext t
      simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and, ENNReal.coe_le_coe]
    rw [hIcc]
    refine (image_congr fun p hp => ?_).symm
    obtain ⟨t, ht, rfl⟩ := hp
    have htD : (t : ℝ≥0∞) ≤ (D n).2 := le_trans (ENNReal.coe_le_coe.2 ht.2) hrle
    exact bdVal_eq_of_tendsto (hαH t htD) (hf' _ (hαH t htD))
  unfold partPrefix
  rw [← hset]
  exact hq

/-- **The new piece up to a time of the piece lies in the piece's tip set.** -/
theorem bdVal_trace_subset_tip {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) {r : ℝ} (hr0 : 0 ≤ r) (hrT : r ≤ stopTime ⊤ (D n)) :
    bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ''
        (trOf (D n) '' Icc 0 r.toNNReal) ⊆
      c.tipSet (fun r' : ℝ≥0 => (D n).1 (min (r' : ℝ≥0∞)
          (min (instrTime (boundaryWalkSpec b jumps θ true) n) (D n).2)).toNNReal)
        (min (instrTime (boundaryWalkSpec b jumps θ true) n) (D n).2) := by
  have hlne : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none := by
    rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl, min_top_left]
  obtain ⟨hbe, -⟩ := GW1P.isClosed_pieces_run _ D hP n
  obtain ⟨ĝ, C, hf, -⟩ := hbe
  have hfc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p)) := fun p hp => by
    rw [hc]
    exact hf p hp
  have hα := isGeneratingTrace_trOf hPR
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → trOf (D n) t ∈ Hbar := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 := by
    obtain ⟨-, -, htime⟩ := stopDrv_eq_and_isGeneratingTrace hPR hfin
    rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
    rw [htime] at hrT
    exact hrT
  rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hPR.2.1 hPR.1 (fun t ht => hfc _ (hαH t ht))]
  rintro _ ⟨p, ⟨t, ht, rfl⟩, rfl⟩
  have htD : (t : ℝ≥0∞) ≤ (D n).2 := le_trans (ENNReal.coe_le_coe.2 ht.2) hrle
  exact ⟨trOf (D n) t, ⟨t, htD, rfl⟩, (bdVal_eq_of_tendsto (hαH t htD) (hf _ (hαH t htD))).symm⟩

/-- **The prefix with the new piece up to a time of the piece is a walk segment.** -/
theorem isWalkSeg_partPrefix_of_chain {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hn : n + 1 ≤ (boundaryWalkSpec b jumps θ true).2.2.length) {r : ℝ} (hr0 : 0 ≤ r)
    (hrT : r ≤ stopTime ⊤ (D n)) {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) (hβ0 : β₀ 0 = 0)
    (hL : β₀ tL ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) :
    IsWalkSeg β₀ tL (partPrefix κ b jumps θ D n r) := by
  obtain ⟨q, hq⟩ := arcHistory_partPrefix_of_chain hP hW hl hfin hr0 hrT
  have hsub : partPrefix κ b jumps θ D n r ⊆ range β₀ := by
    rw [hβr, ← SB.prefixPhysSet_length]
    refine (union_subset (WalkIntRunChron.prefixPhysSet_mono _ D (by omega : n ≤ _)) ?_)
    exact (bdVal_trace_subset_tip hP hl hfin hr0 hrT).trans
      ((GW1Z.tipSet_subset_prefixPhysSet_succ _ D hl).trans (WalkIntRunChron.prefixPhysSet_mono _ D hn))
  exact isWalkSeg_of_arcHistory hq hsub hβ0 (Or.inl hL)

/-- **The inputs of the walk-segment lemmas, almost surely under the retained kernel** (SB2(2)'s setting): GW1's
per-step facts of the actual lower walk (`sb2LowerChainStatement_of_thm12_thm13`, PROVE-SB2-LIFTSET) and its regular
launches (`StagedPiecesRegular`). -/
theorem sb2LowerWalkSegInputs (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀),
        WalkChainFacts κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ∧
        RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := by
  have hC := sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hlwp : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  filter_upwards [hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 (hER _ hlwp)] with ω₀ h₀ hr₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [h₀ c θ hlaunch b' J' h' hb' hT' hG', hr₀] with ω hω hr
  exact ⟨hω, fun j c' θ' hl' => hr j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'⟩

end InteractingSLE.Theorem14.SB.Lk

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxBase
import InteractingSLE.Spec.Supplement.KernelTower
import InteractingSLE.Spec.Supplement.SB3ProofMeas
import InteractingSLE.Spec.Exist.StagedLawPast

/-!
# SB3's induction step

Packet PROVE-T14-SBLEAVES3 (second round). `ae_stageClaim_succ`: the claim at stage `k` gives the claim at stage
`k + 1` (specification p. 633: "Retain this lower prefix `A` through `w`, and fix one clipped available upper stop [...]
S5 pulls this comparison back. [...] Repeat over its finite stages"). Under the walk's retained kernel at stage `k`
(the past is frozen, `Exist.StagedLaw.ae_ae_run_eq`):

* no launch at `k`, or a launched piece of zero lifetime: the stage adds real points `≥ 0` (`WalkRightAdds`);
* a launched piece of positive lifetime: SB2(1) in entry form at launch samples, SB1/S6 and S5's stage step
  (`ae_isOneSided_stage`) with the walk's launch chart and the physical identity (`prefixPhysSet_succ_eq_image`).

The kernel statement is lifted to `P` by the null-measurability of the claim event (`hmeas`; the S1 events are
universally measurable, supplement p. 577), via `SB.ae_of_ae_condExpKernel_of_nullMeasurableSet`. The retained
prefix is represented by a path with finite fibres (`IsPrefixPath`, input `hpath`).
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

/-- A path of a retained prefix from the upper seed: continuous, with finite fibres, in `ℍ̄`, with image `A`. -/
def IsPrefixPath (p : ℝ → ℂ) (u : ℝ) (A : Set ℂ) : Prop :=
  ContinuousOn p (Icc 0 1) ∧ p 0 = u ∧ (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧ p '' Icc 0 1 = A

/-- The physical piece of stage `k` truncated at time `d`: the launch chart's boundary values on the chosen trace of the
staged driver over `[0, d]` (canonical: the boundary values are limits of the chart's inverse from `ℍ`). -/
def PieceTrunc {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (d : ℝ≥0) (ω : Ω) : Set ℂ :=
  (fun z => limUnder (𝓝[H] z) (stChart (lowerWalkState κ b jumps E k ω)).2.1) ''
    (GW2aSingle.chosenTrace (fun t ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).1 t)
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2) ω '' Icc 0 d)

/-- **The truncation claim at stage `k`**: at a live launch, S1 holds for the retained prefix with every available
truncation of the new piece (used for a piece of infinite lifetime, the last one of the walk). -/
def SB3TruncClaim {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  LowerLive κ b jumps E k ω → LowerLaunch κ b jumps E k ω →
    ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2 → (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (lowerPrefix κ b jumps E k u ω ∪ PieceTrunc κ b jumps E k d ω) (η ω) a

/-- The truncated piece through a boundary map of the chart. -/
theorem pieceTrunc_eq_image {Ω : Type u} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {d : ℝ≥0} {ω : Ω} {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart (lowerWalkState κ b jumps E k ω)).2.1 H)
    (hαH : ∀ t : ℝ≥0, t ≤ d → 0 ≤ (GW2aSingle.chosenTrace
      (fun t ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).1 t)
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2) ω t).im) :
    PieceTrunc κ b jumps E k d ω = g '' (GW2aSingle.chosenTrace
      (fun t ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).1 t)
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2) ω '' Icc 0 d) := by
  unfold PieceTrunc
  refine image_congr fun z hz => ?_
  obtain ⟨t, ht, rfl⟩ := hz
  have hv := hαH t ht.2
  have := GW1P.neBot_nhdsWithin_H (show _ ∈ Hbar from hv)
  exact (tendsto_inv_of_bdryMap hgc hgi hv).limUnder_eq

/-- **SB3's induction step under the retained kernel at stage `k`**: the next claim and the truncation claim. -/
theorem ae_ae_stage (hSB2 : SB2UpperLaunchEntryLStatement.{u}) (hSB1 : SB1Statement.{u})
    (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    (hEreg : ∀ j ω, IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω))
    (k : ℕ) {u ψ : ℝ} (hu : u ≤ 0) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps u ψ P h η ζ)
    (hpath : ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω → ∃ p : ℝ → ℂ, IsPrefixPath p u (lowerPrefix κ b jumps E k u ω))
    (hadd : ∀ᵐ ω ∂P, WalkRightAdds κ b jumps E ω)
    (hC : ∀ᵐ ω ∂P, SB3StageClaim κ b jumps E k u η ζ ω) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
      SB3StageClaim κ b jumps E (k + 1) u η ζ ω ∧ SB3TruncClaim κ b jumps E k u η ζ ω := by
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec_def
  have hspec : IsBoundaryContinuedProgram spec.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hEm : ∀ j, Measurable (E spec j) := (hE spec hspec).1
  have h𝒢 : pastSigma κ b jumps spec (E spec) k ≤ mΩ := by
    rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hEreg j) k le_rfl).comap_le
  have hrun := ae_ae_run_eq (κ := κ) (k := k) (P := P) runMeasStatement hb spec (fun j _ => hEm j)
    (fun j _ => hEreg j)
  have hS1L : ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a :=
    hC.mono fun _ hω hl => hω (lowerLive_of_launch hl)
  have hord := ae_hasRelStageOrderingE_of_L hSB2 hSB1 hS6 h13 hκ hκ4 hb hh hE hreg k hu hψ hL hH hη hS1L
  have hηreg := ae_flowLine_regular h13 hκ hη
  have hregS := hreg spec hspec
  have tC := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hC
  have tadd := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hadd
  have tη := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hηreg
  have treg := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hregS
  filter_upwards [hrun, hord, hpath, hregS, tC, tadd, tη, treg] with ω₀ hrun₀ hord₀ hpath₀ hreg₀ tC₀ tadd₀ tη₀ treg₀
  -- the launch at stage `k` is decided by the frozen past
  have hlaunch_eq : ∀ ω, ExplState.run κ b jumps spec (fun j => E spec j ω) k =
      ExplState.run κ b jumps spec (fun j => E spec j ω₀) k →
      (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.1 k =
        (ExplState.run κ b jumps spec (fun j => E spec j ω₀) (k + 1)).2.2.2.1 k :=
    fun ω hω => congrFun (launches_run_succ_of_run_eq spec hω) k
  by_cases hl₀ : LowerLaunch κ b jumps E k ω₀
  swap
  · filter_upwards [hrun₀, tC₀, tadd₀, tη₀] with ω hrunω hCω haddω hηω
    have hlω : ¬ LowerLaunch κ b jumps E k ω := by
      unfold LowerLaunch lowerWalkState at hl₀ ⊢
      rw [hlaunch_eq ω hrunω]
      exact hl₀
    exact ⟨stageClaim_succ_of_adds hu hηω.2.1 hCω (haddω k (Or.inl hlω)), fun _ hl => absurd hl hlω⟩
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl₀
  have hR := hord₀ c θ hcθ
  obtain ⟨p, hp⟩ := hpath₀ hl₀
  set D₀ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => E spec j ω₀ with hD₀
  -- the launch chart at `ω₀`
  obtain ⟨-, -, hc_eq⟩ := eq_launch_of_launches spec D₀ hcθ
  have hregrun : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ), (ExplState.run κ b jumps spec D₀ (j + 1)).2.2.2.1 j =
      some (c', θ') → GW1P.PieceRegular (D₀ j).1 (min (instrTime spec j) (D₀ j).2) := by
    intro j c' θ' hj
    obtain ⟨hi, -, -⟩ := eq_launch_of_launches spec D₀ hj
    exact hreg₀ j θ' _ c' hi hj
  have hnot : stStatus (ExplState.run κ b jumps spec D₀ k) ≠ GW1Conn.stDone := fun hd =>
    hl₀ (launches_eq_none_of_done spec D₀ hd le_rfl)
  have hcc : c.IsConformal := by
    rw [hc_eq]; exact (GW2aCont.isConformal_runChart spec D₀ k fun j _ => hregrun j).1
  have hcb : GW1P.HasProperBdryExt c := by
    rw [hc_eq]; exact (GW1P.isClosed_pieces_run spec D₀ hregrun k).1
  obtain ⟨g, hgc, hgi, -, -⟩ := exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hpA : fillH (p '' Icc 0 1) = fillH (SB.prefixPhysSet κ b jumps spec D₀ k) := by
    rw [hp.2.2.2.2]; exact fillH_union_real _ _
  have hc : ∀ m : ℝ, IsLeftEntryValue c (realMin (p '' Icc 0 1)) m →
      IsLeftEntryChart ((fun z => z - (u : ℂ)) '' (p '' Icc 0 1)) (realMin (p '' Icc 0 1) - u)
        (shiftChart c u m) := fun m hm => by
    rw [hc_eq] at hm ⊢
    exact isLeftEntryChart_shift_of_runChart_entry spec D₀ hregrun k hnot
      (isCompact_Icc.image_of_continuousOn hp.1) hpA (fun _ hy => realMin_le_of_mem_path hp.1 hy) hm u
  rw [← hp.2.2.2.2] at hR
  have hRc := hR
  obtain ⟨b', jumps', h', m, ηr, ζr, -, -, -, -, -, hα, -⟩ := hRc
  -- facts at the samples of the retained kernel
  have hpre : ∀ ω, ExplState.run κ b jumps spec (fun j => E spec j ω) k = ExplState.run κ b jumps spec D₀ k →
      lowerPrefix κ b jumps E k u ω = p '' Icc 0 1 := fun ω hω => by
    rw [hp.2.2.2.2]; exact lowerPrefix_eq_of_run_eq hω
  have hlaunchω : ∀ ω, ExplState.run κ b jumps spec (fun j => E spec j ω) k = ExplState.run κ b jumps spec D₀ k →
      (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.1 k = some (c, θ) := fun ω hω => by
    rw [hlaunch_eq ω hω]; exact hcθ
  have hlω' : ∀ ω, ExplState.run κ b jumps spec (fun j => E spec j ω) k = ExplState.run κ b jumps spec D₀ k →
      LowerLaunch κ b jumps E k ω := fun ω hω => by
    unfold LowerLaunch lowerWalkState
    rw [hlaunchω ω hω]; exact Option.some_ne_none _
  have hgiω : ∀ ω, ExplState.run κ b jumps spec (fun j => E spec j ω) k = ExplState.run κ b jumps spec D₀ k →
      EqOn g (stChart (ExplState.run κ b jumps spec (fun j => E spec j ω) k)).2.1 H := fun ω hω => by
    have hcω := (eq_launch_of_launches spec (fun j => E spec j ω) (hlaunchω ω hω)).2.2
    rw [show stChart (ExplState.run κ b jumps spec (fun j => E spec j ω) k) = c from hcω.symm]; exact hgi
  -- the physical identity at a sample of the kernel
  have hphysω : ∀ ω, ExplState.run κ b jumps spec (fun j => E spec j ω) k = ExplState.run κ b jumps spec D₀ k →
      (E spec k ω).1 0 = 0 → ContinuousOn (E spec k ω).1 {s | (s : ℝ≥0∞) ≤ (E spec k ω).2} →
      IsGeneratingTrace (E spec k ω).1 (E spec k ω).2
        (GW2aSingle.chosenTrace (fun t ω => (E spec k ω).1 t) (fun ω => (E spec k ω).2) ω) →
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ (E spec k ω).2 →
        0 ≤ (GW2aSingle.chosenTrace (fun t ω => (E spec k ω).1 t) (fun ω => (E spec k ω).2) ω s).im) →
      SB.prefixPhysSet κ b jumps spec (fun j => E spec j ω) (k + 1) =
        SB.prefixPhysSet κ b jumps spec (fun j => E spec j ω) k ∪
          g '' (GW2aSingle.chosenTrace (fun t ω => (E spec k ω).1 t) (fun ω => (E spec k ω).2) ω ''
            {t | (t : ℝ≥0∞) ≤ (E spec k ω).2}) := fun ω hω hW0 hWc hgen hαH =>
    prefixPhysSet_succ_eq_image (κ := κ) (b := b) (jumps := jumps) (θ := -(Real.pi / 2))
      (right := true) (fun j => E spec j ω) (k := k) (by rw [hlaunchω ω hω]; exact Option.some_ne_none _)
      hgc (hgiω ω hω) hgen hWc hW0 hαH
  -- the regular data of the new piece at a sample of the kernel
  have hpieceω : ∀ ω, ExplState.run κ b jumps spec (fun j => E spec j ω) k = ExplState.run κ b jumps spec D₀ k →
      (∀ (j : ℕ) (θ' : ℝ) (t : ℝ≥0∞) (c' : Chart), spec.2.2[j]? = some (Sum.inl (θ', t)) →
        (ExplState.run κ b jumps spec (fun j => E spec j ω) (j + 1)).2.2.2.1 j = some (c', θ') →
        (E spec j ω).1 0 = 0 ∧ ContinuousOn (E spec j ω).1 {s | (s : ℝ≥0∞) ≤ min t (E spec j ω).2} ∧
          ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E spec j ω).1 (min t (E spec j ω).2) η ∧
            (min t (E spec j ω).2 = ⊤ → Tendsto (fun s => ‖η s‖) atTop atTop)) →
      (E spec k ω).1 0 = 0 ∧ ContinuousOn (E spec k ω).1 {s | (s : ℝ≥0∞) ≤ (E spec k ω).2} ∧
        IsGeneratingTrace (E spec k ω).1 (E spec k ω).2
          (GW2aSingle.chosenTrace (fun t ω => (E spec k ω).1 t) (fun ω => (E spec k ω).2) ω) := by
    intro ω hω hregω
    have hcθω := hlaunchω ω hω
    obtain ⟨hi, -, -⟩ := eq_launch_of_launches spec (fun j => E spec j ω) hcθω
    rw [instrTime_boundaryWalk_of_launch hcθω] at hi
    obtain ⟨hW0, hWc, γ, hγ, hγt⟩ := hregω k θ ⊤ c hi hcθω
    rw [min_top_left] at hWc hγ hγt
    exact ⟨hW0, hWc, isGeneratingTrace_chosenTrace (W := fun t ω => (E spec k ω).1 t)
      (ζ := fun ω => (E spec k ω).2) (ω := ω) ⟨γ, hγ, hγt⟩⟩
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hα with h0 | hpos
  · filter_upwards [hrun₀, tC₀, tadd₀, tη₀, h0, treg₀, ae_flowLine_regular h13 hκ hα]
      with ω hrunω hCω haddω hηω h0ω hregω hαω
    refine ⟨stageClaim_succ_of_adds hu hηω.2.1 hCω (haddω k (Or.inr h0ω)), ?_⟩
    intro hlive _ d a hd ha
    obtain ⟨hW0, hWc, hgen⟩ := hpieceω ω hrunω hregω
    have hphys := hphysω ω hrunω hW0 hWc hgen hαω.2.2.1
    have hd' : (d : ℝ≥0∞) ≤ (E spec k ω).2 := hd
    have hsub : PieceTrunc κ b jumps E k d ω ⊆
        SB.prefixPhysSet κ b jumps spec (fun j => E spec j ω) k ∪ ((↑) : ℝ → ℂ) '' Ici 0 := by
      rw [pieceTrunc_eq_image hgc (hgiω ω hrunω)
        (fun t ht => hαω.2.2.1 t ((ENNReal.coe_le_coe.2 ht).trans hd'))]
      intro z hz
      apply haddω k (Or.inr h0ω)
      rw [hphys]
      obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hz
      exact Or.inr ⟨_, ⟨t, (ENNReal.coe_le_coe.2 ht.2).trans hd', rfl⟩, rfl⟩
    have h1 := (hCω hlive a ha).union_right_real (T := Ici 0) (by rw [hηω.2.1]; simp)
      (fun x hx => by rw [hηω.2.1, Complex.ofReal_re]; exact hu.trans hx)
    refine h1.mono ?_
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · rcases hsub hz with hz' | hz'
      · exact Or.inl (Or.inl hz')
      · exact Or.inr hz'
  have hLQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω₀),
      realMin (lowerPrefix κ b jumps E k u ω) = realMin (p '' Icc 0 1) := by
    filter_upwards [hrun₀] with ω hω
    rw [hpre ω hω]
  have hηQ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω₀),
      ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} ∧ η ω 0 = u := by
    filter_upwards [tη₀] with ω hω using ⟨hω.1, hω.2.1⟩
  have hS1Q : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω₀),
      ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (p '' Icc 0 1) (η ω) a := by
    filter_upwards [hrun₀, tC₀] with ω hrunω hCω
    rw [← hpre ω hrunω]
    exact hCω (lowerLive_of_launch (hlω' ω hrunω))
  have hstage := ae_isOneSided_stage h13 hκ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hR hc hgc hgi hLQ hηQ hS1Q
    (hpos.mono fun _ hω => pos_iff_ne_zero.2 hω)
  filter_upwards [hstage, hrun₀, treg₀, ae_flowLine_regular h13 hκ hα] with ω hstω hrunω hregω hαω
  obtain ⟨hW0, hWc, hgen⟩ := hpieceω ω hrunω hregω
  refine ⟨fun hlive a ha => ?_, fun _ _ d a hd ha => ?_⟩
  · have hfin := hlive.ne_top_of_launch (hlω' ω hrunω)
    have hphys := hphysω ω hrunω hW0 hWc hgen hαω.2.2.1
    rw [setOf_coe_le_eq_Icc hfin] at hphys
    refine (hstω _ a ENNReal.coe_toNNReal_le_self ha).mono ?_
    rw [← hpre ω hrunω]
    unfold lowerPrefix
    rw [hphys]
    intro z hz
    rcases hz with (hz | hz) | hz
    · exact Or.inl (Or.inl hz)
    · exact Or.inr hz
    · exact Or.inl (Or.inr hz)
  · have hd' : (d : ℝ≥0∞) ≤ (E spec k ω).2 := hd
    rw [pieceTrunc_eq_image hgc (hgiω ω hrunω)
      (fun t ht => hαω.2.2.1 t ((ENNReal.coe_le_coe.2 ht).trans hd')), hpre ω hrunω]
    exact hstω d a hd' ha

/-- The walk's retained past is a sub-σ-algebra. -/
theorem pastSigma_lowerWalk_le {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (spec : ExplSpec)
    (hEm : ∀ j, Measurable (E j)) (hEreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    pastSigma κ b jumps spec E k ≤ mΩ := by
  rw [pastSigma_eq_comap]
  exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hEreg j) k le_rfl).comap_le

/-- **SB3's induction step** (`ae_ae_stage` lifted to `P` by the null-measurability of the two claim events). -/
theorem ae_stageClaim_succ (hSB2 : SB2UpperLaunchEntryLStatement.{u}) (hSB1 : SB1Statement.{u})
    (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    (hEreg : ∀ j ω, IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω))
    (k : ℕ) {u ψ : ℝ} (hu : u ≤ 0) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps u ψ P h η ζ)
    (hpath : ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω → ∃ p : ℝ → ℂ, IsPrefixPath p u (lowerPrefix κ b jumps E k u ω))
    (hadd : ∀ᵐ ω ∂P, WalkRightAdds κ b jumps E ω)
    (hmeas : NullMeasurableSet {ω | SB3StageClaim κ b jumps E (k + 1) u η ζ ω} P)
    (hmeasT : NullMeasurableSet {ω | SB3TruncClaim κ b jumps E k u η ζ ω} P)
    (hC : ∀ᵐ ω ∂P, SB3StageClaim κ b jumps E k u η ζ ω) :
    (∀ᵐ ω ∂P, SB3StageClaim κ b jumps E (k + 1) u η ζ ω) ∧ ∀ᵐ ω ∂P, SB3TruncClaim κ b jumps E k u η ζ ω := by
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have h𝒢 := pastSigma_lowerWalk_le (κ := κ) hb (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (hE _ hspec).1 hEreg k
  have hK := ae_ae_stage hSB2 hSB1 hS6 h13 hκ hκ4 hb hh hE hreg hEreg k hu hψ hL hH hη hpath hadd hC
  exact ⟨SB.ae_of_ae_condExpKernel_of_nullMeasurableSet h𝒢 hmeas (hK.mono fun _ h => h.mono fun _ h' => h'.1),
    SB.ae_of_ae_condExpKernel_of_nullMeasurableSet h𝒢 hmeasT (hK.mono fun _ h => h.mono fun _ h' => h'.2)⟩

end InteractingSLE.Theorem14.SB.Lx

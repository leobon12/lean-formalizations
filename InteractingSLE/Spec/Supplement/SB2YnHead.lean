/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YlHead
import InteractingSLE.Spec.Supplement.SB2YmSeed
import InteractingSLE.Spec.Supplement.SB2NfNew
import InteractingSLE.Spec.Supplement.SB2MdLift
import InteractingSLE.Spec.Supplement.SB2QxPhys

/-!
# B's piece at `relOff` that dies no later than its entrance at `R` adds nothing to the retained hull

Packet PROVE-T14-SB2LIFT (round 38, decision D89, CANON's handoff R9.2 option (A)). At `relOff = ℓ` off a zero root,
let B's piece at `ℓ` die no later than its entrance at `R = max (A ∩ ℝ)` (`ζ_ℓ ≤ entrR`). Then the piece runs only
up to `R`, which is the head situation of SB2(2)'s base, so B's prefix through `ℓ + 1` lies in `fill A` inside `ℍ`.

* `startPiece_order_le`: the first half of LIFTSET's `Lk.startPiece_order` (piece points before the first visit of
  `β₀ t_L` lie on `β₀ '' [0, t_L)`). Its proof uses only `sh ≤ ζ`, not `sh < ζ`.
* **`prefix_succ_subset_fillH_root`** (deterministic, positive lifetime): the walk's physical part after `ℓ + 1`
  instructions meets `ℍ` only inside `fill A`.
  * Before `ℓ` this is REVIEW-FABLE-T14's `Qu.statePhysicalSet_inter_H_subset_fillH`, since `ℓ ≤ relOff`.
  * `R` is not in the walk before `ℓ`; otherwise the piece starts at `R` and `entrR = 0 < ζ_ℓ`.
  * So `ℓ` is a pure piece entry and the piece visits `R` first at `sh = entrR = ζ_ℓ`.
  * Before `sh` the piece lies on `β₀ '' [0, t_R)`, which is in `hullK A` by Lemma S2 (`Lk.s2HullRight`); at `sh` it
    is at `R`, which is real.
* **`ae_stage_succ_succ_subset`**: almost surely, at a launch at `ℓ`, if `ζ_ℓ = 0` or (an upper launch, `relOff = ℓ`,
  off a zero root, `ζ_ℓ ≤ entrR`), the regularized stage set after `ℓ + 2` instructions lies in the one after `ℓ`
  together with `fill A`. The case `ζ_ℓ = 0` is F3LAW's `Qx.stageSet_succ_succ_eq_of_zero`.

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

namespace InteractingSLE.Theorem14.SB.Sz

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P Lk Ms
  WalkSide

section Det

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The piece before its first visit of `β₀ t_L` runs along `β₀ '' [0, t_L)`**, with `sh ≤ ζ`. -/
theorem startPiece_order_le (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0}
    (hRold : β₀ tL ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {sh : ℝ≥0} (_hsh : pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) sh = β₀ tL)
    (hshmin : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = β₀ tL → sh ≤ t)
    (hshle : (sh : ℝ≥0∞) ≤ (D n).2) :
    ∀ t : ℝ≥0, t < sh → ∀ t' : ℝ≥0,
      β₀ t' = pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t → t' < tL := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  set φ := pcPt s (D n) with hφ
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) _ D hl
  have hpc := continuousOn_pcPt_launch hP hl
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have htipR : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → φ t ∈ range β₀ := fun t ht => by
    rw [hβr]
    exact tipSet_subset_physSet_launch hl (by rw [htip]; exact ⟨t, ht, rfl⟩)
  have hold : statePhysicalSet 0 s ⊆ range β₀ := by
    rw [hβr]; exact statePhysicalSet_subset_physSet hlen.le
  have holdc := (prefix_facts hW.1 hW.2 n).1
  have h0old : β₀ 0 ∈ statePhysicalSet 0 s := by rw [hβ0]; exact Or.inl (Or.inl rfl)
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hseed : φ 0 ∈ statePhysicalSet 0 s := by
    rw [hφ, pcPt_zero_launch hP hW hl hpos]
    exact (prefix_facts hW.1 hW.2 n).2 (stStatus_ne_done_of_launches _ D hl')
  obtain ⟨ts, hts⟩ := htipR 0 (by rw [ENNReal.coe_zero]; exact zero_le)
  have htsL : ts < tL := lt_of_mem_old hβ hold holdc h0old hRold (by rw [hts]; exact hseed)
  have harc : ∀ a t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → φ '' Icc a t ⊆ range β₀ := fun a t ht => by
    rintro _ ⟨x, hx, rfl⟩
    exact htipR x (le_trans (ENNReal.coe_le_coe.2 hx.2) ht)
  have hconn : ∀ a t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → IsPreconnected (φ '' Icc a t) := fun a t ht =>
    isPreconnected_Icc.image _ (hpc.mono fun x hx => le_trans (ENNReal.coe_le_coe.2 hx.2) ht)
  intro t ht t' ht'
  have htle : (t : ℝ≥0∞) ≤ (D n).2 := le_trans (ENNReal.coe_le_coe.2 ht.le) hshle
  by_contra hge
  push Not at hge
  have hsub := Icc_subset_preimage hβ (harc 0 t htle) (hconn 0 t htle)
    (show β₀ ts ∈ φ '' Icc 0 t from by rw [hts]; exact ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩)
    (show β₀ t' ∈ φ '' Icc 0 t from by rw [ht']; exact ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩)
  obtain ⟨x, hx, hxR⟩ := hsub ⟨htsL.le, hge⟩
  have := hshmin x (le_trans (ENNReal.coe_le_coe.2 hx.2) htle) hxR
  exact absurd (lt_of_le_of_lt (le_trans this hx.2) ht) (lt_irrefl _)

/-- **B's prefix through `relOff + 1` lies in `fill A` inside `ℍ`** when the piece at `relOff` (off a zero root, of
positive lifetime) dies no later than its entrance at `R` (deterministic). See the module docstring. -/
theorem prefix_succ_subset_fillH_root (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hX : RunExitData κ b jumps θ D) (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (boundaryWalkSpec b jumps θ true).2.2.length) = stDone)
    {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {A : Set ℂ} {R : ℝ}
    (hK : ∀ tL : ℝ≥0, β₀ tL = R → β₀ '' Icc 0 tL ⊆ hullK A)
    (hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hoff : relOff κ θ b jumps R D = ℓ) (hZ : ¬ ZeroRoot κ θ b jumps R D) (hpos : (D ℓ).2 ≠ 0)
    (hζ : (D ℓ).2 ≤ Ck.entrTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) (D ℓ) R) :
    statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)) ∩ H ⊆ fillH A := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D ℓ with hs
  have hpre := Qu.statePhysicalSet_inter_H_subset_fillH hb hX hP hW hlm hlh hallow hdone hβ hβ0 hβr hK hl
    (le_of_eq hoff.symm)
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hreal : ∀ z : ℂ, z ∈ H → ∀ x : ℝ, z = (x : ℂ) → False := fun z hzH x hx => by
    have : (0 : ℝ) < z.im := hzH
    rw [hx, Complex.ofReal_im] at this
    exact lt_irrefl _ this
  -- `R` is not in the walk before `ℓ`: otherwise the piece starts at `R`
  have hRold : (R : ℂ) ∉ statePhysicalSet 0 s := by
    intro hin
    have hs' := (launch_seed_of_not_zeroRoot hb hX hP hW hlm hlh hallow hdone hRphys hZ).2
    rw [hoff] at hs'
    have hpt := hs' hin
    have h0 : pcPt s (D ℓ) 0 = (R : ℂ) := by rw [pcPt_zero_launch hP hW hl hpos, hpt]
    have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 ∧ pcPt s (D ℓ) t = (R : ℂ) :=
      ⟨0, by rw [ENNReal.coe_zero]; exact zero_le, h0⟩
    obtain ⟨-, -, hmin⟩ := visitTime_spec hP hl hvis
    have hv0 : visitTime s (D ℓ) R = 0 := le_antisymm (hmin 0 (by rw [ENNReal.coe_zero]; exact zero_le) h0) zero_le
    rw [Ck.entrTime_eq_visitTime hvis, hv0, ENNReal.coe_zero] at hζ
    exact hpos (le_antisymm hζ zero_le)
  -- so `ℓ` is a pure piece entry, and the piece visits `R`
  have hex := exists_mem_statePhysicalSet_succ (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hRphys
  have hA : ¬ ArcEntry κ θ b jumps R D := by
    intro hArc
    have hM : MarkEntry κ θ b jumps R D := by
      by_contra hM
      exact hZ ⟨hArc, hM⟩
    have ho := relOff_of_mark (κ := κ) (θ := θ) (b₁ := b) (J₁ := jumps) hM
    have he := (startOff_eq κ θ b jumps R D).1 hArc
    have hent := (entryStage_spec κ θ b jumps hex).1
    apply hRold
    rw [hs, ← hoff, ho]
    rw [← he] at hent
    exact hent
  have h0 : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps w D 0) := fun h0 =>
    hRold (statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) (Nat.zero_le _) h0)
  obtain ⟨-, -, hmem⟩ := piece_launch hex hA h0
  have hM : ¬ MarkEntry κ θ b jumps R D := fun h => hA h.1
  have ho := relOff_of_not_mark (κ := κ) (θ := θ) (b₁ := b) (J₁ := jumps) hM
  have hoff' : startOff κ θ b jumps R D = ℓ := ho.symm.trans hoff
  rw [hoff'] at hmem
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  rw [htip] at hmem
  obtain ⟨t₀, ht₀, hR₀⟩ := hmem
  have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 ∧ pcPt s (D ℓ) t = (R : ℂ) := ⟨t₀, ht₀, hR₀⟩
  obtain ⟨hshL, hsh, hshmin⟩ := visitTime_spec hP hl hvis
  have hζsh : (D ℓ).2 = (visitTime s (D ℓ) R : ℝ≥0∞) :=
    le_antisymm (by rw [← Ck.entrTime_eq_visitTime hvis]; exact hζ) hshL
  obtain ⟨tR, htR⟩ : ∃ tR, β₀ tR = R := by
    rw [← hβr] at hRphys
    exact hRphys
  have hord := startPiece_order_le hP hW hl hpos hβ hβ0 hβr (tL := tR) (by rw [htR]; exact hRold)
    (hsh.trans htR.symm) (fun t ht h => hshmin t ht (h.trans htR)) hshL
  -- the new piece
  intro z hz
  obtain ⟨hz, hzH⟩ := hz
  have hz' : z ∈ SB.prefixPhysSet κ b jumps w D (ℓ + 1) := hz
  rw [prefixPhysSet_succ_of_launch hl', htip] at hz'
  rcases hz' with hz1 | ⟨t, ht, rfl⟩
  · exact hpre ⟨hz1, hzH⟩
  · have hR' : pcPt s (D ℓ) t ∈ range β₀ := by
      rw [hβr]; exact tipSet_subset_physSet_launch hl (by rw [htip]; exact ⟨t, ht, rfl⟩)
    obtain ⟨t', ht'⟩ := hR'
    have htsh : t ≤ visitTime s (D ℓ) R := by
      have h1 : (t : ℝ≥0∞) ≤ (visitTime s (D ℓ) R : ℝ≥0∞) := le_trans ht hζsh.le
      exact_mod_cast h1
    rcases lt_or_eq_of_le htsh with htl | hte
    · have h1 := hord t htl t' ht'
      rcases hK tR htR ⟨t', ⟨zero_le, h1.le⟩, ht'⟩ with h2 | ⟨x, -, hx⟩
      · exact h2
      · exact (hreal _ hzH x hx.symm).elim
    · rw [hte, hsh] at hzH
      exact (hreal _ hzH R rfl).elim

end Det

section AE

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)}

/-- **The stage set two stages on stays in the old one and `fill A`**, almost surely, at a zero lifetime or at a
piece at `relOff` (off a zero root) dying no later than its entrance at `R`. -/
theorem ae_stage_succ_succ_subset (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 = 0 ∨
        (ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
          relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
          ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≤ Nd.entrR κ b jumps E u l k ℓ ω)) →
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 2) ω ⊆
        WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω ∪
        fillH (upperPrefix κ b jumps E u l k ω) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Er := StagedReg.regFam E w with hEr
  have hSD := GW1WalkExit.walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hE' hreg' true
  have hCo := GW1WalkExit.walkCompletionStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _
    hE' hreg' true
  filter_upwards [Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft, hSD, hCo,
    hrun _ hwbc, Qx.ae_walkChainFacts_regFam h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER]
    with ω hg hSω hdω hrw hWC hlℓ hcase
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  have hl' : (ExplState.run κ b jumps w (fun j => Er j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [hrw]; exact hlℓ
  rcases hcase with h0 | ⟨hup, hoff, hZ, hζ⟩
  · -- lifetime `0`: the stage set does not change
    obtain ⟨old, q₀, q₁, hS⟩ := Qx.pieceSimpleAt_of_chainFacts hWC hl'
    have h0' : (Er ℓ ω).2 = 0 := by rw [hEr, StagedReg.regFam, StagedReg.regHist_snd]; exact h0
    rw [Qx.stageSet_succ_succ_eq_of_zero (κ := κ) (b := b) (jumps := jumps) (E := Er) hl' hS h0']
    exact subset_union_left
  · by_cases hpos : (D ℓ).2 = 0
    · obtain ⟨old, q₀, q₁, hS⟩ := Qx.pieceSimpleAt_of_chainFacts hWC hl'
      have h0' : (Er ℓ ω).2 = 0 := by rw [hEr, StagedReg.regFam, StagedReg.regHist_snd]; exact hpos
      rw [Qx.stageSet_succ_succ_eq_of_zero (κ := κ) (b := b) (jumps := jumps) (E := Er) hl' hS h0']
      exact subset_union_left
    have hgω := hg hup
    have hr' : ∀ n, ExplState.run κ b jumps w D n =
        ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n := fun n => (hrw n).symm
    have hX : RunExitData κ b jumps θ D := runExitData_of_run_eq hr' (runExitData_of_stageData hSω)
    have hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps w D n) := fun n hn => by
      rw [hr' n]
      exact (allowedSt_run hSω n).1 hn
    have hdone : stStatus (ExplState.run κ b jumps w D w.2.2.length) = GW1Conn.stDone := by
      rw [hr']
      exact hdω
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
    have hRphys : ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈ ExplState.physSet κ b jumps w D := by
      obtain ⟨-, tR, htR, -⟩ := s2HullRight hpc hp0 hpH hβ hβ0 hS1'
      rw [hpA] at htR
      rw [← hβr, ← htR]
      exact mem_range_self tR
    have hsub := prefix_succ_subset_fillH_root hb hX hgω.reg hgω.chain hgω.noLeftMove hgω.noLeftHit hallow hdone
      hβ hβ0 hβr hK hRphys hlℓ hoff hZ hpos hζ
    -- the connector at `ℓ + 1` launches nothing
    have hno : WalkLaw.pieceSet κ b jumps w Er (ℓ + 1) ω = ∅ := by
      unfold WalkLaw.pieceSet
      exact ite_eq_left (Qx.walk_noLaunch_succ hl')
    intro z hz
    rw [show ℓ + 2 = ℓ + 1 + 1 from rfl, WalkLaw.stageSet_succ, hno, union_empty,
      Qt.stageSet_eq_prefixPhysSet_inter_H] at hz
    refine Or.inr (hsub ⟨?_, hz.2⟩)
    have hz1 := hz.1
    unfold SB.prefixPhysSet at hz1
    rw [hrw (ℓ + 1)] at hz1
    exact hz1

end AE

end InteractingSLE.Theorem14.SB.Sz

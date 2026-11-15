/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfLaunch
import InteractingSLE.Spec.Supplement.WalkInfLocal
import InteractingSLE.Spec.Supplement.WalkLeafLaunch
import InteractingSLE.Spec.Supplement.WalkPastDet

/-!
# The explored set of ANY staged program is a history-marked local set

Packet PROVE-T14-SB2LCOND (round 2), toward the union kernel of SB2(2)'s relative stages (supplement p. 631: "At
every rational ordinary time of the other history, its marked union with `A` has the Gaussian local-set kernel").
The landed marked locality covers boundary walks (`WalkLeaf.launchLocal_of_thm12_thm13`: instructions with own time
`⊤`) and capped walk prefixes (`WalkInf.launchLocalCap_of_thm12_thm13`). SB2(2)'s retained history `A` is the prefix of
a SCHEDULED program (`upperSpec u l`: angle-`ψ_j` flows for finite own times `t_j`). Here every instruction is
handled:

* an instruction that is not a flow launches nothing;
* a flow for own time `⊤`: `WalkLeaf.launchLocal_of_thm12_thm13`;
* a flow for a finite own time `t`: the program `w = capSpec spec k θ ⊤` (the same prefix, then the same flow for own
  time `⊤`) has the same drivers as a staged history (`WalkSide.isStagedHistory_capSpec`), its pieces are regular by
  Theorem 1.3 (`stagedPiecesRegular_of_regular`), and `capSpec w k θ t` runs exactly as `spec` through instruction
  `k`, so `WalkInf.launchLocalCap_of_thm12_thm13` for `w` at `k` with the cap `t` is the launch locality of `spec`.

Hence **`launchLocal_any_of_thm12_thm13`** (per stage) and **`stageSet_markedLocal_of_thm12_thm13`**: at every number
of instructions the explored set is a history-marked local set of the centred field for the retained past (R58 form:
avoidance events up to null sets), by the landed gluing `WalkInf.markedLocalAE_of_kernel` and the determination of the
retained pasts (`StagedDet.exists_pastMap_eq_comp_field`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lcd

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-! ### The capped program at a finite-time flow instruction runs as the program -/

section Cap

variable {k : ℕ} {θ : ℝ} {t : ℝ≥0}

theorem run_capSpec_capSpec_of_le (hk : k < spec.2.2.length) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ} (hn : n ≤ k) :
    ExplState.run κ b jumps (capSpec (capSpec spec k θ ⊤) k θ t) D n = ExplState.run κ b jumps spec D n := by
  have hwlen : k ≤ (capSpec spec k θ ⊤).2.2.length := by rw [capSpec_length hk.le]; omega
  rw [run_capSpec_of_le hwlen D hn, run_capSpec_of_le hk.le D hn]

theorem run_capSpec_capSpec_succ (hk : k < spec.2.2.length) (hsk : spec.2.2[k]? = some (Sum.inl (θ, (t : ℝ≥0∞))))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b jumps (capSpec (capSpec spec k θ ⊤) k θ t) D (k + 1) =
      ExplState.run κ b jumps spec D (k + 1) := by
  have hwlen : k ≤ (capSpec spec k θ ⊤).2.2.length := by rw [capSpec_length hk.le]; omega
  rw [run_capSpec_succ hwlen D, run_capSpec_of_le hk.le D le_rfl, run_succ, hsk]
  rfl

theorem instrTime_capSpec_capSpec (hk : k < spec.2.2.length)
    (hsk : spec.2.2[k]? = some (Sum.inl (θ, (t : ℝ≥0∞)))) :
    instrTime (capSpec (capSpec spec k θ ⊤) k θ t) k = instrTime spec k := by
  have hwlen : k ≤ (capSpec spec k θ ⊤).2.2.length := by rw [capSpec_length hk.le]; omega
  rw [instrTime_capSpec hwlen]
  simp only [instrTime, hsk]

end Cap

/-! ### Launch locality at every instruction -/

/-- **The launched piece of any staged program is marked local off the explored set** under the stage kernel, for
the marks of its stopped record (every instruction: no flow, a flow for own time `⊤`, or for a finite own time). -/
theorem launchLocal_any_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (u₀ : ℂ → ℝ) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      WalkLaw.IsHistoryAvoidanceLocalOff
        (MeasurableSpace.comap (fun ω => recOf (instrTime spec k) (E k ω)) inferInstance)
        (WalkLaw.stageSet κ b jumps spec E k ω₀) (WalkLaw.pieceSet κ b jumps spec E k)
        (WholeField.centredField h u₀) (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) := by
  classical
  have hR : StagedPiecesRegular κ b jumps P spec E := stagedPiecesRegular_of_regular h13 hκ hb hE hreg
  rcases hsk : spec.2.2[k]? with _ | a
  · refine Eventually.of_forall fun ω₀ hl => absurd ?_ hl
    by_contra hne
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hne
    have := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec _ hcθ).1
    rw [hsk] at this
    simp at this
  rcases a with ⟨θ, t⟩ | a
  swap
  · refine Eventually.of_forall fun ω₀ hl => absurd ?_ hl
    by_contra hne
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hne
    have := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec _ hcθ).1
    rw [hsk] at this
    simp at this
  induction t using ENNReal.recTopCoe with
  | top =>
    refine WalkLeaf.launchLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE hR hreg u₀ k (θ := θ) ?_
    intro θ' t' h'
    rw [hsk] at h'
    simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h'
    exact ⟨h'.1.symm, h'.2.symm⟩
  | coe t =>
    have hk : k < spec.2.2.length := by
      by_contra hk
      rw [List.getElem?_eq_none (by omega)] at hsk
      simp at hsk
    set w := capSpec spec k θ ⊤ with hwdef
    have hw : IsStagedHistory κ b jumps P h w E := isStagedHistory_capSpec hb hE hreg hk hsk
    have hwR : StagedPiecesRegular κ b jumps P w E := stagedPiecesRegular_of_regular h13 hκ hb hw hreg
    have hwlen : k < w.2.2.length := by rw [hwdef, capSpec_length hk.le]; omega
    have hwk : w.2.2[k]? = some (Sum.inl (θ, ⊤)) := capSpec_getElem?_self hk.le
    have hcap := WalkInf.launchLocalCap_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hw hwR hreg u₀ hwlen hwk t
    have hstage : ∀ ω, WalkLaw.stageSet κ b jumps (capSpec w k θ t) E k ω = WalkLaw.stageSet κ b jumps spec E k ω :=
      fun ω => by
        unfold WalkLaw.stageSet
        rw [run_capSpec_capSpec_of_le hk _ le_rfl]
    have hpiece : WalkLaw.pieceSet κ b jumps (capSpec w k θ t) E k = WalkLaw.pieceSet κ b jumps spec E k := by
      funext ω
      unfold WalkLaw.pieceSet
      rw [run_capSpec_capSpec_succ hk hsk, run_capSpec_capSpec_of_le hk _ le_rfl, instrTime_capSpec_capSpec hk hsk]
    have hpast : pastSigma κ b jumps (capSpec w k θ t) E k = pastSigma κ b jumps spec E k := by
      rw [pastSigma_capSpec_of_le hwlen.le E le_rfl, hwdef, pastSigma_capSpec_of_le hk.le E le_rfl]
    filter_upwards [hcap] with ω₀ h1 hl
    have hl' : (ExplState.run κ b jumps (capSpec w k θ t) (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none := by
      rw [run_capSpec_capSpec_succ hk hsk]
      exact hl
    have h2 := h1 hl'
    rw [instrTime_capSpec_capSpec hk hsk, hstage, hpiece, hpast] at h2
    exact h2

/-- **The explored set of any staged program is a history-marked local set** at every number of instructions (R58
form), from Theorems 1.2–1.3. -/
theorem stageSet_markedLocal_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (n : ℕ) :
    (∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[LocalSets.aeSigma (pastSigma κ b jumps spec E n) P]
        {ω | Disjoint (WalkLaw.stageSet κ b jumps spec E n ω) U}) ∧
    (∀ᵐ ω ∂P, IsOpen (H \ WalkLaw.stageSet κ b jumps spec E n ω)) ∧
    WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps spec E n) (WalkLaw.stageSet κ b jumps spec E n)
      (WholeField.centredField h u₀) P := by
  have hR : StagedPiecesRegular κ b jumps P spec E := stagedPiecesRegular_of_regular h13 hκ hb hE hreg
  exact WalkInf.markedLocalAE_of_kernel hb hh hu₀ hE hR hreg
    (fun j => StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hE hR j)
    (fun j => WalkInf.kernelLocal_of_launchLocal hh.1 u₀ hE hreg j
      (launchLocal_any_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE hreg u₀ j)) n

end InteractingSLE.Theorem14.SB.Lcd

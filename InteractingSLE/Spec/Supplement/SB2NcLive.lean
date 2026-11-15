/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcRmax
import InteractingSLE.Spec.Supplement.SBTail2RetainFreeze
import InteractingSLE.Spec.Supplement.WalkStageLocalMeas
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# F2b′'s live event at a tail stage

Packet PROVE-AUX61-NOJUMP (round 21, D34, component A). **`exists_liveEvent`**: at a flow stage `ℓ` of B, an event
`F` of the line σ-algebra at time `0` (`lineSigma0`: the upper past through `k` and B's past capped at its time `0`)
with, almost surely,
`ω ∈ F ↔ (stage event ∧ relOff (max (A ∩ ℝ)) < ℓ ∧ 0 < B's lifetime at ℓ)` (D31's intrinsic characterization).

* The event is a.s. the frozen event `stage ∧ 0 < ζ_ℓ ∧ ∃ o, o + 2 ≤ ℓ ∧ relOffEvent o`
  (`relOffEvent_of_walkGood`: on the walk facts the offset event holds at the offset; `even_of_launch`);
* it is measurable (`exists_measurable_realMax_upper`, `exists_measurableSet_relOffEvent_rand`, the regularized
  launch and cap events) and frozen under the conditional laws given `lineSigma0` (`Retain.ae_ae_run_eq`), hence in
  the completion (`WalkLaw.mem_aeSigma_of_frozen`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf WalkSide Mz GW1Bookkeep GW1Conn Lk LuM
  Sec7.PocketTraversal Sec7.Lemma71C Dv

/-- **An event of `𝓔` is frozen under the conditional laws given `𝓔`.** -/
theorem ae_ae_mem_iff {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝓔 : 𝓔 ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[𝓔] s) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝓔 ω₀), (ω ∈ s ↔ ω₀ ∈ s) := by
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝓔 hs,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝓔 hs.compl] with ω₀ h1 h2
  by_cases h : ω₀ ∈ s
  · filter_upwards [h1 h] with ω hω
    exact iff_of_true hω h
  · filter_upwards [h2 h] with ω hω
    exact iff_of_false hω h

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- B launches only at even stages. -/
theorem even_of_launch {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ℓ % 2 = 0 := by
  have h1 := (flow_of_launch hl).2
  have hget : (boundaryWalkSpec b jumps θ true).2.2[ℓ]? =
      if ℓ < 2 * ((PiecewiseConstantBoundaryData.jumpSet b jumps).card + 1) then
        some (if ℓ % 2 = 0 then (Sum.inl (θ, ⊤) : Instr) else Sum.inr (Sum.inl true)) else none :=
    getElem?_replicate_pair _ _ _ _
  rw [hget] at h1
  by_contra hne
  split_ifs at h1 <;> simp_all

/-- **On the walk facts, the offset event holds at the offset**: `R = max (A ∩ ℝ)` enters the walk by the stage after
its start offset. -/
theorem relOffEvent_of_walkGood {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
    {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω : Ω} (hg : WalkGood κ b jumps E u l k ω) :
    relOffEvent κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
      (relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  obtain ⟨pA, hpc, hp0, hpH, -, hpA⟩ := hg.upath
  obtain ⟨β, hβ, hβ0, hβr, hS1, -⟩ := hg.proper
  set A := upperPrefix κ b jumps E u l k ω with hAdef
  set R := realMax A with hRdef
  have hS1' : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by rw [hpA]; exact hS1
  obtain ⟨-, tR, htR, -⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1'
  rw [hpA] at htR
  have hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps w D := by rw [← hβr, ← htR]; exact mem_range_self tR
  have hex := exists_mem_statePhysicalSet_succ (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hRphys
  obtain ⟨hent, -⟩ := entryStage_spec κ θ b jumps hex
  have hso : startOff κ θ b jumps R D ≤ relOff κ θ b jumps R D := by unfold relOff; split_ifs <;> omega
  have hse : entryStage κ θ b jumps R D ≤ startOff κ θ b jumps R D + 1 := by unfold startOff; omega
  exact ⟨rfl, entryStage κ θ b jumps R D, by omega, hent⟩

section

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **F2b′'s live event at a flow stage.** -/
theorem exists_liveEvent (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hgood : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k → WalkGood κ b jumps E u l k ω) :
    ∃ F : Set Ω, MeasurableSet[lineSigma0 κ b jumps E u l k ℓ] F ∧
      ∀ᵐ ω ∂P, (ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
        0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2)) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set su := Lu.upperSpec u l with hsudef
  set w := boundaryWalkSpec b jumps θ true with hwdef
  have hsu : IsBoundaryContinuedProgram su.2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun'⟩ := StagedReg.regFam_spec hb hE hER
  set Eu := StagedReg.regFam E su with hEudef
  set Ew := StagedReg.regFam E w with hEwdef
  have hEum : ∀ j, Measurable (Eu j) := (hE' su hsu).1
  have hEwm : ∀ j, Measurable (Ew j) := (hE' w hw).1
  -- the σ-algebra
  have hcap := WalkSide.pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps) Ew hℓ.le hwℓ (0 : ℚ≥0)
  rw [NNRat.cast_zero] at hcap
  have h𝒢 : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
    sup_le ((hE' su hsu).2.1 k) (hcap.trans ((hE' w hw).2.1 (ℓ + 1)))
  have hu𝒢 : pastSigma κ b jumps su Eu k ≤ lineSigma0 κ b jumps E u l k ℓ := le_sup_left
  have hwℓ𝒢 : pastSigma κ b jumps w Ew ℓ ≤ lineSigma0 κ b jumps E u l k ℓ := by
    refine le_trans ?_ le_sup_right
    rw [← WalkSide.pastSigma_capSpec_of_le (θ := θ) (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ.le Ew le_rfl]
    exact pastSigma_mono _ _ (Nat.le_succ ℓ)
  -- the measurable pieces
  set LU : Set Ω := {ω | (ExplState.run κ b jumps su (fun j => Eu j ω) (k + 1)).2.2.2.1 k ≠ none} with hLUdef
  have hLU : MeasurableSet[pastSigma κ b jumps su Eu k] LU :=
    Lv.measurableSet_launch_pastSigma (spec := su) hb hEum (hreg' su) k
  set CE : Set Ω := capEvent κ b jumps w Ew ℓ 0 with hCEdef
  have hCE : MeasurableSet[pastSigma κ b jumps (capSpec w ℓ θ ((0 : ℝ≥0) : ℝ≥0∞)) Ew (ℓ + 1)] CE :=
    measurableSet_capEvent hb hEwm (hreg' w) hℓ.le hwℓ 0
  obtain ⟨Rt, hRtm, hRt⟩ := exists_measurable_realMax_upper (κ := κ) hb (E := E) (u := u) (l := l)
    (hE su hsu).1 (hER su hsu) hu k
  have hRw' := WalkLaw.stagedPiecesRegular_regHist (hER w hw)
  obtain ⟨Mw, hMwae, hMwm, hMwp⟩ := hRw'.ae_pieceRegular.exists_measurable_mem
  choose S hSm hS using fun o => exists_measurableSet_relOffEvent_rand hb θ (D := Ew) hEwm (hreg' w) hMwm hMwp
    hRtm o
  set SS : Set Ω := LU ∩ CE ∩ ⋃ o, ({_ω | o + 2 ≤ ℓ} ∩ S o) with hSSdef
  have hSS : MeasurableSet SS :=
    ((h𝒢 _ (hu𝒢 _ hLU)).inter (h𝒢 _ (le_sup_right (a := pastSigma κ b jumps su Eu k) _ hCE))).inter
      (MeasurableSet.iUnion fun o => (MeasurableSet.const _).inter (hSm o))
  -- the frozen event and its regularized reading
  set I : Set Ω := {ω | ω ∈ stageEvent κ b jumps E u l k ℓ ∧ 0 < (E w ℓ ω).2 ∧
    ∃ o, o + 2 ≤ ℓ ∧ relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) o}
    with hIdef
  set J : Ω → Prop := fun ω => ω ∈ LU ∧ ω ∈ CE ∧
    ∃ o, o + 2 ≤ ℓ ∧ relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω))
      (fun i => Ew i ω) o with hJdef
  set M : Set Ω := {ω | (∀ n, ExplState.run κ b jumps su (fun j => Eu j ω) n =
      ExplState.run κ b jumps su (fun j => E su j ω) n) ∧
    (∀ n, ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => E w j ω) n) ∧
    ω ∈ Mw ∧ (IsCompact (upperPrefix κ b jumps E u l k ω) → Rt ω = realMax (upperPrefix κ b jumps E u l k ω)) ∧
    (ω ∈ Lu.upperLaunchSet κ b jumps E u l k → IsCompact (upperPrefix κ b jumps E u l k ω))} with hMdef
  have hMP : ∀ᵐ ω ∂P, ω ∈ M := by
    filter_upwards [hrun' su hsu, hrun' w hw, hMwae, hRt, hgood] with ω h1 h2 h3 h4 h5
    refine ⟨h1, h2, h3, h4, fun hl => ?_⟩
    obtain ⟨pA, hp, -, -, -, hpA⟩ := (h5 hl).upath
    exact hpA ▸ isCompact_Icc.image_of_continuousOn hp
  have hpre : ∀ ω ∈ M, upperPrefix κ b jumps (StagedReg.regFam E) u l k ω = upperPrefix κ b jumps E u l k ω := by
    intro ω hω
    unfold upperPrefix SB.prefixPhysSet
    show _ ∪ _ = _
    rw [show ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
      (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω) k =
      ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩ (fun j => E ⟨u, true, scheduleProgram 0 l⟩ j ω) k
      from hω.1 k]
  have hIJ : ∀ ω ∈ M, (ω ∈ I ↔ J ω) := by
    intro ω hω
    have hlu : ω ∈ Lu.upperLaunchSet κ b jumps E u l k ↔ ω ∈ LU := by
      show _ ≠ none ↔ _ ≠ none
      rw [hω.1 (k + 1)]
    have hce : (ω ∈ stageEvent κ b jumps E u l k ℓ ∧ 0 < (E w ℓ ω).2) ↔ (ω ∈ LU ∧ ω ∈ CE) := by
      have hsnd : (Ew ℓ ω).2 = (E w ℓ ω).2 := StagedReg.regularize_snd _ _
      show ((ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧ _ ≠ none) ∧ _) ↔
        (ω ∈ LU ∧ (_ ≠ none ∧ ((0 : ℝ≥0) : ℝ≥0∞) < (Ew ℓ ω).2))
      rw [hlu, hω.2.1 (ℓ + 1), hsnd, ENNReal.coe_zero]
      tauto
    have hro : ∀ o, o + 2 ≤ ℓ → (relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E w i ω) o ↔ relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω))
          (fun i => Ew i ω) o) := fun o _ => by
      rw [hpre ω hω]
      exact relOffEvent_congr _ _ _ _ _ o fun n _ => (hω.2.1 n).symm
    constructor
    · rintro ⟨h1, h2, o, ho, h3⟩
      obtain ⟨h4, h5⟩ := hce.1 ⟨h1, h2⟩
      exact ⟨h4, h5, o, ho, (hro o ho).1 h3⟩
    · rintro ⟨h4, h5, o, ho, h3⟩
      obtain ⟨h1, h2⟩ := hce.2 ⟨h4, h5⟩
      exact ⟨h1, h2, o, ho, (hro o ho).2 h3⟩
  have hEM : ∀ ω ∈ M, (ω ∈ I ↔ ω ∈ SS) := by
    intro ω hω
    rw [hIJ ω hω]
    constructor
    · rintro ⟨h4, h5, o, ho, h3⟩
      have hlu : ω ∈ Lu.upperLaunchSet κ b jumps E u l k := by
        show _ ≠ none
        rw [← hω.1 (k + 1)]; exact h4
      have hR : realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω) = Rt ω := by
        rw [hpre ω hω, hω.2.2.2.1 (hω.2.2.2.2 hlu)]
      rw [hR] at h3
      exact ⟨⟨h4, h5⟩, mem_iUnion.2 ⟨o, ho, (hS o ω hω.2.2.1).1 h3⟩⟩
    · rintro ⟨⟨h4, h5⟩, hU⟩
      obtain ⟨o, ho, h3⟩ := mem_iUnion.1 hU
      have hlu : ω ∈ Lu.upperLaunchSet κ b jumps E u l k := by
        show _ ≠ none
        rw [← hω.1 (k + 1)]; exact h4
      have hR : realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω) = Rt ω := by
        rw [hpre ω hω, hω.2.2.2.1 (hω.2.2.2.2 hlu)]
      refine ⟨h4, h5, o, ho, ?_⟩
      rw [hR]
      exact (hS o ω hω.2.2.1).2 h3
  -- frozen under the conditional laws
  have hfrU := Retain.ae_ae_run_eq su (WalkLaw.stagedPiecesRegular_regHist (hER su hsu)) h𝒢 hu𝒢
  have hfrW : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (lineSigma0 κ b jumps E u l k ℓ) ω₀), ∀ n, n ≤ ℓ →
      ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => Ew j ω₀) n := by
    have hn : ∀ n, ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (lineSigma0 κ b jumps E u l k ℓ) ω₀), n ≤ ℓ →
        ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => Ew j ω₀) n := by
      intro n
      by_cases hnℓ : n ≤ ℓ
      · filter_upwards [Retain.ae_ae_run_eq w hRw' h𝒢 ((pastSigma_mono _ _ hnℓ).trans hwℓ𝒢)] with ω₀ hx
        filter_upwards [hx] with ω hω _
        exact hω
      · exact Eventually.of_forall fun _ => Eventually.of_forall fun _ h => absurd h hnℓ
    filter_upwards [ae_all_iff.2 hn] with ω₀ hx
    exact ae_all_iff.2 fun n => hx n
  have hfr : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (lineSigma0 κ b jumps E u l k ℓ) ω₀), (ω ∈ I ↔ ω₀ ∈ I) := by
    filter_upwards [ae_ae_mem_iff (P := P) h𝒢 (hu𝒢 _ hLU),
      ae_ae_mem_iff (P := P) h𝒢 (le_sup_right (a := pastSigma κ b jumps su Eu k) _ hCE), hfrU, hfrW,
      Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hMP, hMP] with ω₀ h1 h2 h3 h4 h5 hM₀
    filter_upwards [h1, h2, h3, h4, h5] with ω g1 g2 g3 g4 g5
    rw [hIJ ω g5, hIJ ω₀ hM₀]
    have hup : upperPrefix κ b jumps (StagedReg.regFam E) u l k ω =
        upperPrefix κ b jumps (StagedReg.regFam E) u l k ω₀ := by
      unfold upperPrefix SB.prefixPhysSet
      show _ ∪ _ = _ ∪ _
      rw [show ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
        (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω) k =
        ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
          (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω₀) k from g3]
    show (ω ∈ LU ∧ ω ∈ CE ∧ _) ↔ (ω₀ ∈ LU ∧ ω₀ ∈ CE ∧ _)
    rw [g1, g2, hup]
    refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun o => ?_
    constructor
    · rintro ⟨ho, hr⟩
      exact ⟨ho, (relOffEvent_congr _ _ _ _ _ o fun n hn => g4 n (by omega)).1 hr⟩
    · rintro ⟨ho, hr⟩
      exact ⟨ho, (relOffEvent_congr _ _ _ _ _ o fun n hn => g4 n (by omega)).2 hr⟩
  have hmem := WalkLaw.mem_aeSigma_of_frozen (P := P) h𝒢 (E := I) hSS hMP hEM hfr
  obtain ⟨G', hG'm, hG'e⟩ := hmem
  refine ⟨G', hG'm, ?_⟩
  -- the intrinsic characterization
  filter_upwards [hG'e.mem_iff, hgood] with ω hG hg
  rw [← hG]
  constructor
  · rintro ⟨hst, hζ, o, ho, hr⟩
    exact ⟨hst, by rw [hr.1]; omega, hζ⟩
  · rintro ⟨hst, hlt, hζ⟩
    have hev := even_of_launch hst.2
    have hre := relOff_even κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
    have hlt' : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ := hlt
    exact ⟨hst, hζ, _, by omega, relOffEvent_of_walkGood (hg hst.1)⟩

end

end InteractingSLE.Theorem14.SB.Nc

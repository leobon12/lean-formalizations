/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfGood
import InteractingSLE.Spec.Supplement.SB2NcData
import InteractingSLE.Spec.Supplement.SB2CnMeas

/-!
# F2b′'s root: the B-time-0 event, the right end `R` at time `0`, the root offset

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). Three tools for the root objects:

* **`exists_rootLive`**: an event `FB` of the line σ-algebra at B-time `0` with, almost surely,
  `ω ∈ FB ↔ (stage event ∧ ℓ ≤ relOff ∧ 0 < ζ_ℓ)` — the launch and positive-lifetime events (measurable for the
  pasts) minus the tail live event (`Nc.exists_liveEvent`);
* **`exists_realMax_lineC0`**: `R = max (A ∩ ℝ)` agrees almost surely with a variable measurable for the completed
  line σ-algebra at time `0` (frozen under its conditional laws, `Nc.measurable_inf_aeSigma_of_frozen`);
* **`root_of_entr`** (deterministic): at a launch of B's stage `ℓ ≤ relOff` whose piece enters `R` before its
  lifetime, `ℓ = relOff` and the root is not a zero root.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf Supp8.Q3Stop WalkSide LocalSets Sec7.PocketTraversal Lk LuM
  Nc GW1Bookkeep

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A piece entering `R` before its lifetime at a stage `ℓ ≤ relOff` is the root's**, off a zero root. -/
theorem root_of_entr {Ω : Type u} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)}
    {k ℓ : ℕ} {ω : Ω} (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hle : ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))
    (hent : Nd.entrR κ b jumps E u l k ℓ ω < bLife b jumps E ℓ ω) :
    relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
      ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set R := realMax (upperPrefix κ b jumps E u l k ω) with hRdef
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 ∧ pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) t = (R : ℂ) := by
    by_contra hno
    have h1 : Nd.entrR κ b jumps E u l k ℓ ω = (D ℓ).2 := Ck.entrTime_eq_life hno
    rw [h1] at hent
    exact lt_irrefl _ hent
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hg.reg hl
  have hmem : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D (ℓ + 1)) := by
    have : (R : ℂ) ∈ SB.prefixPhysSet κ b jumps w D (ℓ + 1) := by
      rw [prefixPhysSet_succ_of_launch hl']
      right
      rw [htip]
      obtain ⟨t, ht, he⟩ := hvis
      exact ⟨t, ht, he⟩
    exact this
  have hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D (n + 1)) := ⟨ℓ, hmem⟩
  obtain ⟨-, hmin⟩ := entryStage_spec κ θ b jumps hex
  have hes : entryStage κ θ b jumps R D ≤ ℓ := by
    by_contra hlt
    exact hmin ℓ (not_le.1 hlt) hmem
  have hev := even_of_launch hl
  have hoff := startOff_eq κ θ b jumps R D
  have hso : startOff κ θ b jumps R D ≤ entryStage κ θ b jumps R D := by unfold startOff; omega
  have hse : startOff κ θ b jumps R D % 2 = 0 := startOff_even κ θ b jumps R D
  by_cases hm : MarkEntry κ θ b jumps R D
  · have hr := relOff_of_mark κ θ b jumps hm
    have he1 := hoff.1 hm.1
    refine ⟨by omega, fun hz => hz.2 hm⟩
  · have hr := relOff_of_not_mark κ θ b jumps hm
    by_cases ha : ArcEntry κ θ b jumps R D
    · exfalso
      have he1 := hoff.1 ha
      have : relOff κ θ b jumps R D = startOff κ θ b jumps R D := hr
      unfold ArcEntry at ha
      omega
    · exact ⟨by have := hoff.2 ha; omega, fun hz => ha hz.1⟩

section Ae

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The root's B-time-0 event.** -/
theorem exists_rootLive (hb : IsPiecewiseConstantBoundaryData b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hgood : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k → WalkGood κ b jumps E u l k ω) :
    ∃ FB : Set Ω, MeasurableSet[lineSigma0 κ b jumps E u l k ℓ] FB ∧
      ∀ᵐ ω ∂P, (ω ∈ FB ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
        ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
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
  obtain ⟨F, hFm, hFae⟩ := exists_liveEvent hb hE hER hu hlθ k ℓ hℓ hwℓ hgood
  set LU : Set Ω := {ω | (ExplState.run κ b jumps su (fun j => Eu j ω) (k + 1)).2.2.2.1 k ≠ none} with hLUdef
  have hLU : MeasurableSet[pastSigma κ b jumps su Eu k] LU :=
    Lv.measurableSet_launch_pastSigma (spec := su) hb hEum (hreg' su) k
  set CE : Set Ω := capEvent κ b jumps w Ew ℓ 0 with hCEdef
  have hCE : MeasurableSet[pastSigma κ b jumps (capSpec w ℓ θ ((0 : ℝ≥0) : ℝ≥0∞)) Ew (ℓ + 1)] CE :=
    measurableSet_capEvent hb hEwm (hreg' w) hℓ.le hwℓ 0
  have hLU0 : MeasurableSet[lineSigma0 κ b jumps E u l k ℓ] LU := le_sup_left (b := pastSigma κ b jumps
    (capSpec w ℓ θ ((0 : ℝ≥0) : ℝ≥0∞)) Ew (ℓ + 1)) _ hLU
  have hCE0 : MeasurableSet[lineSigma0 κ b jumps E u l k ℓ] CE :=
    le_sup_right (a := pastSigma κ b jumps su Eu k) _ hCE
  refine ⟨(LU ∩ CE) \ F, (hLU0.inter hCE0).diff hFm, ?_⟩
  filter_upwards [hFae, hrun' su hsu, hrun' w hw] with ω hF h1 h2
  have hlu : ω ∈ Lu.upperLaunchSet κ b jumps E u l k ↔ ω ∈ LU := by
    show _ ≠ none ↔ _ ≠ none
    rw [h1 (k + 1)]
  have hce : (ω ∈ stageEvent κ b jumps E u l k ℓ ∧ 0 < (E w ℓ ω).2) ↔ (ω ∈ LU ∧ ω ∈ CE) := by
    have hsnd : (Ew ℓ ω).2 = (E w ℓ ω).2 := StagedReg.regularize_snd _ _
    show ((ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧ _ ≠ none) ∧ _) ↔
      (ω ∈ LU ∧ (_ ≠ none ∧ ((0 : ℝ≥0) : ℝ≥0∞) < (Ew ℓ ω).2))
    rw [hlu, h2 (ℓ + 1), hsnd, ENNReal.coe_zero]
    tauto
  simp only [mem_diff, mem_inter_iff]
  rw [← hce, hF]
  constructor
  · rintro ⟨⟨hst, hpos⟩, hn⟩
    exact ⟨hst, not_lt.1 fun hlt => hn ⟨hst, hlt, hpos⟩, hpos⟩
  · rintro ⟨hst, hle, hpos⟩
    exact ⟨⟨hst, hpos⟩, fun h' => absurd h'.2.1 (not_lt.2 hle)⟩

/-- **`R = max (A ∩ ℝ)` at B-time `0`**: almost surely a variable measurable for the completed line σ-algebra. -/
theorem exists_realMax_lineC0 (hb : IsPiecewiseConstantBoundaryData b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))) :
    ∃ Rt : Ω → ℝ, Measurable[lineC0 P κ b jumps E u l k ℓ] Rt ∧
      ∀ᵐ ω ∂P, Rt ω = realMax (upperPrefix κ b jumps E u l k ω) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set su := Lu.upperSpec u l with hsudef
  set w := boundaryWalkSpec b jumps θ true with hwdef
  have hsu : IsBoundaryContinuedProgram su.2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun'⟩ := StagedReg.regFam_spec hb hE hER
  set Ew := StagedReg.regFam E w with hEwdef
  have hcap := WalkSide.pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps) Ew hℓ.le hwℓ (0 : ℚ≥0)
  rw [NNRat.cast_zero] at hcap
  have h𝒢 : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
    sup_le ((hE' su hsu).2.1 k) (hcap.trans ((hE' w hw).2.1 (ℓ + 1)))
  obtain ⟨Rt, hRtm, hRt⟩ := Cn.exists_measurable_realMax_upperW (P := P) hb (hE su hsu).1 (hER su hsu) k
  refine ⟨Rt, measurable_inf_aeSigma_of_frozen h𝒢 hRtm ?_, hRt⟩
  have hfr := Retain.ae_ae_run_eq su (WalkLaw.stagedPiecesRegular_regHist (hER su hsu)) h𝒢
    (le_sup_left (a := pastSigma κ b jumps su (StagedReg.regFam E su) k)) (k := k)
  have hM : ∀ᵐ ω ∂P, Rt ω = realMax (upperPrefix κ b jumps E u l k ω) ∧
      ∀ n, ExplState.run κ b jumps su (fun j => StagedReg.regFam E su j ω) n =
        ExplState.run κ b jumps su (fun j => E su j ω) n := by
    filter_upwards [hRt, hrun' su hsu] with ω h1 h2 using ⟨h1, h2⟩
  filter_upwards [hfr, Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hM, hM] with ω₀ g1 g2 hM₀
  filter_upwards [g1, g2] with ω e1 e2
  have hup : ∀ ω' : Ω, (∀ n, ExplState.run κ b jumps su (fun j => StagedReg.regFam E su j ω') n =
      ExplState.run κ b jumps su (fun j => E su j ω') n) →
      upperPrefix κ b jumps E u l k ω' = upperPrefix κ b jumps (StagedReg.regFam E) u l k ω' := by
    intro ω' hω'
    unfold upperPrefix SB.prefixPhysSet
    show _ ∪ _ = _ ∪ _
    rw [show ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
      (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω') k =
      ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩ (fun j => E ⟨u, true, scheduleProgram 0 l⟩ j ω') k
      from hω' k]
  have hreg : upperPrefix κ b jumps (StagedReg.regFam E) u l k ω =
      upperPrefix κ b jumps (StagedReg.regFam E) u l k ω₀ := by
    unfold upperPrefix SB.prefixPhysSet
    show _ ∪ _ = _ ∪ _
    rw [show ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
      (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω) k =
      ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
        (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω₀) k from e1]
  rw [e2.1, hM₀.1, hup ω e2.2, hup ω₀ hM₀.2, hreg]

end Ae

end InteractingSLE.Theorem14.SB.Nf

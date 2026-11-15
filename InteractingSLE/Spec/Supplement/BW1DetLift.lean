/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1DetGraph
import InteractingSLE.Spec.Supplement.BW1TermLift
import InteractingSLE.Spec.Supplement.GW4RelLaw

/-!
# BW1 at a walk launch: the lift through the Borel relation graph

Packet PROVE-BW1-DET. `BW1Term.ae_isTermRelOf_pos` lifts BW1's identification from the regular conditional laws to
`P` through `DetTerminalStatement`, whose regularity clause (a continuous relative driver has a transient generating
trace) is a converse Rohde–Schramm statement that is not available deterministically. Here the lift uses instead:

* the Borel relation graph `termRelGraphStatement` (`BW1DetGraph`), applied to the triple
  (post-piece counterflow `Q`, launch counterflow `V`, record of the piece), which is measurable;
* the regularity of `Q` under the conditional laws, from Theorem 1.3 (`ae_kernel_isRegCf`: `Q` is a centred
  counterflow driver of the post-piece field with infinite lifetime under every conditional law,
  `GW4Rel.ae_trace_transient_noSimpleArc`), carried by the Borel event of regular rational codes.

* **`ae_isTermRelOf_pos_graph`**: `ae_isTermRelOf_pos` without `DetTerminalStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.BW1Det

open Exist Exist.StagedLaw Exist.Staged GW1RestartPair BW1Term

/-- The record of the piece at a launch, read from the retained past. -/
theorem pastMap_last_eq_recOf {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {right : Bool}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {ω : Ω}
    (hl : (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none) :
    pastMap κ b jumps (GW1Z.walkSpec b jumps right) E (k + 1) ω (Fin.last k) = recOf ⊤ (E k ω) := by
  simp only [pastMap, Fin.val_last]
  rw [retained_run_walk hl]
  rfl

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Under the conditional law given the retained past at a next launch, the canonical post-piece counterflow is
almost surely regular** (Theorem 1.3 for the centred counterflow of the post-piece field). -/
theorem ae_kernel_isRegCf (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E right n V ζV ℓ) {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞}
    (hQ : GW1Laws.IsTerminalRestartCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q ζQ) :
    ∀ᵐ ω₁ ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω₁) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₁), GW1Path.IsRegCf (fun t => Q t ω) := by
  have hκ := hdata.pos
  have hκ4 := hdata.lt_four
  have hb := hdata.boundary
  have hh := hdata.field
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps right)
  have hRp := hdata.pieces _ hprog
  obtain ⟨βk, Yk, hW, hgood⟩ := GW1Laws.exists_post_witness hT13₀ hκ hκ4 hb hh hdata.counterflow
    hdata.complete right hE hreg n
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hdata.stages, hRp] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  have hK := GW1Laws.ae_terminal_kernel hb hE hreg hW hgood hprev
  filter_upwards [hQ.2, hK] with ω₁ hQ₁ hK₁ hnext
  obtain ⟨-, -, -, hconfd, hliftd, -⟩ := hK₁ hnext
  have htr : ∀ ω, IsChartTransport (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω₁) (2 * n + 1))) 1 0 (chiC κ) (h ω)
      (Chart.chartTransport hconfd 1 0 (chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hconfd (Chart.locallyIntegrableOn_of_continuousOn hliftd) 1 0 _ _
  obtain ⟨hcfQ, hζQ⟩ := hQ₁ hnext _ htr
  filter_upwards [GW4Rel.ae_trace_transient_noSimpleArc hT13 hκ hκ4 hcfQ hζQ] with ω hω
  obtain ⟨hc, h0, γ, hγ, htr', -⟩ := hω
  exact ⟨hc, h0, γ, hγ, htr'⟩

/-- **`P`-almost surely at a next launch whose piece has positive lifetime, the canonical post-piece counterflow is
regular and is the relative counterflow of the launch counterflow after the piece.** -/
theorem ae_isTermRelOf_pos_graph (hBW1 : BW1.BW1Statement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E right n V ζV ℓ) {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞}
    (hQ : GW1Laws.IsTerminalRestartCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q ζQ)
    (hQreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ζQ ω = ⊤ ∧ Continuous (fun t => Q t ω) ∧ Q 0 ω = 0) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2 ≠ 0 →
      GW1Path.IsRegCf (fun t => Q t ω) ∧
        IsTermRelOf (fun t => Q t ω) (fun t => V t ω) (E (GW1Z.walkSpec b jumps right) (2 * n) ω) := by
  classical
  obtain ⟨G, hGm, hG⟩ := termRelGraphStatement
  have hκ := hdata.pos
  have hb := hdata.boundary
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps right)
  have hRp := hdata.pieces _ hprog
  -- the measurable identification event
  have hVm : ∀ t, Measurable (V t) := hdata.current.1
  have hQm : Measurable fun ω => (fun t => Q t ω) := measurable_pi_iff.mpr hQ.1
  have hVm' : Measurable fun ω => (fun t => V t ω) := measurable_pi_iff.mpr hVm
  have hpm0 : ∀ k, Measurable[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k]
      (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k) := fun k s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have hrecm : Measurable fun ω => pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right))
      (2 * n + 1) ω (Fin.last (2 * n)) :=
    (measurable_pi_apply _).comp ((hpm0 (2 * n + 1)).mono (hE.2.1 (2 * n + 1)) le_rfl)
  set M : Set Ω := {ω | (((fun t => Q t ω), (fun t => V t ω)), pastMap κ b jumps (GW1Z.walkSpec b jumps right)
      (E (GW1Z.walkSpec b jumps right)) (2 * n + 1) ω (Fin.last (2 * n))) ∈ G} ∩
    {ω | pathCode (fun t => Q t ω) ∈ GW1Borel.regularCodes} with hMdef
  have hM : MeasurableSet M :=
    (((hQm.prodMk hVm').prodMk hrecm) hGm).inter ((measurable_pathCode.comp hQm) GW1Borel.measurableSet_regularCodes)
  -- the events
  have hpm : ∀ k, Measurable[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k]
      (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k) := fun k s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have hL0 := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * n)
  have hLn := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * (n + 1))
  rw [GW1RestartPair.pastSigma_walk_connector] at hLn
  set L' : Set Ω := {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none} ∩
    {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none} ∩
    {ω | (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1) ω
      (Fin.last (2 * n))).2.1 ≠ 0} with hL'def
  have hL' : MeasurableSet[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right))
      (2 * n + 1)] L' := by
    refine ((pastSigma_mono (κ := κ) (b := b) (jumps := jumps) _ _ (Nat.le_succ (2 * n)) _ hL0).inter hLn).inter ?_
    have hc : Measurable[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right))
        (2 * n + 1)] fun ω => (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right))
          (2 * n + 1) ω (Fin.last (2 * n))).2.1 :=
      measurable_fst.comp (measurable_snd.comp ((measurable_pi_apply _).comp (hpm (2 * n + 1))))
    exact (hc (measurableSet_singleton 0)).compl
  -- the regularity
  have hVreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      GW1Path.IsRegCf (fun t => V t ω) := by
    filter_upwards [hdata.current.2.2] with ω hω hl
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨-, hc, h0, htr, -⟩ := hω c θ hcθ
    exact ⟨hc, h0, htr⟩
  have hDreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      GW1P.PieceRegular (E (GW1Z.walkSpec b jumps right) (2 * n) ω).1
        (min ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2) := by
    filter_upwards [hRp] with ω hω hl
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    have := hω (2 * n) θ _ c (eq_launch_of_launches _ _ hcθ).1 hcθ
    rwa [GW1W.instrTime_walk hl] at this
  have hcg : @MeasurableSpace.CountablyGenerated Ω
      (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) := by
    rw [pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  -- (1) under the conditional laws given the retained past before `2n + 1`
  have hT1 : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none} →
      ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀), ω₁ ∈ L' →
        ∀ᵐ ω ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀) (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₁), ω ∈ M := by
    filter_upwards [ae_kernel_isTermRelOf hBW1 h12p hT13 hT13₀ hdata hQ,
      KernelTower.ae_ae_condExpKernel_condExpKernel_eq (P := P)
        (pastSigma_mono (κ := κ) (b := b) (jumps := jumps) (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (Nat.le_succ (2 * n))) (hE.2.1 (2 * n + 1)) hcg,
      Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n))
        (Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n + 1)) (hVreg.and (hDreg.and hQreg))),
      Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n))
        (Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) (hE.2.1 (2 * n + 1)) hL'),
      Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n)) (ae_kernel_isRegCf hT13 hT13₀ hdata hQ)]
      with ω₀ hk hkk hreg2 hmem2 hrc2 hl0
    filter_upwards [hk hl0, hkk, hreg2, hmem2, hrc2] with ω₁ hk1 hkk1 hreg1 hmem1 hrc1 hL1
    rw [hkk1]
    obtain ⟨⟨hl1, hn1⟩, hp1⟩ := hL1
    have hpos : (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁).2 ≠ 0 := by
      have e := pastMap_last_snd_fst (κ := κ) (b := b) (jumps := jumps) hl1
      rw [← e]
      exact hp1
    filter_upwards [hk1 hn1 hpos, hreg1, hmem1 ⟨⟨hl1, hn1⟩, hp1⟩, hrc1 hn1] with ω hrel hregω hmemω hrcω
    obtain ⟨⟨hlω, hnω⟩, -⟩ := hmemω
    obtain ⟨hVr, hDr, -⟩ := hregω
    have hVr' := hVr hlω
    have hDr' := hDr hlω
    have hfin := ne_top_of_next hlω hnω
    refine ⟨?_, ?_⟩
    · change (((fun t => Q t ω), (fun t => V t ω)), pastMap κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n + 1) ω (Fin.last (2 * n))) ∈ G
      rw [pastMap_last_eq_recOf hlω]
      exact (hG _ _ _ hrcω hVr' hDr' hfin).2 hrel
    · change GW1Path.IsRegCf (GW1Borel.driver (pathCode fun t => Q t ω))
      rw [driver_pathCode hrcω.1 hrcω.2.1]
      exact hrcω
  -- (2) under the conditional laws given the retained past before `2n`
  have hT2 : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none} →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀), ω ∈ L'ᶜ ∪ M := by
    filter_upwards [hT1] with ω₀ hω₀ hl0
    have h2 := GW2Later.ae_of_ae_condExpKernel_on' (P := condExpKernel P (pastSigma κ b jumps
      (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀) (hE.2.1 (2 * n + 1)) hL' hM
      (hω₀ hl0)
    filter_upwards [h2] with ω hω
    by_cases hωL : ω ∈ L'
    · exact Or.inr (hω hωL)
    · exact Or.inl hωL
  -- (3) under `P`
  have hT3 := GW2Later.ae_of_ae_condExpKernel_on' (hE.2.1 (2 * n)) hL0
    ((hE.2.1 (2 * n + 1) _ hL').compl.union hM) hT2
  -- (4) the conclusion
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hdata.stages, hRp] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  filter_upwards [hT3, hprev, hVreg, hDreg, hQreg] with ω hω hpv hVr hDr hQr hn hpos
  have hl := hpv hn
  have hωL : ω ∈ L' := by
    refine ⟨⟨hl, hn⟩, ?_⟩
    change (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1) ω
      (Fin.last (2 * n))).2.1 ≠ 0
    have e := pastMap_last_snd_fst (κ := κ) (b := b) (jumps := jumps) hl
    simp only [pastMap]
    rw [e]
    exact hpos
  obtain ⟨hGω, hRegω⟩ := (hω hl).resolve_left (fun h => h hωL)
  have hVr' := hVr hl
  have hDr' := hDr hl
  have hQc := (hQr hn).2.1
  have hQ0 := (hQr hn).2.2
  have hregQ : GW1Path.IsRegCf (fun t => Q t ω) := by
    have h1 : GW1Path.IsRegCf (GW1Borel.driver (pathCode fun t => Q t ω)) := hRegω
    rwa [driver_pathCode hQc hQ0] at h1
  have hfin := ne_top_of_next hl hn
  have hGω' : (((fun t => Q t ω), (fun t => V t ω)), pastMap κ b jumps (GW1Z.walkSpec b jumps right)
      (E (GW1Z.walkSpec b jumps right)) (2 * n + 1) ω (Fin.last (2 * n))) ∈ G := hGω
  rw [pastMap_last_eq_recOf hl] at hGω'
  exact ⟨hregQ, (hG _ _ _ hregQ hVr' hDr' hfin).1 hGω'⟩

end InteractingSLE.Theorem14.BW1Det

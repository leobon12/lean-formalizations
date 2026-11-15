/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsNext

/-!
# GW1's finite retargeting law: the conditional half proved, the pathwise half isolated

Packet PROVE-GW1-LAWS. `GW1RestartPair.IsForcedRetarget` (BW2–BR4a in the walk's retained conditional experiment) has
a **conditional** half (measurable driver; under the regular conditional law given the post-piece past, the driver
drives the centred counterflow of the field read in the next launch chart, with infinite lifetime) and a **pathwise**
half (almost surely the relative curve is the terminal relative curve `Q` before its first visit to the next union,
through a clock).

* `exists_next_launch_canonical`: at the next launch of either walk, the canonical driver read from the conditional
  word and the next-launch chart field (`GW1Laws.cfDrvOf`) is measurable, satisfies the conditional half, and is
  almost surely continuous from `0` with infinite lifetime. Inputs: Theorem 1.2 (R44 form) and Theorem 1.3.
* `IsForcedRetargetCond`, `IsForcedRetargetPath`: the two halves; `isForcedRetarget_iff`.
* **`RetargetPathStatement`** (named input): every measurable driver satisfying the conditional half also satisfies
  the pathwise half for some clock. This is the content of BW2's forced arc and BR4a's target change inside the
  conditional pair (Astra follow-up 5 §4.4: "Only now apply finite retargeting, inside the already identified
  conditional law"); it involves no construction of a driver.
* **`finiteRetargetLawStatement_of_path`**: `FiniteRetargetLawStatement` from Theorems 1.2–1.3 and
  `RetargetPathStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Laws

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData GW1RestartPair

section Halves

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
  (right : Bool) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ)

/-- The conditional half of `IsForcedRetarget`. -/
def IsForcedRetargetCond (U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  (∀ t, Measurable (U t)) ∧
  ∀ᵐ ω₀ ∂P, ∀ c θ,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) = some (c, θ) →
    ∀ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      IsCenteredCounterflowDriver κ
        (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω₀)
        h' U ζ ∧
      ∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω₀), ζ ω = ⊤

/-- The pathwise half of `IsForcedRetarget`. -/
def IsForcedRetargetPath (Q U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (a : Ω → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ∀ c θ,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) = some (c, θ) →
    ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0 ∧
    (∃ γ, IsGeneratingTrace (fun t => U t ω) ⊤ γ ∧
      Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
    let d := stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E j ω) (2 * n + 1))
    let B := SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E j ω) (2 * (n + 1))
    ∃ T : ℝ≥0, firstTipTime (d.trans infinitySourceChart) (fun t => Q t ω) B = T ∧
      (∃ z ∈ B, (d.trans infinitySourceChart).tipAt (fun t => Q t ω) T z) ∧
      Continuous (a ω) ∧ StrictMono (a ω) ∧ range (a ω) = Iio T ∧
      ∀ r z, (c.trans infinitySourceChart).tipAt (fun t => U t ω) r z ↔
        (d.trans infinitySourceChart).tipAt (fun t => Q t ω) (a ω r) z

theorem isForcedRetarget_iff (Q U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (a : Ω → ℝ≥0 → ℝ≥0) :
    IsForcedRetarget κ b jumps P h right E n Q U ζ a ↔
      IsForcedRetargetCond κ b jumps P h right E n U ζ ∧ IsForcedRetargetPath κ b jumps P right E n Q U ζ a :=
  ⟨fun hR => ⟨⟨hR.1, hR.2⟩, hR.3⟩, fun hR => ⟨hR.1.1, hR.1.2, hR.2⟩⟩

end Halves

/-- **Named input: the pathwise half of BW2–BR4a in the retained conditional pair.** For the restart data of a walk
launch and any terminal relative pair, every measurable driver that is the conditional centred counterflow at the next
launch (the conditional half), with a measurable lifetime and almost surely continuous from `0` with infinite
lifetime at the next launch, is almost surely the terminal relative curve before its first visit to the next union,
through a continuous strictly increasing clock (the pathwise half). The regularity hypotheses are stated at the level
of `P` (not only under the conditional laws) because pathwise regularity does not pass from the conditional laws to
`P` without measurability (ruling R51). -/
def RetargetPathStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (right : Bool) (n : ℕ)
    (V : ℝ≥0 → Ω → ℝ) (ζV : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
    RestartData κ b jumps P h W' ζ' E right n V ζV ℓ →
    ∀ (Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞) (β : Ω → ℝ≥0 → ℝ≥0),
      IsTerminalRestart κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n V Q ζQ β →
    ∀ (U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsForcedRetargetCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n U ζ → Measurable ζ →
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0) →
      ∃ a : Ω → ℝ≥0 → ℝ≥0,
        IsForcedRetargetPath κ b jumps P right (E (GW1Z.walkSpec b jumps right)) n Q U ζ a

section Walk

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The good sorted witness at a later launch of either walk** (from GW0's forward implication, i.e. Theorem 1.3
at universe `0`, for the ambient bounds). -/
theorem exists_good_witness (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) (right : Bool) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (GW1Z.walkSpec b jumps right) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {k : ℕ} (hk : 0 < k) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (GW1Z.walkSpec b jumps right) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
          none → IsCfGoodWord κ (β ω) := by
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀)
    hκ hκ4 hb hh hcf hζ'
  cases right
  · obtain ⟨β, Y, hW, hI⟩ := exists_sorted_witness_left (θ := Real.pi / 2) hκ hb hh hE hreg hambR hk
    refine ⟨β, Y, hW, hI.mono fun ω hω hl => ?_⟩
    obtain ⟨hs, hR, hP, hO, -⟩ := hω hl
    exact ⟨hs, fn_bound_neg_of_lOrig hP hO (stRecL_run_nonpos κ b jumps _ _ le_rfl k) hambL, hR⟩
  · obtain ⟨β, Y, hW, hI⟩ := exists_sorted_witness_right (θ := -(Real.pi / 2)) hκ hb hh hE hreg hambL hk
    refine ⟨β, Y, hW, hI.mono fun ω hω hl => ?_⟩
    obtain ⟨hs, hL, hP, hO⟩ := hω hl
    exact ⟨hs, hL, fn_bound_pos_of_rOrig hP hO (zero_le_stRecR_run κ b jumps _ _ le_rfl k) hambR⟩

/-- **The canonical next-launch driver** of either walk: measurable, the conditional half of `IsForcedRetarget`, and
almost surely continuous from `0` with infinite lifetime at the next launch. -/
theorem exists_next_launch_canonical (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) (right : Bool) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (GW1Z.walkSpec b jumps right) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (n : ℕ) :
    ∃ (U : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsForcedRetargetCond κ b jumps P h right E n U ζ ∧ Measurable ζ ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω)
          (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        ζ ω = ⊤ ∧ Continuous (fun t => U t ω) ∧ U 0 ω = 0 := by
  obtain ⟨β, Y, hW, hgood⟩ := exists_good_witness hT13₀ hκ hκ4 hb hh hcf hζ' right hE hreg
    (k := 2 * (n + 1)) (by omega)
  have hD := measurable_cfDrvOf_witness h12p hκ hE hW
  have hcond := ae_isCenteredCounterflowDriver_witness h12p hκ hT13 hb hh hE hreg hW hgood
  set spec := GW1Z.walkSpec b jumps right with hspec
  have hker : ∀ ω, condExpKernel P (pastSigma κ b jumps spec E (2 * (n + 1))) ω =
      condExpKernel P (pastSigma κ b jumps spec E (2 * n + 1)) ω :=
    condExpKernel_walk_connector P E n
  refine ⟨fun t ω => (cfDrvOf h12p hκ (β ω, Y ω)).1 t, fun ω => (cfDrvOf h12p hκ (β ω, Y ω)).2,
    ⟨fun t => (measurable_pi_apply t).comp (measurable_fst.comp hD), ?_⟩, measurable_snd.comp hD, ?_⟩
  · filter_upwards [hcond] with ω₀ h₀ c θ hl h' hh'
    rw [← hker ω₀]
    exact h₀ c θ hl h' hh'
  · have hL : MeasurableSet[pastSigma κ b jumps spec E (2 * (n + 1))]
        {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none} :=
      GW1W.measurableSet_pastSigma_launch hb spec hE.1 hreg _
    have hA : MeasurableSet {ω | (cfDrvOf h12p hκ (β ω, Y ω)).2 = ⊤} :=
      (measurable_snd.comp hD) (measurableSet_singleton ⊤)
    have htop := GW2Later.ae_of_ae_condExpKernel_on' (hE.2.1 _) hL hA
      (ae_cfDrvOf_witness_eq_top h12p hκ hT13 hE hW hgood)
    filter_upwards [htop] with ω hω hl
    have hζω : (cfDrvOf h12p hκ (β ω, Y ω)).2 = ⊤ := hω hl
    obtain ⟨hcont, h0⟩ := cfDrvOf_regular h12p hκ (β ω, Y ω)
    refine ⟨hζω, ?_, h0⟩
    rw [hζω] at hcont
    simp only [ENNReal.coe_lt_top, ofPred_true] at hcont
    exact continuousOn_univ.1 hcont

/-- **GW1's finite retargeting law from its pathwise half** (conditional helper): Theorems 1.2 (R44 form) and 1.3
supply the conditional half through the canonical next-launch driver. -/
theorem finiteRetargetLawStatement_of_path (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hPath : RetargetPathStatement.{u}) : FiniteRetargetLawStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h W' ζ' E right n V ζV ℓ hdata Q ζQ β hQ
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  obtain ⟨U, ζ, hcond, hζm, hreg⟩ := exists_next_launch_canonical h12p hT13 hT13₀ hdata.pos hdata.lt_four
    hdata.boundary hdata.field hdata.counterflow hdata.complete right (hdata.staged _ hprog) (hdata.regular _) n
  obtain ⟨a, hpath⟩ := hPath κ b jumps P h W' ζ' E right n V ζV ℓ hdata Q ζQ β hQ U ζ hcond hζm hreg
  exact ⟨U, ζ, a, (isForcedRetarget_iff κ b jumps P h right _ n Q U ζ a).2 ⟨hcond, hpath⟩⟩

end Walk

end InteractingSLE.Theorem14.GW1Laws

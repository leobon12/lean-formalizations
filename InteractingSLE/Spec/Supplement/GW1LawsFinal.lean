/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsTerminalLaw
import InteractingSLE.Spec.Supplement.GW1RestartPairParam

/-!
# GW1's two restart laws from their pathwise halves

Packet PROVE-GW1-LAWS. Assembly:

* `exists_post_witness`: the recentred good stop word at a next launch, for either walk;
* **`exists_terminal_canonical`**: the canonical post-piece driver satisfies the conditional half of
  `IsTerminalRestart` and is almost surely continuous from `0` with infinite lifetime at a next launch;
* `IsTerminalRestartCond`, `IsTerminalRestartPath`, `isTerminalRestart_iff`;
* **`TerminalPathStatement`** (named input): BW1's pathwise identification;
* **`terminalRestartLawStatement_of_path`**, and **`walkLaunchClockStatement_of_paths`**: GW1's launch clocks at every
  launch of either walk from GB6's restart law, Theorems 1.2–1.3 and the two pathwise named inputs.
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

/-- The conditional half of `IsTerminalRestart`. -/
def IsTerminalRestartCond (Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞) : Prop :=
  (∀ t, Measurable (Q t)) ∧
  ∀ᵐ ω₀ ∂P,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω₀)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
    ∀ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport
        (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E j ω₀) (2 * n + 1))) 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      IsCenteredCounterflowDriver κ
        (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω₀)
        h' Q ζQ ∧
      ∀ᵐ ω ∂(condExpKernel P
        (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) E (2 * n + 1)) ω₀), ζQ ω = ⊤

/-- The pathwise half of `IsTerminalRestart`. -/
def IsTerminalRestartPath (V Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞) (β : Ω → ℝ≥0 → ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P,
    (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω)
      (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
    ζQ ω = ⊤ ∧ Continuous (fun t => Q t ω) ∧ Q 0 ω = 0 ∧
    (∃ γ, IsGeneratingTrace (fun t => Q t ω) ⊤ γ ∧
      Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
    IsRetainedClock
      ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E j ω) (2 * n))).trans infinitySourceChart)
      ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E j ω) (2 * n + 1))).trans infinitySourceChart)
      (fun t => V t ω) (fun t => Q t ω)
      (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E j ω) (2 * n + 1)) (β ω)

theorem isTerminalRestart_iff (V Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞) (β : Ω → ℝ≥0 → ℝ≥0) :
    IsTerminalRestart κ b jumps P h right E n V Q ζQ β ↔
      IsTerminalRestartCond κ b jumps P h right E n Q ζQ ∧ IsTerminalRestartPath κ b jumps P right E n V Q ζQ β :=
  ⟨fun hR => ⟨⟨hR.1, hR.2⟩, hR.3⟩, fun hR => ⟨hR.1.1, hR.1.2, hR.2⟩⟩

end Halves

/-- **Named input: BW1's pathwise identification in the retained conditional pair.** For the restart data of a walk
launch, every measurable driver that is the conditional centred counterflow of the post-piece field (the conditional
half of `IsTerminalRestart`), with a measurable lifetime and almost surely continuous from `0` with infinite lifetime
at a next launch, is almost surely the launch counterflow before its first visit to the new union, through a retained
clock (the pathwise half). -/
def TerminalPathStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (right : Bool) (n : ℕ)
    (V : ℝ≥0 → Ω → ℝ) (ζV : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
    RestartData κ b jumps P h W' ζ' E right n V ζV ℓ →
    ∀ (Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞),
      IsTerminalRestartCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q ζQ → Measurable ζQ →
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        ζQ ω = ⊤ ∧ Continuous (fun t => Q t ω) ∧ Q 0 ω = 0) →
      ∃ β : Ω → ℝ≥0 → ℝ≥0,
        IsTerminalRestartPath κ b jumps P right (E (GW1Z.walkSpec b jumps right)) n V Q ζQ β

section Walk

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The recentred good stop word at a next launch of either walk.** -/
theorem exists_post_witness (hT13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) (right : Bool) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (GW1Z.walkSpec b jumps right) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (n : ℕ) :
    ∃ (βk : Ω → BoundaryWord) (Yk : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (GW1Z.walkSpec b jumps right) E (2 * (n + 1)) βk Yk ∧
      ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (2 * (n + 1) + 1)).2.2.2.1
          (2 * (n + 1)) ≠ none →
        (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠
          none →
        ∃ γ : BoundaryWord, IsCfGoodWord κ γ ∧
          βk ω = BoundaryWord.shiftW (postShift κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E j ω) n) γ := by
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀)
    hκ hκ4 hb hh hcf hζ'
  cases right
  · exact exists_post_witness_left hκ hb hh hE hreg hambL hambR n
  · exact exists_post_witness_right hκ hb hh hE hreg hambL hambR n

/-- **The canonical post-piece driver**: measurable, the conditional half of `IsTerminalRestart`, and almost surely
continuous from `0` with infinite lifetime at a next launch. -/
theorem exists_terminal_canonical (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E right n V ζV ℓ) :
    ∃ (Q : ℝ≥0 → Ω → ℝ) (ζQ : Ω → ℝ≥0∞),
      IsTerminalRestartCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q ζQ ∧ Measurable ζQ ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
        ζQ ω = ⊤ ∧ Continuous (fun t => Q t ω) ∧ Q 0 ω = 0 := by
  have hκ := hdata.pos
  have hb := hdata.boundary
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps right)
  obtain ⟨βk, Yk, hW, hgood⟩ := exists_post_witness hT13₀ hκ hdata.lt_four hb hdata.field hdata.counterflow
    hdata.complete right hE hreg n
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hdata.stages, hdata.pieces _ hprog] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  have hK := ae_terminal_kernel hb hE hreg hW hgood hprev
  have hβm : Measurable (postWord κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n βk) :=
    measurable_postWord hb _ hE.1 hreg n (hW.1.mono (hE.2.1 _) le_rfl)
  have hYm : Measurable (postField κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n Yk) :=
    measurable_postField hb _ hE.1 hreg n hW.2.1
  have hD : Measurable fun ω => cfDrvOf h12p hκ
      (postWord κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n βk ω,
        postField κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n Yk ω) :=
    (measurable_cfDrvOf h12p hκ).comp (hβm.prodMk hYm)
  have hker : ∀ ω, condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * (n + 1))) ω =
      condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω :=
    condExpKernel_walk_connector (κ := κ) (b := b) (jumps := jumps)
      (θ := if right then -(Real.pi / 2) else Real.pi / 2) (right := right) P _ n
  -- the lifetime under the kernel
  have hlife : ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω₀)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * (n + 1))) ω₀),
        (cfDrvOf h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n βk ω,
          postField κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n Yk ω)).2 = ⊤ := by
    filter_upwards [hK] with ω₀ hk hlk
    obtain ⟨hgw, hgff, hwd, -, -, -⟩ := hk hlk
    filter_upwards [hwd, ae_cfDrvOf_snd_eq_top h12p hκ hT13 hgw.1 hgw.2.1 hgw.2.2 hgff] with ω h1 h2
    rw [h1]
    exact h2
  refine ⟨fun t ω => (cfDrvOf h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right)
      (E (GW1Z.walkSpec b jumps right)) n βk ω, postField κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) n Yk ω)).1 t,
    fun ω => (cfDrvOf h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right)
      (E (GW1Z.walkSpec b jumps right)) n βk ω, postField κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) n Yk ω)).2,
    ⟨fun t => (measurable_pi_apply t).comp (measurable_fst.comp hD), ?_⟩, measurable_snd.comp hD, ?_⟩
  · filter_upwards [hK, hlife] with ω₀ hk hl₀ hlk h' hh'
    obtain ⟨hgw, hgff, hwd, hconf, hlift, htrans⟩ := hk hlk
    rw [← hker ω₀]
    have hYe := htrans h' hh'
    have hh'm : Measurable h' := by
      have e : h' = fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) := funext fun ω =>
        (hh' ω).eq_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift)
      rw [e]
      exact (Chart.measurable_chartTransport _ _ _ _).comp hdata.field.1
    have hgff' := isGFFWithBoundaryData_congr_ae hgff hh'm hYe
    have hae : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * (n + 1))) ω₀),
        (cfDrvOf h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n βk ω,
          postField κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n Yk ω)).2 =
          (cfDrvOf h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) n βk ω₀, h' ω)).2 ∧
        ∀ t, (cfDrvOf h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) n βk ω,
          postField κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) n Yk ω)).1 t =
          (cfDrvOf h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) n βk ω₀, h' ω)).1 t := by
      filter_upwards [hwd, hYe] with ω h1 h2
      rw [h1, h2]
      exact ⟨rfl, fun _ => rfl⟩
    exact ⟨isCenteredCounterflowDriver_of_ae_cfDrvOf h12p hκ hT13 hgw.1 hgff'
      (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hD)) (measurable_snd.comp hD) hae, hl₀ hlk⟩
  · have hL := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * (n + 1))
    have hA : MeasurableSet {ω | (cfDrvOf h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) n βk ω, postField κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) n Yk ω)).2 = ⊤} :=
      (measurable_snd.comp hD) (measurableSet_singleton ⊤)
    have htop := GW2Later.ae_of_ae_condExpKernel_on' (hE.2.1 _) hL hA hlife
    filter_upwards [htop] with ω hω hl
    have hζω := hω hl
    obtain ⟨hcont, h0⟩ := cfDrvOf_regular h12p hκ (postWord κ b jumps (GW1Z.walkSpec b jumps right)
      (E (GW1Z.walkSpec b jumps right)) n βk ω, postField κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) n Yk ω)
    refine ⟨hζω, ?_, h0⟩
    rw [hζω] at hcont
    simp only [ENNReal.coe_lt_top, ofPred_true] at hcont
    exact continuousOn_univ.1 hcont

/-- **GW1's terminal restart law from its pathwise half** (conditional helper). -/
theorem terminalRestartLawStatement_of_path (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hPath : TerminalPathStatement.{u}) : TerminalRestartLawStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h W' ζ' E right n V ζV ℓ hdata
  obtain ⟨Q, ζQ, hcond, hζm, hreg⟩ := exists_terminal_canonical h12p hT13 hT13₀ hdata
  obtain ⟨β, hpath⟩ := hPath κ b jumps P h W' ζ' E right n V ζV ℓ hdata Q ζQ hcond hζm hreg
  exact ⟨Q, ζQ, β, (isTerminalRestart_iff κ b jumps P h right _ n V Q ζQ β).2 ⟨hcond, hpath⟩⟩

end Walk

/-- **GW1's launch clocks at every launch of either walk** from GB6's restart law, Theorems 1.2–1.3 and the two
pathwise named inputs (conditional helper). -/
theorem walkLaunchClockStatement_of_paths (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hT : TerminalPathStatement.{u}) (hR : RetargetPathStatement.{u}) :
    GW1Z.WalkLaunchClockStatement.{u} :=
  GW1RestartPair.walkLaunchClockStatement_of_terminal_and_retarget_laws hGB6 hT13 hT13₀
    (terminalRestartLawStatement_of_path h12p hT13 hT13₀ hT) (finiteRetargetLawStatement_of_path h12p hT13 hT13₀ hR)

end InteractingSLE.Theorem14.GW1Laws

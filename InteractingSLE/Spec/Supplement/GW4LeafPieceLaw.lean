/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafPiece
import InteractingSLE.Spec.Supplement.GW1PieceSimpleFiber

/-!
# GW1's reverse first visits of every launched piece of the two walks, almost surely

Packet PROVE-T14-GW4REG. GW1 (p. 619): "Apply GB6, within the independently established complete conditional pair in
item 2, to every available interior-tip prefix of `β_j`. It lies in `η[0, T_{w_j}]` in reverse first-visit order."

* `ae_fcAt`: under a law `Q` (the regular conditional law at a launch), GB6's first-contact assertion (from its restart
  law) gives the measurable event `FCAt` for the piece and its conditional counterflow almost surely;
* **`walkPieceVisitStatement_of_clock`**: almost surely, every piece launched by either boundary walk has its
  first-visit data `PieceVisitOK` with respect to the original counterflow and the old union before its instruction.
  Inputs: GB6's restart law, GW0's forward implication, Theorem 1.3, GW1's launch clocks
  (`GW1Z.WalkLaunchClockStatement`)
  and the chart fibres (`GW1Z.ChartFiberStatement`, proved). The proof is that of
  `GW1Z.gw1PieceSimpleStatement_of_clock` with the event `FCAt` added.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW1Z
open Supp8.GB6 (IsFirstContactAtTip sphereInv)
open Exist.StagedLaw (instrTime)

/-- **GB6's first contacts under a law `Q`, as the event `FCAt`.** -/
theorem ae_fcAt (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {b' : ℝ → ℝ} {jumps' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' jumps')
    {h' : Ω → DistOn upperHalfPlaneOpens} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b' jumps' θ Q h' (fun t ω => (e ω).1 t) (fun ω => (e ω).2))
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} (hWk : IsCenteredCounterflowDriver κ Q h' Wk ζk)
    (hζk : ∀ᵐ ω ∂Q, ζk ω = ⊤) (t₀ : ℝ≥0∞) :
    ∀ᵐ ω ∂Q, FCAt (fun t => LP.traceAt t (e ω).1) (fun t => LP.traceAt t fun s => Wk s ω)
      (min t₀ (e ω).2) := by
  have hh := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  obtain ⟨b'', J'', h'', hb'', htr, hcf⟩ := hWk
  have hκ' : 0 < 16 / κ := by positivity
  obtain ⟨hadmL, hadmR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hcf hζk
  set γ := GW2aSingle.chosenTrace Wk ζk with hγdef
  set α := GW2aSingle.chosenTrace (fun t ω => (e ω).1 t) (fun ω => (e ω).2) with hαdef
  have hγ := GW2aSingle.ae_chosenTrace hT13 hκ' hcf
  have hα := GW2aSingle.ae_chosenTrace hT13 hκ hfl
  have hcomp : ∀ᵐ ω ∂Q, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop := by
    filter_upwards [hγ, hζk] with ω hω hζ
    rw [hζ] at hω
    exact ⟨hζ, hω.1, hω.2 rfl⟩
  have hFC := Supp8.GB6.gb6FirstContactStatement_of_restart hGB6 κ θ hκ hκ4 hθ.1 hθ.2 Ω _ Q
    inferInstance h' b' jumps' Wk (fun t ω => (e ω).1 t) ζk (fun ω => (e ω).2) γ α b'' J'' h'' hb' hh hb''
    htr hcf hadmL hadmR hcomp hfl (hα.mono fun _ hω => hω.1)
  have hall := ae_all_iff.2 fun q : ℚ => hFC (rt q)
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hcfd := Supp8.GB6.ae_driver_zero_continuousOn hcf
  filter_upwards [hcomp, hα, hall, hdrv, hcfd] with ω hcω hαω hqω hdω hcfω
  have hWc : Continuous fun s => Wk s ω := by
    have hc' := hcfω.2
    rw [hcω.1] at hc'
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc'
    exact continuousOn_univ.1 hc'
  have hγc : Continuous (γ ω) := by
    have hc' := hcω.2.1.2.1
    simp only [le_top, ofPred_true] at hc'
    exact continuousOn_univ.1 hc'
  have hαS : IsGeneratingTrace (e ω).1 (min t₀ (e ω).2) (α ω) := hαω.1.mono_horizon (min_le_right _ _)
  have hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < min t₀ (e ω).2 → LP.traceAt (rt q) (e ω).1 = α ω (rt q) := fun q hq =>
    LP.traceAt_eq_of_isGeneratingTrace hαω.1 hdω.2 hdω.1 (lt_of_lt_of_le hq (min_le_right _ _))
  have hG : ∀ r : ℚ, LP.traceAt (rt r) (fun s => Wk s ω) = γ ω (rt r) := fun r =>
    LP.traceAt_eq_of_isGeneratingTrace hcω.2.1 hWc.continuousOn hcfω.1 ENNReal.coe_lt_top
  exact fcAt_of_firstContact hαS.2.1 hγc hA hG fun q _ hqS hqH =>
    hqω q (lt_of_lt_of_le hqS (min_le_right _ _)) hqH

/-- **The first-visit data of every launched piece of a boundary walk** (GW1, p. 619), for the staged families of
`GW1Z.GW1PieceSimpleStatement` (drivers regular at every sample, launched pieces regular almost surely): almost surely,
for every generating trace `γ` of the counterflow, every piece launched by the walk has its first-visit data with
respect to `γ` and the old union before its instruction. -/
def WalkPieceVisitStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ right : Bool, ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ →
        ∀ (k : ℕ) (c : Chart) (θ : ℝ),
          (ExplState.run κ b jumps (walkSpec b jumps right) (fun j => E (walkSpec b jumps right) j ω)
            (k + 1)).2.2.2.1 k = some (c, θ) →
          PieceVisitOK γ c (E (walkSpec b jumps right) k ω).1
            (min (instrTime (walkSpec b jumps right) k) (E (walkSpec b jumps right) k ω).2)
            (SB.prefixPhysSet κ b jumps (walkSpec b jumps right) (fun j => E (walkSpec b jumps right) j ω) k)

/-- **`WalkPieceVisitStatement` from GW1's launch clocks** (and GB6's restart law, GW0's forward implication,
Theorem 1.3, the chart fibres). -/
theorem walkPieceVisitStatement_of_clock (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hD : WalkLaunchClockStatement.{u}) (hF : ChartFiberStatement) : WalkPieceVisitStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg hR right
  have hwR := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (walkAngle_mem_Icc right) right
  have hS := hE (walkSpec b jumps right) hwR
  have hRs := hR (walkSpec b jumps right) hwR
  have htrace := GW4Traverse.ae_trace_of_isCenteredCounterflowDriver hT13 hκ hcf hζ'
  have hall : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ →
      ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (walkSpec b jumps right) (fun j => E (walkSpec b jumps right) j ω)
          (k + 1)).2.2.2.1 k = some (c, θ) →
        PieceVisitOK γ c (E (walkSpec b jumps right) k ω).1
          (min (instrTime (walkSpec b jumps right) k) (E (walkSpec b jumps right) k ω).2)
          (SB.prefixPhysSet κ b jumps (walkSpec b jumps right) (fun j => E (walkSpec b jumps right) j ω) k) := by
    intro k
    obtain ⟨Wk, ζk, ℓ, hWm, hD1, hD2⟩ := hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hR right k
    set spec := walkSpec b jumps right with hspec
    set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.1 k ≠ none}
      with hLdef
    have hL : MeasurableSet[pastSigma κ b jumps spec (E spec) k] L :=
      GW1W.measurableSet_pastSigma_launch hb spec hS.1 (hreg spec) k
    set M := PieceVisitEvent (E spec k) (fun ω => min (instrTime spec k) (E spec k ω).2) Wk ∩
      {ω | FCAt (fun t => LP.traceAt t (E spec k ω).1) (fun t => LP.traceAt t fun s => Wk s ω)
        (min (instrTime spec k) (E spec k ω).2)} with hMdef
    have hM : MeasurableSet M := by
      refine (measurableSet_pieceVisitEvent (hS.1 k)
        (measurable_const.min (measurable_snd.comp (hS.1 k))) hWm).inter ?_
      refine measurableSet_setOfPred.2 (measurable_fcAt (fun t => ?_) (fun t => ?_)
        (measurable_const.min (measurable_snd.comp (hS.1 k))))
      · exact (LP.measurable_traceAt t).comp (measurable_fst.comp (hS.1 k))
      · exact (LP.measurable_traceAt t).comp (measurable_pi_iff.2 hWm)
    have hker : ∀ᵐ ω₀ ∂P, ω₀ ∈ L →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω₀), ω ∈ M := by
      filter_upwards [hS.2.2.2 k, hD1] with ω₀ hst hd1 hω₀
      obtain ⟨⟨c, θ⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω₀
      obtain ⟨b', jumps', h', hb', htr, hfl⟩ := hst c θ hl
      obtain ⟨hWk, hζk⟩ := hd1 c θ hl h' htr
      have hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        angle_walkSpec_mem (Exist.StagedLaw.eq_launch_of_launches spec _ hl).1
      have hrec := Eventually.of_forall (f := ae (condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω₀))
        fun ω => (hreg spec k ω).2.2.2
      filter_upwards [ae_mem_pieceVisitEvent hGB6 hGW0 hT13 hκ hκ4 hθ hb' hfl hrec hWk hζk (instrTime spec k),
        ae_fcAt hGB6 hGW0 hT13 hκ hκ4 hθ hb' hfl hWk hζk (instrTime spec k)] with ω h1 h2
      exact ⟨h1, h2⟩
    have hP := GW2Later.ae_of_ae_condExpKernel_on' (hS.2.1 k) hL hM hker
    filter_upwards [hP, hRs, hD2, htrace] with ω hPω hRω hD2ω htrω γ hγ c θ hl
    have hωM : ω ∈ M := hPω (show _ ≠ none by rw [hl]; exact Option.some_ne_none _)
    have hk := (Exist.StagedLaw.eq_launch_of_launches spec _ hl).1
    obtain ⟨hw0, hwc, η, hη, -⟩ := hRω k θ (instrTime spec k) c hk hl
    obtain ⟨-, hWkc, hWk0, ⟨γk, hγk, hγktr⟩, -, hℓm, hrange, hiff⟩ := hD2ω c θ hl
    obtain ⟨hW'c, hW'0, -⟩ := htrω
    have hregω : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
        (ExplState.run κ b jumps spec (fun j => E spec j ω) (j + 1)).2.2.2.1 j = some (c', θ') →
        GW1P.PieceRegular (E spec j ω).1 (min (instrTime spec j) (E spec j ω).2) := by
      intro j c' θ' hl'
      obtain ⟨a1, a2, a3, a4, a5⟩ :=
        hRω j θ' (instrTime spec j) c' (Exist.StagedLaw.eq_launch_of_launches spec _ hl').1 hl'
      exact ⟨a1, a2, a3, a4, a5⟩
    obtain ⟨f, C, hf, hC, hfib⟩ := hF κ b jumps spec (fun j => E spec j ω) hregω k c θ hl
    exact pieceVisitOK_of_events hf hC hfib hη hwc hw0 hγk hγktr hWkc hWk0 hγ hW'c hW'0 hℓm hrange hiff
      hωM.1.1 hωM.1.2 hωM.2
  filter_upwards [ae_all_iff.2 hall] with ω hω γ hγ k c θ hl
  exact hω k γ hγ c θ hl

end GW4Leaf

end Theorem14

end InteractingSLE

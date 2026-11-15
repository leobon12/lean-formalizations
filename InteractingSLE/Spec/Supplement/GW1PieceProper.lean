/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PieceRun
import InteractingSLE.Spec.Supplement.GW2aSingle
import InteractingSLE.Spec.Supplement.SBFrontier
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# GW1's properness for the pieces of the walks: `SB.GW1PieceProperStatement` from piece regularity

Packet PROVE-T14-GW1P. `SB.GW1PieceProperStatement` (PROVE-T14-SB) asks that almost surely every ordinary piece of
both boundary walks of GW1 is relatively closed in `ℍ` (supplement p. 618: "a field-determined continuous injective
proper curve `R`"). The deterministic half is `GW1P.closure_tipSet_inter_H_subset_run` (files `GW1PieceChart`,
`GW1PieceRun`): it suffices that every launched piece has regular data (`GW1P.PieceRegular`). This file supplies
that regularity from Theorem 1.3:

* **`ae_pieceRegular_of_isFlowLineDriver`** — under any probability law for which a driver is a flow-line driver,
  Theorem 1.3 (`Exist.Theorem13Statement`), the continuity of the integrated evolution and Aux. lemma 3 (with the
  recorded continuous limit at a finite positive lifetime) give a.s. regular data, for any own stop time;
* **`ae_pieceRegular_first`** — the first piece of a history from the root `0` that starts with an ordinary
  instruction is a.s. regular under `P` (its conditional law is `P`: `IsStagedHistory.isFlowLineDriver_first`);
* **`ae_condExpKernel_pieceRegular`** — every launched piece is a.s. regular under its conditional law
  `condExpKernel P (pastSigma … k) ω₀`, for `P`-a.e. `ω₀` at which it is launched;
* **`gw1PieceProperStatement_of_later`** — `SB.GW1PieceProperStatement` from Theorem 1.3 and the named statement
  `StagedLaterPieceRegularStatement` (every later launched piece of a staged history is regular `P`-a.s.).

## The remaining step and why it is not proved here

`StagedLaterPieceRegularStatement` is the passage from "regular under the conditional law, for `P`-a.e. launch
point" (`ae_condExpKernel_pieceRegular`, proved) to "regular `P`-a.s.". For an event `G` this passage is valid when
`G` is (null-)measurable (`Sec5.Lemma56Stages.ae_of_ae_condExpKernel`,
`SB.ae_of_ae_condExpKernel_of_nullMeasurableSet`). The regularity event involves the continuity of the driver
`(E k ω).1` at every real time; `E k` is only measurable for the product σ-algebra of `ℝ≥0 → ℝ`, in which every
nonempty measurable set contains discontinuous paths, so this event is
in general not measurable, and the frozen `IsStagedHistory` constrains the pieces after the first one only through
their conditional laws. See the handoff `planning/handoffs/PROVE-T14-GW1P.md` (§5) for the precise obstruction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1P

open CounterflowRange Exist.Staged Exist.StagedLaw

/-! ### Regular data from Theorem 1.3 -/

/-- **Regular data of a flow-line piece** (Theorem 1.3, the continuity of the integrated evolution, Aux. lemma 3):
under a probability law `μ` for which `W` (lifetime `ζ`) is a flow-line driver and whose recorded value at a finite
positive lifetime is the continuous limit when there is one, almost surely the piece run for own time `t` (stop
`min t ζ`) has regular data. -/
theorem ae_pieceRegular_of_isFlowLineDriver (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b J θ μ h W ζ)
    (hrec : ∀ᵐ ω ∂μ, ζ ω ≠ ⊤ → 0 < ζ ω → ∀ c : ℝ,
      Tendsto (fun t => W t ω) (𝓝[<] (ζ ω).toNNReal) (𝓝 c) → W (ζ ω).toNNReal ω = c) (t : ℝ≥0∞) :
    ∀ᵐ ω ∂μ, PieceRegular (fun s => W s ω) (min t (ζ ω)) := by
  have hα := GW2aSingle.ae_chosenTrace h13 hκ hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hthr := hC.1.ae_tendsto_threshold hκ
  filter_upwards [hα, hdrv, hthr, hrec] with ω hαω hdω hthω hrecω
  have hend : ζ ω ≠ ⊤ → 0 < ζ ω →
      Tendsto (fun s => W s ω) (𝓝[<] (ζ ω).toNNReal) (𝓝 (W (ζ ω).toNNReal ω)) := by
    intro hne hpos
    have hT : (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hne
    have hTpos : 0 < (ζ ω).toNNReal := ENNReal.toNNReal_pos hpos.ne' hne
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthω _ hTpos hT
    have h1 : Tendsto (fun s => W s ω) (𝓝[<] (ζ ω).toNNReal) (𝓝 w₀) :=
      (continuous_fst.tendsto _).comp hlim
    rw [hrecω hne hpos w₀ h1]
    exact h1
  refine ⟨hdω.1, continuousOn_le_min t hdω.2 hend, GW2aSingle.chosenTrace W ζ ω,
    IsGeneratingTrace.mono_horizon hαω.1 (min_le_right _ _), fun htop => hαω.2 ?_⟩
  exact top_unique (htop ▸ min_le_right _ _)

/-- **The first piece of a history from the root `0`** starting with an ordinary instruction `(θ, t)` is `P`-a.s.
regular (its conditional law is `P`). -/
theorem ae_pieceRegular_first (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) (hroot : spec.1 = 0) {θ : ℝ} {t : ℝ≥0∞} {rest : List Instr}
    (hp : spec.2.2 = Sum.inl (θ, t) :: rest) :
    ∀ᵐ ω ∂P, PieceRegular (E 0 ω).1 (min (instrTime spec 0) (E 0 ω).2) := by
  have ht : instrTime spec 0 = t := by simp [instrTime, hp]
  rw [ht]
  exact ae_pieceRegular_of_isFlowLineDriver h13 hκ (hS.isFlowLineDriver_first hκ hb hh hroot hp) (hS.2.2.1 0) t

/-- **Every launched piece is regular under its conditional law**: for `P`-a.e. `ω₀` at which instruction `k`
launches a piece, the piece's data are regular almost surely under `condExpKernel P (pastSigma … k) ω₀`. -/
theorem ae_condExpKernel_pieceRegular (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        PieceRegular (E k ω).1 (min (instrTime spec k) (E k ω).2) := by
  have hrec := Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 k) (hS.2.2.1 k)
  filter_upwards [hS.2.2.2 k, hrec] with ω₀ hω₀ hrecω₀ c θ hl
  obtain ⟨b', jumps', h', -, -, hfl⟩ := hω₀ c θ hl
  exact ae_pieceRegular_of_isFlowLineDriver h13 hκ hfl hrecω₀ (instrTime spec k)

/-! ### The named input and the reduction -/

/-- **Regularity of the later pieces of a staged history** (the open input): for every staged history of a GFF
with piecewise constant data (`0 < κ < 4`), every piece launched by an instruction `k > 0` has `P`-a.s. regular data
(`PieceRegular`: continuous driver up to its stop `min t_k ζ_k`, continuous generating trace, transient at an
infinite stop). Its conditional-law form is `ae_condExpKernel_pieceRegular` (proved from Theorem 1.3); the passage to
`P` is the missing step (module docstring). -/
def StagedLaterPieceRegularStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), IsStagedHistory κ b jumps P h spec E →
      ∀ k : ℕ, 0 < k → ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
        PieceRegular (E k ω).1 (min (instrTime spec k) (E k ω).2)

/-- The program of a boundary walk starts with its ordinary instruction `(θ, ⊤)`. -/
theorem boundaryWalkSpec_prog (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) :
    (boundaryWalkSpec b jumps θ right).2.2 = Sum.inl (θ, ⊤) :: (Sum.inr (Sum.inl right) ::
      (List.replicate (PiecewiseConstantBoundaryData.jumpSet b jumps).card
        [(Sum.inl (θ, ⊤) : Instr), Sum.inr (Sum.inl right)]).flatten) := by
  simp [boundaryWalkSpec, List.replicate_succ]

/-- **Every piece of a boundary walk is a.s. relatively closed in `ℍ`**, given Theorem 1.3 and the regularity of
the later pieces. -/
theorem ae_closure_tipSet_inter_H_subset_walk (h13 : Exist.Theorem13Statement.{u})
    (hL : StagedLaterPieceRegularStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) (θ : ℝ) (right : Bool) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E) :
    ∀ᵐ ω ∂P, ∀ p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun k => E k ω)
        (boundaryWalkSpec b jumps θ right).2.2.length).1,
      closure (p.1.tipSet p.2.1 p.2.2) ∩ H ⊆ p.1.tipSet p.2.1 p.2.2 := by
  have h0 := ae_pieceRegular_first h13 hκ hb hh hS rfl (boundaryWalkSpec_prog b jumps θ right)
  have hall : ∀ᵐ ω ∂P, ∀ (k : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) (k + 1)).2.2.2.1 k =
        some (c, θ') →
      PieceRegular (E k ω).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (E k ω).2) := by
    rw [ae_all_iff]
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · filter_upwards [h0] with ω hω c θ' _ using hω
    · exact hL κ hκ hκ4 b jumps hb P h hh _ E hS k hk
  filter_upwards [hall] with ω hω
  exact closure_tipSet_inter_H_subset_run _ (fun j => E j ω) hω

/-- **`SB.GW1PieceProperStatement` from Theorem 1.3 and the regularity of the later pieces.** -/
theorem gw1PieceProperStatement_of_later (h13 : Exist.Theorem13Statement.{u})
    (hL : StagedLaterPieceRegularStatement.{u}) : SB.GW1PieceProperStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' _ _ E hE
  have hθ : ∀ θ : ℝ, θ = -(Real.pi / 2) ∨ θ = Real.pi / 2 → θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rintro θ (rfl | rfl) <;> constructor <;> linarith [Real.pi_pos]
  have hR := ae_closure_tipSet_inter_H_subset_walk h13 hL hκ hκ4 hb hh (-(Real.pi / 2)) true
    (hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (hθ _ (Or.inl rfl)) true))
  have hLw := ae_closure_tipSet_inter_H_subset_walk h13 hL hκ hκ4 hb hh (Real.pi / 2) false
    (hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (hθ _ (Or.inr rfl)) false))
  filter_upwards [hR, hLw] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **GW1's properness for the walks** (`SB.GW1ProperStatement`) from Theorem 1.3 and the regularity of the later
pieces. -/
theorem gw1ProperStatement_of_later (h13 : Exist.Theorem13Statement.{u})
    (hL : StagedLaterPieceRegularStatement.{u}) : SB.GW1ProperStatement.{u} :=
  SB.gw1ProperStatement_of_pieces (gw1PieceProperStatement_of_later h13 hL)

end GW1P

end Theorem14

end InteractingSLE

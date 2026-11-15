/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2Sched
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# GW2a's later pieces: the conditional counterflow pair at a launch, and the step under the conditional law

Packet PROVE-T14-BR6. Lemma GW2a (supplement p. 623): "Use the induction datum of GW1 […] In the already established
complete conditional counterflow pair targeted at the current incoming tip, GB6 and BW1 apply to the next ordinary
piece"; Lemma GW1, induction datum 2 (p. 618): "Given this retained datum, `η[0, T_{w_j}]` has the complete
conditional counterflow kernel in `U_j` from `y` to `w_j`, with all cumulative groups greater than `−2`."

* **`HasLaunchPair`** is that datum at the launch of instruction `k`, at a sample `ω₀` of the retained past: under the
  regular conditional law `condExpKernel P (pastSigma … k) ω₀`, for every field `h'` that is the field `h` read in the
  launch chart `c`, a centred counterflow driver `Wk` of `h'` with infinite lifetime whose tips, read through `c` and
  the inversion, are physical points of the completed counterflow range of the original counterflow `W'`.
* **`ae_condExpKernel_piece_subset_of_pair`**: for a staged history whose launched pieces are regular (ruling R51's
  `StagedPiecesRegular`), at almost every `ω₀` at which the datum holds, the piece launched at `k` lies in the
  completed counterflow range under the conditional law (BR5's `GW2aPiece.ae_condExpKernel_piece_subset`, with the
  launch chart's boundary extension from the regularity of the earlier pieces, `GW1P.isClosed_pieces_run`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Later

open CounterflowRange GW2aMulti

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **GW1's induction datum 2 at the launch of instruction `k`** (supplement p. 618; GW2a p. 623: "the already
established complete conditional counterflow pair targeted at the current incoming tip"), at a sample `ω₀` of the
retained past. If instruction `k` launches a piece of `ω₀` in the chart `c`, then for every field `h'` that is `h` read
in `c`, under the conditional law given the retained past there is a centred counterflow driver `Wk` of `h'` with
infinite lifetime, and every tip of `Wk` read through `c` and the inversion `z ↦ −1/z` is a physical point of the
completed range of the original counterflow `W'`. The field `h'` is quantified universally, so it is the field of the
staged-history clause. -/
def HasLaunchPair (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω₀ : Ω) : Prop :=
  ∀ (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
    ∀ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      ∃ (Wk : ℝ≥0 → Ω → ℝ) (ζk : Ω → ℝ≥0∞),
        IsCenteredCounterflowDriver κ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' Wk ζk ∧
        (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ζk ω = ⊤) ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ∀ (r : ℝ≥0) (z : ℂ),
          (c.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z →
            z ∈ counterflowCompletedRange (fun t => W' t ω)

omit [StandardBorelSpace Ω] in
/-- **The completed counterflow range is almost surely closed** (Theorem 1.3 at `16/κ`: a continuous transient
generating trace). -/
theorem ae_isClosed_counterflowCompletedRange (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    ∀ᵐ ω ∂P, IsClosed (counterflowCompletedRange (fun t => W' t ω)) := by
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hk : 0 < 16 / κ := by positivity
  filter_upwards [GW2aSingle.ae_chosenTrace hT13 hk hfl, hζ', Supp8.GB6.ae_driver_zero_continuousOn hfl]
    with ω hγω hζω hdω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  exact isClosed_counterflowCompletedRange hγω.1 hWc hdω.1 (hγω.2 rfl)

/-- **The launch chart of a regular run has boundary limits** (`GW1P.isClosed_pieces_run` at the launch). -/
theorem hasProperBdryExt_of_launch {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (Exist.StagedLaw.instrTime spec k) (D k).2))
    {k : ℕ} {c : Chart} {θ : ℝ} (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)) :
    GW1P.HasProperBdryExt c := by
  rw [(Exist.StagedLaw.eq_launch_of_launches spec D hl).2.2]
  exact (GW1P.isClosed_pieces_run spec D hreg k).1

/-- **GW2a's step for the piece launched at `k`, under the conditional law given the retained past**, at almost every
sample `ω₀` at which the conditional counterflow pair (`HasLaunchPair`) is available. Inputs: GB6's restart law,
GW0's forward implication and Theorem 1.3 (named inputs, as in `GW2aPiece.ae_condExpKernel_piece_subset`); the
launched pieces are regular (ruling R51), which gives the launch chart's boundary limits. -/
theorem ae_condExpKernel_piece_subset_of_pair (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ)
    (hθ : ∀ (θ : ℝ) (t : ℝ≥0∞), spec.2.2[k]? = some (Sum.inl (θ, t)) → θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∀ᵐ ω₀ ∂P, HasLaunchPair κ b jumps P h W' spec E k ω₀ → ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        c.tipSet (stoppedDriver spec (fun j => E j ω) k) (pieceStop spec (fun j => E j ω) k) ⊆
          counterflowCompletedRange (fun t => W' t ω) := by
  have h𝒢 := hS.2.1 k
  filter_upwards [hS.2.2.2 k, hR.ae_pieceRegular, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 (hS.2.2.1 k),
    Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 (ae_isClosed_counterflowCompletedRange hT13 hκ hcf hζ')]
    with ω₀ hst hreg hrec hcl hpair c θ hl
  obtain ⟨b', jumps', h', hb', htr, hfl⟩ := hst c θ hl
  obtain ⟨Wk, ζk, hWk, hζk, hid⟩ := hpair c θ hl h' htr
  obtain ⟨f, -, hf, -⟩ := hasProperBdryExt_of_launch hreg hl
  have hθ' : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    hθ θ _ (Exist.StagedLaw.eq_launch_of_launches spec _ hl).1
  exact GW2aPiece.ae_condExpKernel_piece_subset hGB6 hGW0 hT13 hκ hκ4 hθ' hb' hfl hrec hWk hζk hf hcl hid

end GW2Later

end Theorem14

end InteractingSLE

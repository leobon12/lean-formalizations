/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Trace
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart

/-!
# Wang–Wu Corollary 4.13: transience of the nonnegative-weight trace, from the restart input and Zhan's input

Packet PROVE-WW-TRACE. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.4,
Corollary 4.13 (text dump L1384–L1397):

> **Corollary 4.13** (Proper non-boundary-intersecting traces). Under the hypotheses of Lemma 4.12, `γ(t) → ∞` as
> `t → ∞`.
> *Proof.* At any positive rational time `s`, every force image has strictly positive distance from the driver. …
> The mapped future `g_s(γ(s + ·)) − W_s` has the force-point SDE law with these remote images, and all its
> cumulative weights remain nonnegative. … The independent transience theorem of Zhan, External input 8.3, says that
> this mapped future tends to infinity. Apply the theorem to the conditional law for almost every marked state and
> then integrate … Hydrodynamic normalization gives `g_s⁻¹(z + W_s) = z + W_s + O(1/z)` at infinity, so the original
> future also tends to infinity.

The step "apply the theorem to the conditional law for almost every marked state and then integrate" is the restart
of the evolution at a deterministic time with its random force word. In the project it is the named open input
`Sec7.RandomRestartTraceStatement` (PROVE-SEC7-C3, `Spec/Sec7/ContinuityProb2Restart.lean`; its almost-surely-constant
case is proved there). External input 8.3 is the named hypothesis `ZhanNonboundaryTransience` (PROVE-WW-C). This
file proves Corollary 4.13 from these two inputs, and nothing else:

* every ordered word strictly separated from the start with nonnegative cumulative weights is complete
  (`LP.IsCompleteForceWord 4`): Lemma 4.12 and the input 8.3 (`isCompleteForceWord_of_separated`);
* at time `1` the force word `V_1 − W_1` of the chain is such a word almost surely (Lemma 4.12's noncollision), on an
  `𝓕_1`-measurable event (`restartEvent`);
* the restart input gives a transient generating trace of the shifted driver; joined to the trace on `[0, 1]`
  (PROVE-SEC7-C3's `IsGeneratingTraceIcc.join`, whose hydrodynamic bound transfers transience) and by uniqueness of
  generating traces it is the trace of Lemma 4.12.

## Main results

* `IsMarkedChain.ae_simple_transient_trace` (**Corollary 4.13**, conditional on the two named inputs);
* `IsMarkedChain.ae_theorem13_of_nonneg`: the conclusion of the frozen Theorem 1.3 at `κ = 4` for every ordered word
  with nonnegative cumulative weights (conditional on the two named inputs).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open QuantumZipper (H fwdHull)

variable {nL nR : ℕ}

/-- **Separated words with nonnegative cumulative weights are complete at `κ = 4`** (Lemma 4.12 and External
input 8.3). -/
theorem isCompleteForceWord_of_separated (hZ : ZhanNonboundaryTransience.{u}) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j) (hcum : HasNonnegCumWeights ρL ρR) :
    LP.IsCompleteForceWord.{u} 4 xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact (IsMarkedChain.ae_theorem13_of_separated hZ hF hxL hxR hcum hE).mono fun _ h => h.2

section Chain

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The **restart event at time `1`**: the chain is alive at time `1`, and its force word at time `1` is ordered and
strictly separated from the driver (written with the killed coordinates, which are `𝓕_1`-measurable). -/
def restartEvent (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω} ∩
    {ω | (∀ i, killedProc ζ (VL i) 1 ω < killedProc ζ W 1 ω) ∧
      (∀ j, killedProc ζ W 1 ω < killedProc ζ (VR j) 1 ω) ∧
      (∀ i j : Fin nL, i ≤ j → killedProc ζ (VL j) 1 ω ≤ killedProc ζ (VL i) 1 ω) ∧
      (∀ i j : Fin nR, i ≤ j → killedProc ζ (VR i) 1 ω ≤ killedProc ζ (VR j) 1 ω)}

theorem measurableSet_restartEvent (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    MeasurableSet[𝓕 1] (restartEvent W VL VR ζ) := by
  obtain ⟨-, hW, hVL, hVR, -⟩ := hE
  have hζ : MeasurableSet[𝓕 1] {ω | ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω} := by
    simpa using hW 1 univ MeasurableSet.univ
  have mW := measurable_killedProc hW 1
  have mL := fun i => measurable_killedProc (hVL i) 1
  have mR := fun j => measurable_killedProc (hVR j) 1
  refine hζ.inter ?_
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine ((MeasurableSet.iInter fun i => measurableSet_lt (mL i) mW).inter
    ((MeasurableSet.iInter fun j => measurableSet_lt mW (mR j)).inter
      ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_).inter
        (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_))))
  · by_cases hij : i ≤ j
    · simpa [hij] using measurableSet_le (mL j) (mL i)
    · simp [hij]
  · by_cases hij : i ≤ j
    · simpa [hij] using measurableSet_le (mR i) (mR j)
    · simp [hij]

/-- **Corollary 4.13** (proper non-boundary-intersecting traces), from the restart input
`Sec7.RandomRestartTraceStatement 4` and External input 8.3 (`ZhanNonboundaryTransience`): under the hypotheses of
Lemma 4.12, almost surely the simple trace of Lemma 4.12 also satisfies `γ(t) → ∞`. -/
theorem IsMarkedChain.ae_simple_transient_trace (hR : Sec7.RandomRestartTraceStatement.{u} 4)
    (hZ : ZhanNonboundaryTransience.{u}) (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ Function.Injective η ∧
        (∀ t, 0 < t → η t ∈ H) ∧
        (∀ t : ℝ≥0, fwdHull (fun s : ℝ => W s.toNNReal ω) t = η '' Ioc 0 t) ∧
        Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hT := isStoppingTime_const 𝓕 (1 : ℝ≥0)
  have hAm : MeasurableSet[hT.measurableSpace] (restartEvent W VL VR ζ) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurableSet_restartEvent hE
  have hkill : ∀ {X : ℝ≥0 → Ω → ℝ} {ω : Ω}, ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω →
      killedProc ζ X 1 ω = X 1 ω := fun h => by simp only [killedProc, h, ↓reduceIte]
  have hrest := hR xL xR ρL ρR P 𝓕 W VL VR B ζ hE (fun _ => 1) hT (restartEvent W VL VR ζ) hAm
    (fun ω hω => hω.1) fun ω hω => by
      obtain ⟨h1, hsL, hsR, haL, haR⟩ := hω
      simp only [hkill h1] at hsL hsR haL haR
      refine isCompleteForceWord_of_separated hZ ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_,
        fun j => ?_⟩ (fun i => ?_) (fun j => ?_) hcum
      · show VL j 1 ω - W 1 ω ≤ VL i 1 ω - W 1 ω
        linarith [haL i j hij]
      · show VL i 1 ω - W 1 ω ≤ 0
        linarith [hsL i]
      · show VR i 1 ω - W 1 ω ≤ VR j 1 ω - W 1 ω
        linarith [haR i j hij]
      · show 0 ≤ VR j 1 ω - W 1 ω
        linarith [hsR j]
      · show VL i 1 ω - W 1 ω < 0
        linarith [hsL i]
      · show 0 < VR j 1 ω - W 1 ω
        linarith [hsR j]
  filter_upwards [hE.ae_simple_trace hF hcum, hrest, hE.2.2.2.2] with ω
    ⟨hζ, hsep, η, hη, hinj, hH, hhull⟩ hrω hp
  have hη' : IsGeneratingTrace (fun t => W t ω) ⊤ η := hη
  refine ⟨hζ, hsep, η, hη', hinj, hH, hhull, ?_⟩
  have h1 : ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hmem : ω ∈ restartEvent W VL VR ζ := by
    refine ⟨h1, ?_⟩
    simp only [Set.mem_ofPred_eq, hkill h1]
    obtain ⟨hsL, hsR⟩ := hsep 1 one_pos
    have hlt : ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω := h1
    exact ⟨hsL, hsR, fun i j hij => hp.isForcePath.antitone_vL hlt hij,
      fun i j hij => hp.isForcePath.monotone_vR hlt hij⟩
  obtain ⟨η₂, hη₂, htr₂⟩ := hrω hmem
  have hζ1 : ζ ω - ((1 : ℝ≥0) : ℝ≥0∞) = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
  rw [hζ1] at hη₂
  have hwc : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} := by
    have := hp.2.2.2.1; rwa [hζ] at this
  have hw0 : (fun t => W t ω) 0 = 0 := hp.1
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη' hwc hw0 (σ := 1) ENNReal.coe_lt_top
  have hwc' : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) + ⊤} := by
    rwa [add_top]
  obtain ⟨hjoin, htj⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have heq : ∀ t : ℝ≥0, η t = Sec7.joinTrace (fun t => W t ω) 1 η η₂ t := fun t =>
    hη'.eq_of_le hjoin hwc hw0 le_top
  have ht := htj rfl (htr₂ hζ1)
  refine ht.congr fun t => ?_
  rw [heq t]

/-- **The conclusion of the frozen Theorem 1.3 at `κ = 4`** for every ordered word with nonnegative cumulative
weights (marks at `0±` allowed), from the restart input and External input 8.3: almost surely the threshold clause
holds, the chain has a generating trace on `[0, ζ]`, and it is transient when `ζ = ∞`. -/
theorem IsMarkedChain.ae_theorem13_of_nonneg (hR : Sec7.RandomRestartTraceStatement.{u} 4)
    (hZ : ZhanNonboundaryTransience.{u}) (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  filter_upwards [hE.ae_simple_transient_trace hR hZ hF hcum] with ω
    ⟨hζ, _, η, hη, _, _, _, htend⟩
  exact ⟨fun hth => absurd hth (hcum.not_thresholdCondition_zero hF), η, hζ ▸ hη, fun _ => htend⟩

end Chain

end InteractingSLE.WangWu

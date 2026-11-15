/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContStepAux

/-!
# Lemma GW2a for every program: GW1's inductive step at a launch

Packet PROVE-GW2AC. Lemma GW2a, proof (supplement p. 623): "In the already established complete conditional
counterflow pair targeted at the current incoming tip, GB6 and BW1 apply to the next ordinary piece because its angle is
in the displayed interval. They identify its full actual precontact law." At a sample `ω₀` at which GW1's datum holds
before an instruction that launches a piece, let `ν` be the regular conditional law given the retained past. Under `ν`
the piece is a flow line of the field `h_j` read in the launch chart `c` (`IsStagedHistory`), and the datum gives the
centred counterflow `W_k` of `h_j`. For `ν`-almost every sample `ω`:

* if the piece of `ω` stops at `⊤`, the history is done and there is nothing to prove;
* if it stops at `0` (zero lifetime, or own time `0`), the chart does not change, and the regular conditional law given
  the retained past one instruction later is `ν` again (the record is almost surely constant, because the lifetime is
  zero almost surely or almost never, `ae_lifetime_eq_zero_or_ne`); the datum is inherited;
* at a finite positive stop, GB6 (an interior tip before the lifetime, `GW2Later.GB6PrefixPairStatement`) or BW1 (a
  real endpoint or a threshold, `BW1PrefixPairStatement`), applied in the world `ν` with the last record of the retained
  past, gives the pair for the field read in the new chart `c.loewner U T` — through the composition of chart
  transports, the identification of the conditional law given the last record with the regular conditional law given
  the longer retained past (`ae_ae_condExpKernel_succ_eq`), and the composition of tips
  (`GW2Later.mem_of_tipAt_loewner_trans`).

Main result: **`ae_hasStatePair_succ_of_launch`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aCont

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### Records and charts at a zero stop -/

theorem recOf_of_stop_zero {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : e.1 0 = 0) (h0 : min t e.2 = 0) :
    recOf t e = readRec (fun _ => 0, 0, decide (e.2 ≤ t)) := by
  have h1 : (fun r : ℝ≥0 => e.1 (min (r : ℝ≥0∞) (min t e.2)).toNNReal) = fun _ => 0 := by
    funext r
    rw [h0, min_eq_right zero_le, ENNReal.toNNReal_zero, he]
  unfold recOf retOf
  rw [h1, h0]

theorem stopDrv_of_stop_zero {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : e.1 0 = 0) (h0 : min t e.2 = 0) :
    stopDrv t e = fun _ => 0 := by
  funext x
  simp only [stopDrv, retOf, h0, min_eq_right zero_le, ENNReal.toNNReal_zero, he]

theorem stopTime_of_stop_zero {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (h0 : min t e.2 = 0) : stopTime t e = 0 := by
  simp only [stopTime, h0, ENNReal.toNNReal_zero, NNReal.coe_zero]

/-- The chart after a launch with a finite stop, in the notation of the records. -/
theorem chart_launch_eq (s : ExplState) (k : ℕ) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (h : min t e.2 ≠ ⊤) :
    (ExplState.launch s k e θ t).2.2.2.2.1 = s.2.2.2.2.1.loewner (stopDrv t e) (stopTime t e) :=
  chart_launch s k e θ t h

/-! ### The step at a launch -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
theorem min_eq_zero_cases {t ζ : ℝ≥0∞} (h : min t ζ = 0) : t = 0 ∨ ζ = 0 := by
  rcases le_total t ζ with hle | hle
  · rw [min_eq_left hle] at h; exact Or.inl h
  · rw [min_eq_right hle] at h; exact Or.inr h

/-- **At a zero stop the regular conditional law one instruction later is the current one.** Under
`ν = condExpKernel P (pastSigma j) ω₀`, where instruction `j` launches a flow line `E j` of `ν`, the last record is
almost surely constant on the event of a zero stop (the lifetime is zero almost surely or almost never). -/
theorem ae_condExpKernel_succ_eq_of_stop_zero {P : Measure Ω} [IsProbabilityMeasure P] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hle : ∀ k, pastSigma κ b jumps spec E k ≤ mΩ)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {j : ℕ} {t : ℝ≥0∞} {ω₀ : Ω}
    (hK : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
      condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
          (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω =
        condExpKernel P (pastSigma κ b jumps spec E (j + 1)) ω)
    (hgν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
      lastRec κ b jumps spec E j ω = recOf t (E j ω))
    (hz : (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀), (E j ω).2 = 0) ∨
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀), (E j ω).2 ≠ 0) :
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀), min t (E j ω).2 = 0 →
      condExpKernel P (pastSigma κ b jumps spec E (j + 1)) ω = condExpKernel P (pastSigma κ b jumps spec E j) ω₀ := by
  have hgm := measurable_lastRec hle j
  have hconst : ∀ r₀ : RecData, (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
      lastRec κ b jumps spec E j ω = r₀) → ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
        condExpKernel P (pastSigma κ b jumps spec E (j + 1)) ω = condExpKernel P (pastSigma κ b jumps spec E j) ω₀ :=
    fun r₀ hr₀ => by
      filter_upwards [hK, ae_condExpKernel_comap_eq_self hgm hr₀] with ω h1 h2
      rw [← h1, h2]
  rcases hz with hz | hz
  · have hc : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
        lastRec κ b jumps spec E j ω = readRec (fun _ => 0, 0, true) := by
      filter_upwards [hgν, hz] with ω h1 h2
      have h0 : min t (E j ω).2 = 0 := by rw [h2]; exact min_eq_right zero_le
      rw [h1, recOf_of_stop_zero (hreg j ω).2.1 h0, h2]
      simp
    filter_upwards [hconst _ hc] with ω h _ using h
  · by_cases ht0 : t = 0
    · have hc : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
          lastRec κ b jumps spec E j ω = readRec (fun _ => 0, 0, false) := by
        filter_upwards [hgν, hz] with ω h1 h2
        have h0 : min t (E j ω).2 = 0 := by rw [ht0]; exact min_eq_left zero_le
        rw [h1, recOf_of_stop_zero (hreg j ω).2.1 h0, ht0]
        have : ¬ (E j ω).2 ≤ 0 := fun h => h2 (le_antisymm h zero_le)
        simp [this]
      filter_upwards [hconst _ hc] with ω h _ using h
    · filter_upwards [hz] with ω h2 h0
      exact ((min_eq_zero_cases h0).elim (fun h => absurd h ht0) fun h => absurd h h2)

/-- **GW1's inductive step at a launch** (module docstring). For a staged history with measurable drivers regular at
every sample whose pieces are almost surely regular (ruling R51) and whose ordinary angles lie in `[−π/2, π/2]`: at
almost every `ω₀` at which GW1's datum holds after `j` instructions and instruction `j` launches its piece (in every
history that has the state of `ω₀`), almost surely under the regular conditional law given the retained past the datum
holds after `j + 1` instructions. Named inputs: GB6 (`GW2Later.GB6PrefixPairStatement`), BW1
(`BW1PrefixPairStatement`), Theorem 1.3. -/
theorem ae_hasStatePair_succ_of_launch (hG : GB6PrefixPairStatement.{u}) (hBW1 : BW1PrefixPairStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {spec : ExplSpec}
    (hθs : ∀ (k : ℕ) (θ : ℝ) (t : ℝ≥0∞), spec.2.2[k]? = some (Sum.inl (θ, t)) →
      θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (j : ℕ) :
    ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' spec E j ω₀ → ∀ (θ : ℝ) (t : ℝ≥0∞),
      spec.2.2[j]? = some (Sum.inl (θ, t)) →
      (∀ D, ExplState.run κ b jumps spec D j = ExplState.run κ b jumps spec (fun i => E i ω₀) j →
        ExplState.run κ b jumps spec D (j + 1) =
          ExplState.launch (ExplState.run κ b jumps spec (fun i => E i ω₀) j) j (D j) θ t) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀), HasStatePair κ b jumps P h W' spec E (j + 1) ω := by
  have hle := hS.2.1
  have hEm := hS.1
  filter_upwards [hS.2.2.2 j, hR.ae_pieceRegular,
    ae_ae_run_eq runMeasStatement hb spec (fun i _ => hEm i) (fun i _ => hreg i) (k := j) (P := P),
    ae_ae_condExpKernel_succ_eq hle j,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hle j) hR.ae_pieceRegular,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hle j) (Sec7.Aux122Disint.ae_ae_condExpKernel (hle (j + 1))
      (ae_isClosed_counterflowCompletedRange hT13 hκ hcf hζ'))]
    with ω₀ hst hreg0 hrun hK hregν hclν hD θ t hj hlaunch
  have hinstr : instrTime spec j = t := by simp only [instrTime, hj]
  have hl0 : (ExplState.run κ b jumps spec (fun i => E i ω₀) (j + 1)).2.2.2.1 j =
      some ((ExplState.run κ b jumps spec (fun i => E i ω₀) j).2.2.2.2.1, θ) := by
    rw [hlaunch _ rfl, launches_launch, Function.update_self]
  have hterm := not_isTerminal_of_launch hl0
  obtain ⟨b', J', hj', hb', htrj, hfl⟩ := hst _ _ hl0
  obtain ⟨Wk, ζk, hWk, hζk, hidk⟩ := hD hterm hj' htrj
  have hθ := hθs j θ t hj
  have hconf := isConformal_runChart spec (fun i => E i ω₀) j fun i _ => hreg0 i
  have hext : GW1P.HasProperBdryExt (ExplState.run κ b jumps spec (fun i => E i ω₀) j).2.2.2.2.1 :=
    hasProperBdryExt_of_launch hreg0 hl0
  have hhj := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  have hgm : Measurable (lastRec κ b jumps spec E j) := measurable_lastRec hle j
  have hlaunchω : ∀ ω, ExplState.run κ b jumps spec (fun i => E i ω) j =
      ExplState.run κ b jumps spec (fun i => E i ω₀) j →
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j =
        some ((ExplState.run κ b jumps spec (fun i => E i ω₀) j).2.2.2.2.1, θ) := fun ω hω => by
    rw [hlaunch _ hω, launches_launch, Function.update_self]
  have hgν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀),
      lastRec κ b jumps spec E j ω = recOf t ((fun s => (E j ω).1 s), (E j ω).2) := by
    filter_upwards [hrun] with ω hω
    rw [lastRec_of_launch spec E j (by rw [hlaunchω ω hω]; exact Option.some_ne_none _), hinstr]
  have hBν := hBW1 κ hκ hκ4 θ hθ b' J' hb' _ hj' hhj Wk ζk hWk hζk _ _ hfl t _ hgm hgν
  have hGν : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀), t ≠ ⊤ → t < (E j ω).2 →
      IsInteriorStop (fun s => (E j ω).1 s) t →
      ∀ h₂ : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω', IsChartTransport (Chart.id.loewner (stopDrv t ((fun s => (E j ω).1 s), (E j ω).2))
          (stopTime t ((fun s => (E j ω).1 s), (E j ω).2))) 1 0 (QuantumZipper.chiC κ) (hj' ω') (h₂ ω')) →
        ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞),
          IsCenteredCounterflowDriver κ (condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
            (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω) h₂ W₂ ζ₂ ∧
          (∀ᵐ ω' ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
            (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω), ζ₂ ω' = ⊤) ∧
          ∀ᵐ ω' ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
            (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω), ∀ (r : ℝ≥0) (z : ℂ),
            ((Chart.id.loewner (stopDrv t ((fun s => (E j ω).1 s), (E j ω).2))
              (stopTime t ((fun s => (E j ω).1 s), (E j ω).2))).trans infinitySourceChart).tipAt
                (fun s => W₂ s ω') r z →
              z ∈ counterflowCompletedRange (fun s => Wk s ω') := by
    by_cases ht : t = ⊤
    · exact Eventually.of_forall fun ω h => absurd ht h
    · filter_upwards [hG κ hκ hκ4 θ hθ b' J' hb' _ hj' hhj Wk ζk hWk hζk _ _ hfl t ht _ hgm hgν] with ω hω _
      exact hω
  have hzero := ae_condExpKernel_succ_eq_of_stop_zero hle hreg hK hgν (ae_lifetime_eq_zero_or_ne hfl)
  have hlift := KernelTower.ae_ae_condExpKernel_of_ae (P := condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
    (m := MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) hgm.comap_le
    ((GW2Later.ae_counterflow_regular hT13 hκ hWk hζk).and hidk)
  filter_upwards [hrun, hK, hregν, hclν, hBν, hGν, hzero, hlift] with ω hω hKω hregω hclω hBω hGω hzω hliftω
  intro hlive h'' htr''
  have hs1 := hlaunch _ hω
  have hrω := hregω j _ _ (hlaunchω ω hω)
  rw [hinstr] at hrω
  rw [hs1] at hlive htr'' ⊢
  by_cases htop : min t (E j ω).2 = ⊤
  · exact absurd (isTerminal_launch_of_top _ _ _ _ _ htop) hlive
  rw [chart_launch_eq _ _ _ _ _ htop] at htr'' ⊢
  by_cases h0 : min t (E j ω).2 = 0
  · -- a zero stop: the chart and the conditional law do not change
    have he0 : (E j ω).1 0 = 0 := (hreg j ω).2.1
    rw [stopDrv_of_stop_zero he0 h0, stopTime_of_stop_zero h0] at htr'' ⊢
    have htr0 : ∀ ω', IsChartTransport (ExplState.run κ b jumps spec (fun i => E i ω₀) j).2.2.2.2.1 1 0
        (QuantumZipper.chiC κ) (h ω') (h'' ω') := fun ω' =>
      (isChartTransport_loewner_zero_iff (W := fun _ => 0) continuous_const rfl).1 (htr'' ω')
    obtain ⟨W₂, ζ₂, hW₂, hζ₂, hid₂⟩ := hD hterm h'' htr0
    rw [hzω h0]
    refine ⟨W₂, ζ₂, hW₂, hζ₂, hid₂.mono fun ω' hω' r z hz => hω' r z ?_⟩
    exact (tipAt_loewner_zero_iff (W := fun _ => 0) continuous_const rfl).1 hz
  -- a finite positive stop: GB6 or BW1 in the conditional world
  have hpos : 0 < min t (E j ω).2 := pos_iff_ne_zero.2 h0
  have hU : Continuous (stopDrv t (E j ω)) := hrω.continuous_stoppedReal.1
  have hU0 : stopDrv t (E j ω) 0 = 0 := hrω.continuous_stoppedReal.2
  have hT : 0 ≤ stopTime t (E j ω) := NNReal.coe_nonneg _
  have hc₂ := Chart.isConformal_id.loewner hU hU0 hT
  have hℓ₂ := hc₂.continuousOn_lift_inv (Chart.continuousOn_lift_loewner hU hU0 hT)
  have htr₂ : ∀ ω', IsChartTransport (Chart.id.loewner (stopDrv t (E j ω)) (stopTime t (E j ω))) 1 0
      (QuantumZipper.chiC κ) (hj' ω') (h'' ω') := fun ω' =>
    IsChartTransport.of_trans hconf.1 hc₂ hconf.2 hℓ₂ (htrj ω') (by rw [← Chart.loewner_eq_trans]; exact htr'' ω')
  have hpair : ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ (condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
        (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω) h'' W₂ ζ₂ ∧
      (∀ᵐ ω' ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
        (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω), ζ₂ ω' = ⊤) ∧
      ∀ᵐ ω' ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps spec E j) ω₀)
        (MeasurableSpace.comap (lastRec κ b jumps spec E j) inferInstance) ω), ∀ (r : ℝ≥0) (z : ℂ),
        ((Chart.id.loewner (stopDrv t (E j ω)) (stopTime t (E j ω))).trans infinitySourceChart).tipAt
          (fun s => W₂ s ω') r z → z ∈ counterflowCompletedRange (fun s => Wk s ω') := by
    by_cases hgb : t < (E j ω).2 ∧ IsInteriorStop (fun s => (E j ω).1 s) t
    · exact hGω (ne_top_of_lt hgb.1) hgb.1 hgb.2 h'' htr₂
    · refine hBω hpos htop ?_ h'' htr₂
      by_cases hlt : t < (E j ω).2
      · right
        rw [min_eq_left hlt.le]
        exact fun hi => hgb ⟨hlt, hi⟩
      · exact Or.inl (not_lt.1 hlt)
  obtain ⟨W₂, ζ₂, hW₂, hζ₂, hid₂⟩ := hpair
  rw [hKω] at hW₂ hζ₂ hid₂ hliftω
  refine ⟨W₂, ζ₂, hW₂, hζ₂, ?_⟩
  have hB : HasBdryLimits (fwdMapInv (stopDrv t (E j ω)) (stopTime t (E j ω))) := hrω.hasBdryLimits htop
  filter_upwards [hid₂, GW2Later.ae_counterflow_regular hT13 hκ hW₂ hζ₂, hliftω, hclω]
    with ω' hid₂ω hreg₂ω hlω' hclω'
  obtain ⟨γ₂, hγ₂, hW₂c, hW₂0, -⟩ := hreg₂ω
  obtain ⟨⟨γk, hγk, hWkc, hWk0, htrk⟩, hidkω⟩ := hlω'
  intro r z hz
  exact mem_of_tipAt_loewner_trans hext hU hU0 hT hB hγk hWkc hWk0 htrk hclω' hidkω hγ₂ hW₂c hW₂0 hid₂ω r z hz

end GW2aCont

end Theorem14

end InteractingSLE

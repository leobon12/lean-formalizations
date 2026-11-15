/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2LaterChain
import InteractingSLE.Spec.Supplement.KernelTower2

/-!
# GW1's inductive step from GB6 conditioned on the piece's own prefix: the statement and the deterministic part

Packet PROVE-T14-BR7. GW1's inductive step (`GW2Later.GB6PastStepStatement`, supplement pp. 618–620, 623) is GB6
applied in the conditional world of the retained past, to the piece launched next, together with the tower property.
This file states GB6 in the form the step needs, for one flow line in an arbitrary probability space, and proves the
deterministic facts the reduction uses; `GB6PastStep.lean` proves the step from it.

* **`GB6PrefixPairStatement`** (named input): Proposition GB6's conditional-law half (supplement §8.6, pp. 518–520:
  "Conditional on the marked prefix, the portion of `η` before its first contact with `α[0, σ]`, in the chart of `U`
  taking `(y, p)` to `(0, ∞)`, is the complete canonical counterflow of the conditional component field. Its relative
  lifetime is infinite"), for a flow line `α` of `h` with angle in `[−π/2, π/2]` stopped at a deterministic own time `s`
  before its lifetime with an interior tip, conditioning on (any measurable version of) the record of the stopped
  prefix: the field read in the flow's own chart at `s` has a centred counterflow with infinite lifetime whose physical
  tips, read in the original chart, are points of the completed range of `η`. It differs from the landed
  `Supp8.GB6.GB6RestartStatement` in conditioning on the prefix itself instead of the boundary word `β` only (the
  restart statement asserts the conditional law of the restart variable given `β`; it does not assert that the law
  given the whole prefix depends on the prefix only through `β`, which is what the staged induction consumes).
* `Chart.tipAt_unique`, `image_counterflowCompletedRange_subset`, **`mem_of_tipAt_loewner_trans`**: a counterflow read
  through a composed chart `c₀ ∘ f_T⁻¹` whose tips (read through `f_T⁻¹`) lie on another counterflow, whose own tips
  (read through `c₀`) lie in a closed set `R`, has its tips (read through the composed chart) in `R`.
* `isConformal_succChart`, `continuousOn_lift_succChart`: the run charts of a GW2 schedule after successful regular
  pieces are conformal with continuous lifts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Later

open CounterflowRange GW2Schedule GW2aMulti GW2Sched Exist.StagedLaw

/-- **Named input: Proposition GB6 conditional on the flow's own marked prefix** (supplement §8.6, pp. 518–520), in the
original flow chart `(ℍ, 0, ∞)`. For `0 < κ < 4`, a GFF `h` with piecewise-constant data `b`, its centred counterflow
`W` with almost surely infinite lifetime ("its complete continuous transient trace and its universal marked field
coupling"), an angle-`θ` flow line `Wα` of `h` (`θ ∈ [−π/2, π/2]`), a deterministic own time `s < ∞`, and a measurable
version `g` of the record of the prefix stopped at `s`: for almost every `ω` at which `s` is before the lifetime of
`Wα` and the tip `p = α(s)` is interior, every field `h₂` that is `h` read in the flow's own Loewner chart at `s`
(taking `p` to `0`) has, under the regular conditional law given the prefix, a centred counterflow driver `W₂` with
almost surely infinite lifetime ("the complete canonical counterflow of the conditional component field. Its relative
lifetime is infinite"), and almost surely every physical tip of `W₂`, read back through the flow chart and the
inversion, is a point of the completed range of `W` ("the portion of `η` before its first contact with `α[0, σ]`"). -/
def GB6PrefixPairStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ, θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) →
  ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q h b jumps →
  ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ Q h W ζ → (∀ᵐ ω ∂Q, ζ ω = ⊤) →
  ∀ (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞), IsFlowLineDriver κ b jumps θ Q h Wα ζα →
  ∀ s : ℝ≥0∞, s ≠ ⊤ → ∀ g : Ω → RecData, Measurable g →
    (∀ᵐ ω ∂Q, g ω = recOf s ((fun t => Wα t ω), ζα ω)) →
    ∀ᵐ ω ∂Q, s < ζα ω → IsInteriorStop (fun t => Wα t ω) s →
      ∀ h₂ : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω', IsChartTransport (Chart.id.loewner (stopDrv s ((fun t => Wα t ω), ζα ω))
          (stopTime s ((fun t => Wα t ω), ζα ω))) 1 0 (QuantumZipper.chiC κ) (h ω') (h₂ ω')) →
        ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞),
          IsCenteredCounterflowDriver κ (condExpKernel Q (MeasurableSpace.comap g inferInstance) ω) h₂ W₂ ζ₂ ∧
          (∀ᵐ ω' ∂(condExpKernel Q (MeasurableSpace.comap g inferInstance) ω), ζ₂ ω' = ⊤) ∧
          ∀ᵐ ω' ∂(condExpKernel Q (MeasurableSpace.comap g inferInstance) ω), ∀ (r : ℝ≥0) (z : ℂ),
            ((Chart.id.loewner (stopDrv s ((fun t => Wα t ω), ζα ω))
              (stopTime s ((fun t => Wα t ω), ζα ω))).trans infinitySourceChart).tipAt
                (fun t => W₂ t ω') r z →
              z ∈ counterflowCompletedRange (fun t => W t ω')

/-! ### Tips read through a composed chart -/

/-- A physical tip is unique (a limit along `y ↓ 0`). -/
theorem _root_.InteractingSLE.Chart.tipAt_unique {c : Chart} {W : ℝ≥0 → ℝ} {r : ℝ≥0} {z z' : ℂ}
    (h : c.tipAt W r z) (h' : c.tipAt W r z') : z = z' :=
  tendsto_nhds_unique h h'

/-- **The boundary-limit map of a chart sends the completed range of a counterflow into every closed set containing the
counterflow's tips read through the chart** (the endpoint `0` by transience and continuity of the boundary map). -/
theorem image_counterflowCompletedRange_subset {c : Chart} {f : ℂ → ℂ}
    (hc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun r => ‖γ r‖) atTop atTop) {R : Set ℂ} (hR : IsClosed R)
    (hid : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt W r z → z ∈ R) :
    ∀ p ∈ counterflowCompletedRange W, f p ∈ R := by
  have hpt : ∀ r : ℝ≥0, γ r ≠ 0 → f (-(γ r)⁻¹) ∈ R := fun r hr =>
    hid r _ (GW2aPiece.tipAt_trans_of_ne_zero hc hγ hW hW0 hr)
  have hf0 : f 0 ∈ R := by
    have hfc := GW1P.continuousOn_of_tendsto hc
    have h0 : Tendsto (fun r => -(γ r)⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : Tendsto (fun r => ‖γ r‖⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp htr
      simpa only [norm_neg, norm_inv] using h1
    have hne : ∀ᶠ r in atTop, γ r ≠ 0 :=
      (htr.eventually (eventually_gt_atTop 0)).mono fun r hr => norm_pos_iff.1 hr
    have hmem : ∀ᶠ r in atTop, -(γ r)⁻¹ ∈ Hbar :=
      Eventually.of_forall fun r => GW2aPiece.neg_inv_mem_Hbar (GW2aPiece.trace_mem_Hbar hγ hW hW0 r)
    have h00 : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
    have hlim : Tendsto (fun r => f (-(γ r)⁻¹)) atTop (𝓝 (f 0)) :=
      (hfc 0 h00).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h0, hmem⟩)
    exact hR.mem_of_tendsto hlim (hne.mono fun r hr => hpt r hr)
  intro p hp
  rcases hp with hp | hp0
  · rw [tipSet_infinitySourceChart_top hγ hW hW0] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact hpt r hr
  · rw [mem_singleton_iff.1 hp0]
    exact hf0

/-- A boundary-limit map agrees with the map at interior points. -/
theorem eq_of_tendsto_nhdsWithin_H {g f : ℂ → ℂ} {w : ℂ} (hw : w ∈ H) (h : Tendsto g (𝓝[H] w) (𝓝 (f w))) :
    g w = f w :=
  tendsto_nhds_unique (tendsto_pure_nhds g w) (h.mono_left (pure_le_nhdsWithin hw))

/-- **Tips through a composed chart** (GW1's induction, p. 620: the conditional counterflow of the next piece, targeted
at the new tip, lies in the conditional counterflow range of the previous one, and so in the original range). Let `c₀`
be a good chart, `f_T⁻¹` the inverse Loewner map of a continuous driver `U` at time `T` with boundary limits, `Wk` a
counterflow driver with a continuous transient trace whose tips read through `c₀` lie in a closed set `R`, and `W₂` a
counterflow driver with a continuous trace whose tips read through `f_T⁻¹` lie in the completed range of `Wk`. Then
every tip of `W₂` read through `c₀.loewner U T` lies in `R`. -/
theorem mem_of_tipAt_loewner_trans {c₀ : Chart} (hc₀ : GW1P.HasProperBdryExt c₀) {U : ℝ → ℝ} (hU : Continuous U)
    (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hB : HasBdryLimits (fwdMapInv U T))
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hγk : IsGeneratingTrace Wk ⊤ γk) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (htrk : Tendsto (fun r => ‖γk r‖) atTop atTop) {R : Set ℂ} (hR : IsClosed R)
    (hid : ∀ (r : ℝ≥0) (z : ℂ), (c₀.trans infinitySourceChart).tipAt Wk r z → z ∈ R)
    {W₂ : ℝ≥0 → ℝ} {γ₂ : ℝ≥0 → ℂ} (hγ₂ : IsGeneratingTrace W₂ ⊤ γ₂) (hW₂ : Continuous W₂) (hW₂0 : W₂ 0 = 0)
    (hin : ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner U T).trans infinitySourceChart).tipAt W₂ r z →
      z ∈ counterflowCompletedRange Wk) :
    ∀ (r : ℝ≥0) (z : ℂ), ((c₀.loewner U T).trans infinitySourceChart).tipAt W₂ r z → z ∈ R := by
  have hext := hc₀.loewner hU hU0 hT hB
  obtain ⟨f₀, -, hf₀, -⟩ := hc₀
  have hFH : ∀ z ∈ H, fwdMapInv U T z ∈ H := fun z hz => QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hT hz
  have hFmem : ∀ p ∈ Hbar, extendFrom H (fwdMapInv U T) p ∈ Hbar := fun p hp =>
    GW1P.mem_Hbar_of_tendsto hp hFH (hB.tendsto hp)
  have hcF : ∀ p ∈ Hbar, Tendsto (Chart.id.loewner U T).2.1 (𝓝[H] p)
      (𝓝 (extendFrom H (fwdMapInv U T) p)) := fun p hp => hB.tendsto hp
  have hcc : ∀ p ∈ Hbar, Tendsto (c₀.loewner U T).2.1 (𝓝[H] p)
      (𝓝 (f₀ (extendFrom H (fwdMapInv U T) p))) := fun p hp =>
    tendsto_loewner_inv hU hU0 hT (hB.tendsto hp) (hf₀ _ (hFmem p hp))
  have himg := image_counterflowCompletedRange_subset hf₀ hγk hWk hWk0 htrk hR hid
  intro r z hz
  by_cases hr : γ₂ r = 0
  · exfalso
    obtain ⟨f, C, hf, hC⟩ := hext
    have hU₂ : Continuous fun s : ℝ => W₂ s.toNNReal := hW₂.comp continuous_real_toNNReal
    have hU₂0 : (fun s : ℝ => W₂ s.toNNReal) 0 = 0 := by simpa using hW₂0
    have hF := hγ₂.tendsto_fwdMapInv_mul_I hW₂.continuousOn hW₂0 (ENNReal.coe_lt_top (r := r))
    rw [hr] at hF
    set a : ℝ → ℂ := fun y => -(fwdMapInv (fun s : ℝ => W₂ s.toNNReal) r ((y : ℂ) * Complex.I))⁻¹ with ha
    have hmemH : ∀ y : ℝ, 0 < y → fwdMapInv (fun s : ℝ => W₂ s.toNNReal) r ((y : ℂ) * Complex.I) ∈ H :=
      fun y hy => QuantumZipper.RS.fwdMapInv_mem_H hU₂ hU₂0 (NNReal.coe_nonneg r)
        (show 0 < ((y : ℂ) * Complex.I).im by simpa using hy)
    have haH : ∀ y : ℝ, 0 < y → a y ∈ H := fun y hy => GW2aPiece.neg_inv_mem_H (hmemH y hy)
    have hnorm0 : Tendsto (fun y : ℝ => ‖fwdMapInv (fun s : ℝ => W₂ s.toNNReal) r ((y : ℂ) * Complex.I)‖)
        (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using hF.norm
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact norm_pos_iff.2 (fun h0 => by
          have := hmemH y hy
          rw [h0] at this
          exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)))
    have hanorm : Tendsto (fun y => ‖a y‖) (𝓝[>] 0) atTop := by
      have := tendsto_inv_nhdsGT_zero.comp hnorm0
      refine this.congr fun y => ?_
      simp only [Function.comp_apply, ha, norm_neg, norm_inv]
    have hval : ∀ y : ℝ, 0 < y → (c₀.loewner U T).2.1 (a y) = f (a y) := fun y hy =>
      eq_of_tendsto_nhdsWithin_H (haH y hy) (hf _ (QuantumZipper.H_subset_Hbar (haH y hy)))
    have hbig : Tendsto (fun y => ‖(c₀.loewner U T).2.1 (a y)‖) (𝓝[>] 0) atTop := by
      refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C) hanorm)
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [hval y hy]
      have h1 := hC (a y) (QuantumZipper.H_subset_Hbar (haH y hy))
      have h2 : ‖a y‖ ≤ ‖f (a y)‖ + ‖f (a y) - a y‖ := by
        calc ‖a y‖ = ‖f (a y) - (f (a y) - a y)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖f (a y)‖ + ‖f (a y) - a y‖ := norm_sub_le _ _
      linarith
    exact not_tendsto_atTop_of_tendsto_nhds hz.norm hbig
  · have h1 := GW2aPiece.tipAt_trans_of_ne_zero hcc hγ₂ hW₂ hW₂0 hr
    have h2 := GW2aPiece.tipAt_trans_of_ne_zero hcF hγ₂ hW₂ hW₂0 hr
    rw [Chart.tipAt_unique hz h1]
    exact himg _ (hin r _ h2)

/-! ### The run charts are conformal -/

/-- The stopped driver of a regular piece is continuous and starts at `0`. -/
theorem continuous_stopDrv {Δ : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : GW1P.PieceRegular e.1 (min Δ e.2)) :
    Continuous (stopDrv Δ e) ∧ stopDrv Δ e 0 = 0 :=
  he.continuous_stoppedReal

/-- **The run charts of a GW2 schedule after successful regular pieces are conformal, with continuous lifts.** -/
theorem isConformal_succChart (x₀ : ℝ) (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ k, (∀ j < k, GW1P.PieceRegular (D j).1 (min (Δ j) (D j).2)) →
      (succChart x₀ Δ D k).IsConformal ∧
        ContinuousOn (fun w => (succChart x₀ Δ D k).2.2 ((succChart x₀ Δ D k).2.1 w)) H
  | 0, _ => ⟨Chart.isConformal_id.recenter x₀, Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift⟩
  | k + 1, hreg => by
    obtain ⟨hc, hℓ⟩ := isConformal_succChart x₀ Δ D k fun j hj => hreg j (Nat.lt_succ_of_lt hj)
    obtain ⟨hU, hU0⟩ := continuous_stopDrv (hreg k (Nat.lt_succ_self k))
    have hT : 0 ≤ stopTime (Δ k) (D k) := NNReal.coe_nonneg _
    have hc₂ := Chart.isConformal_id.loewner hU hU0 hT
    have hℓ₂ : ContinuousOn (fun w => (Chart.id.loewner (stopDrv (Δ k) (D k)) (stopTime (Δ k) (D k))).2.2
        ((Chart.id.loewner (stopDrv (Δ k) (D k)) (stopTime (Δ k) (D k))).2.1 w)) H :=
      hc₂.continuousOn_lift_inv (Chart.continuousOn_lift_loewner hU hU0 hT)
    simp only [succChart]
    refine ⟨hc.loewner hU hU0 hT, ?_⟩
    rw [Chart.loewner_eq_trans]
    have hcomp : ContinuousOn (fun w => (Chart.id.loewner (stopDrv (Δ k) (D k)) (stopTime (Δ k) (D k))).2.2
        ((Chart.id.loewner (stopDrv (Δ k) (D k)) (stopTime (Δ k) (D k))).2.1 w) +
        (succChart x₀ Δ D k).2.2 ((succChart x₀ Δ D k).2.1
          ((Chart.id.loewner (stopDrv (Δ k) (D k)) (stopTime (Δ k) (D k))).2.1 w))) H :=
      hℓ₂.add (hℓ.comp hc₂.1.continuousOn hc₂.2.1)
    refine hcomp.congr fun w hw => ?_
    exact IsChartTransport.trans_lift_inv hc (hc₂.2.1 hw)

end GW2Later

end Theorem14

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelLocal
import InteractingSLE.Spec.Sec7.SideHeightHull

/-!
# Lemma 4.7's direction, item (A): the strip counterflow hull with its own stopped record

Packet PROVE-CFRESTART, field side. Proposition 3.7 with both stopped records retained (Astra's E.2; on Proposition
4.9's glued space `CrossCond.isHistoryAvoidanceLocal_cfGlue_of_records`) needs, for each curve, Aux. lemma 18's
history-marked avoidance criterion (`IsHistoryAvoidanceLocal`) of its stopped hull, with its own stopped driving
history as marks. For the flow line this is `Sec7.SideHeight.isHistoryAvoidanceLocal_flowHull`. For the counterflow
of `IsStripCounterflowDriver`, coupled in the chart `M_q` with its parameter field `h′` (the `M_q`-chart transport of
the strip field `h` with sign `−1`), this file proves it for the hull read back in the strip chart `E`:

* `stripFwd_image_eq`, **`measurable_image_stripFwd`**: `S ↦ M_q(S)` is hitting-measurable (`M_q = (−1) + (1+q)·R`);
* `stripFwd_image_stripInv_image`: `M_q(M_q⁻¹(S)) = S` for `S ⊆ ℍ`;
* **`isHistoryAvoidanceLocal_stripInv_hull`**: for an optional hull coupling `(h′, W, …)` (any parameter `κ′ > 0`) and
  a stopping time `τ < ζ` of its frozen driving filtration, every hitting-measurable version of `M_q⁻¹(K_τ)` satisfies
  the history-marked avoidance criterion for the centred strip field `h − u₀` (`u₀` harmonic) with the marks
  `𝓕_τ` (the capacity coding theorem `WholeField.isHistoryAvoidanceLocal_of_capacity` with the clock
  `S ↦ hcap(M_q(S))/2`, and `isLocalSet_stripInv_image` at every stopping time).

With the flow line's `isHistoryAvoidanceLocal_flowHull`, the generic single-space union
`WangWu.isHistoryAvoidanceLocal_union` (given the conditional independence of σ-algebras containing both records) and
`WholeField.exists_condExp_germSigma_history`, this is the strip form of GLUECOND5's E.2/E.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Sec5.CrossRestart

open LocalSets

variable {q : ℝ}

/-- `M_q = (−1) + (1 + q) · R` as an image of sets. -/
theorem stripFwd_image_eq (q : ℝ) (S : Set ℂ) :
    (Sec4.stripCounterflowChart q).1 '' S = (fun z : ℂ => z + ((-1 : ℝ) : ℂ)) ''
      (Sec7.Lemma725RefFull.dil (1 + q) '' (WangWu.negInv '' S)) := by
  rw [image_image, image_image]
  refine image_congr fun z _ => ?_
  rw [Sec4.stripCounterflowChart_fwd, WangWu.negInv, Sec7.Lemma725RefFull.dil]
  push_cast
  ring

/-- **`S ↦ M_q(S)` is hitting-measurable.** -/
theorem measurable_image_stripFwd (hq : 0 < q) :
    Measurable[hittingSigma, hittingSigma] fun S : Set ℂ => (Sec4.stripCounterflowChart q).1 '' S := by
  have e : (fun S : Set ℂ => (Sec4.stripCounterflowChart q).1 '' S) =
      (fun S : Set ℂ => (fun z : ℂ => z + ((-1 : ℝ) : ℂ)) '' S) ∘
        (fun S : Set ℂ => Sec7.Lemma725RefFull.dil (1 + q) '' S) ∘ fun S : Set ℂ => WangWu.negInv '' S :=
    funext fun S => stripFwd_image_eq q S
  rw [e]
  exact (Sec7.SideHeight.measurable_image_add (-1)).comp
    ((Sec7.Lemma725RefFull.measurable_image_dil (by linarith)).comp WangWu.measurable_image_negInv)

/-- `M_q(M_q⁻¹(S)) = S` for `S ⊆ ℍ`. -/
theorem stripFwd_image_stripInv_image (hq : 0 < q) {S : Set ℂ} (hS : S ⊆ H) :
    (Sec4.stripCounterflowChart q).1 '' ((Sec4.stripCounterflowChart q).2.1 '' S) = S := by
  rw [image_image]
  refine (image_congr fun z hz => ?_).trans (image_id S)
  refine Sec4.stripCounterflowChart_fwd_inv hq fun h => ?_
  have := congrArg Complex.im h
  simp only [neg_im, one_im, neg_zero] at this
  exact (ne_of_gt (show (0 : ℝ) < z.im from hS hz)) this

/-- **The strip counterflow hull with its own stopped record.** Let `(h′, W, VL, VR, B, ζ)` be an optional hull
coupling (parameter `κ′ > 0`) of the parameter field `h′ ω`, the `M_q`-chart transport of `h ω` with sign `−1`; let
`u₀` be harmonic with `h − u₀` a zero-boundary GFF. For every stopping time `τ < ζ` of the frozen driving filtration
and every hitting-measurable version `A` of `M_q⁻¹(K_τ)`, `A` satisfies the history-marked avoidance criterion for
`h − u₀` with the marks `𝓕_τ`. -/
theorem isHistoryAvoidanceLocal_stripInv_hull (hq : 0 < q) {κ' : ℝ} (hκ' : 0 < κ') {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h h' : Ω → DistOn upperHalfPlaneOpens} {a k : ℝ}
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕 W VL VR B ζ h')
    (htr : ∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k (h ω) (h' ω))
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀) P)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = (Sec4.stripCounterflowChart q).2.1 ''
      fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace A
      (fun ω => h ω - smoothDist upperHalfPlaneOpens u₀) P := by
  have hh0m := hh0.measurable
  have hE := hC.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτζ] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    obtain ⟨_, h⟩ := hF.exists
    exact h
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX)
    (B := B) (κ := κ') (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ') hseed
  have hΦ : Measurable[hittingSigma] fun S : Set ℂ =>
      WholeField.hullClock ((Sec4.stripCounterflowChart q).1 '' S) :=
    @Measurable.comp _ _ _ hittingSigma hittingSigma _ _ _ WholeField.measurable_hullClock
      (measurable_image_stripFwd hq)
  refine WholeField.isHistoryAvoidanceLocal_of_capacity
    (K := fun t ω => (Sec4.stripCounterflowChart q).2.1 '' fwdHull (fun s : ℝ => W s.toNNReal ω) t) hh0m hΦ ?_
    hσ ?_ hτ hτζ hA hAK
  · filter_upwards [hE.2.2.2.2] with ω hp t ht
    show WholeField.hullClock ((Sec4.stripCounterflowChart q).1 ''
      ((Sec4.stripCounterflowChart q).2.1 '' fwdHull (fun s : ℝ => W s.toNNReal ω) t)) = t
    rw [stripFwd_image_stripInv_image hq fun z hz => hz.1]
    exact WholeField.hullClock_fwdHull_rpath hp.2.2.2.1 hp.1 ht
  · intro S hS hSζ
    obtain ⟨-, -, -, hX', hker⟩ := hC
    have h1 : IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((S ω).untopD 0 : ℝ≥0)) h' P :=
      (hker S hS hSζ).1
    have h2 := WholeField.IsLocalSet.sub_dist (isLocalSet_stripInv_image hq h1 htr)
      (WholeField.isHarmonicDistOn_smoothDist hu₀)
    obtain ⟨A', hA'm, hA'e, hA'loc⟩ := WholeField.IsLocalSet.exists_measurable_version h2 hh0m
    exact ⟨A', hA'm, hA'e, IsLocalSet.isMarkedAvoidanceLocal hh0m hA'm hA'loc⟩

end InteractingSLE.Sec5.CrossRestart

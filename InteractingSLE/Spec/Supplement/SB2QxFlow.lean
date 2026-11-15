/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QwStep
import InteractingSLE.Spec.Supplement.SB2CondCode
import InteractingSLE.Spec.Supplement.SB2MzMain

/-!
# The canonical driver is the conditional flow-line driver; the step through one piece for it

Worker REVIEW-FABLE-T14 (items 2–3 of PROVE-SB2-LCMEAN's handoff R13.8; the step `ℓ → ℓ + 2`). The step
`Qw.ae_isGFF_stepField` asks a driver that is, given the marks of stage `ℓ`, the conditional flow-line driver of the
stage field. For the canonical driver `driverOf (c, Z)` (the field-determined flow line of the field `Z` with word `c`,
`Restart.driverOf`) this follows from the law alone, by Theorem 1.3 (`Cond.isFlowLineDriver_of_driverCodeMatch_univ`):
under the conditional law the word is almost surely the conditioning sample's, and the canonical driver matches its own
code.

* **`ae_isFlowLineDriver_driverOf`**;
* **`ae_isGFF_stepField_canon`**: `Qw.ae_isGFF_stepField` for the canonical driver of the stage field read in
  `Mo.hullChart K x₀` with the shifted word (no flow-line hypothesis).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qx

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField Qw

/-- **The canonical driver is the conditional flow-line driver** (Theorem 1.3): if, given `𝓜`, the field `Z` is
almost surely on `L` a GFF with the data of the `𝓜`-measurable word `c`, then the canonical driver
`driverOf (c, Z)` is there the angle-`θ` flow-line driver of `Z`. -/
theorem ae_isFlowLineDriver_driverOf (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ) {c : Ω → BoundaryWord}
    (hc : Measurable[𝓜] c) {Z : Ω → DistOn upperHalfPlaneOpens} (hZ : Measurable Z) {L : Set Ω}
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Z (c ω₀).fn (c ω₀).jumps) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsFlowLineDriver κ (c ω₀).fn (c ω₀).jumps θ (condExpKernel P 𝓜 ω₀) Z
      (fun t ω => (driverOf h12p hκ θ (c ω, Z ω)).1 t) (fun ω => (driverOf h12p hκ θ (c ω, Z ω)).2) := by
  have hcm : Measurable c := hc.mono h𝓜 le_rfl
  have hD : Measurable fun ω => driverOf h12p hκ θ (c ω, Z ω) :=
    (measurable_driverOf h12p hκ θ).comp (hcm.prodMk hZ)
  filter_upwards [hlaw, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝓜 hc] with ω₀ hl hceq hω₀
  refine Cond.isFlowLineDriver_of_driverCodeMatch_univ h12p hκ θ h13 (c ω₀) (hl hω₀)
    (fun t => (measurable_pi_apply t).comp (measurable_fst.comp hD)) (measurable_snd.comp hD)
    (fun ω => Mu.continuousOn_driverOf h12p hκ θ (c ω, Z ω)) ?_
  filter_upwards [hceq] with ω hω
  rw [← hω]
  exact Mu.isDriverCodeMatch_driverOf h12p hκ θ (c ω, Z ω)

/-- **The step through one piece for the canonical driver.** `Qw.ae_isGFF_stepField` with `e = driverOf (β', Y)`,
where `β' = shiftW x₀ β` is the word of the stage field `Y` read in `Mo.hullChart K x₀`: the flow-line hypothesis is
discharged by `ae_isFlowLineDriver_driverOf`. -/
theorem ae_isGFF_stepField_canon (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {ℋ : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    {p : Ω → S} (hp : Measurable p) (hℋ : ℋ ≤ mΩ) (hpℋ : Measurable[ℋ] p)
    {β : Ω → BoundaryWord} (hβ : Measurable[MeasurableSpace.comap p inferInstance] β)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y) {θ : ℝ} {L : Set Ω}
    (hL : MeasurableSet[MeasurableSpace.comap p inferInstance] L)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsGFFWithBoundaryData (condExpKernel P (MeasurableSpace.comap p inferInstance) ω₀)
      Y (β ω₀).fn (β ω₀).jumps)
    (hrℋ : Measurable[ℋ] fun ω => recOf ⊤ (driverOf h12p hκ θ (β ω, Y ω)))
    {x₀ : Ω → ℝ} (hx₀ : Measurable[MeasurableSpace.comap p inferInstance] x₀)
    {K₂ : Ω → Set ℂ} (hK₂m : @IsDyadicHitMeasurable Ω ℋ K₂) (hK₂c : ∀ ω, IsCompact (K₂ ω))
    (hK₂p : ∀ ω, IsPreconnected (K₂ ω ∪ Restart.lowerHalf)) {A : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hAloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) P) (hAl : IsLocalSet A (centredField h u₀) P)
    {G : Set Ω} (hG : MeasurableSet[ℋ] G) (hGL : G ⊆ L)
    (hGζ : ∀ ω ∈ G, (driverOf h12p hκ θ (β ω, Y ω)).2 ≠ ⊤)
    (hGA : ∀ᵐ ω ∂P, ω ∈ G → A ω = fillH (K₂ ω))
    (hYt₂ : ∀ᵐ ω ∂P, ω ∈ G → LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ θ (β ω, Y ω)))) →
      IsChartTransport (Mo.hullChart (fillH (K₂ ω)) 0) 1 0 (chiC κ) (h ω)
        (stepField κ x₀ (fun ω => driverOf h12p hκ θ (β ω, Y ω)) Y ω)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P ℋ ω₀)
      (stepField κ x₀ (fun ω => driverOf h12p hκ θ (β ω, Y ω)) Y)
      (stepWord κ θ x₀ β (fun ω => driverOf h12p hκ θ (β ω, Y ω)) ω₀).fn
      (stepWord κ θ x₀ β (fun ω => driverOf h12p hκ θ (β ω, Y ω)) ω₀).jumps := by
  have hPΩ : MeasurableSpace.comap p inferInstance ≤ mΩ := hp.comap_le
  have hD : Measurable fun ω => driverOf h12p hκ θ (β ω, Y ω) :=
    (measurable_driverOf h12p hκ θ).comp ((hβ.mono hPΩ le_rfl).prodMk hY)
  exact ae_isGFF_stepField hκ hh hu₀ hp hℋ hpℋ hβ hY hD
    (fun ω => Mz.isRegularDriver_driverOf h12p hκ θ _) hrℋ hL
    (ae_isFlowLineDriver_driverOf h12p h13 hκ θ hPΩ hβ hY hlaw) hx₀ hK₂m hK₂c hK₂p hAm hAc hAloc hAl hG hGL hGζ
    hGA hYt₂

end InteractingSLE.Theorem14.SB.Qx

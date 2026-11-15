/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5SameLate
import InteractingSLE.Spec.Sec7.SideC5Cover
import InteractingSLE.Spec.Sec7.SideVisLate

/-!
# The late reference-height cover from the ambient heights and a pathwise cover

Packet PROVE-R5-SAMETIME. `Wire.VisitReferenceHeightCoverPosExc` (PROVE-SIDE-COLLAR2's remaining cover input) asks,
for every local-set mean of the old hull references, for the exact limit of the reference mean read in the old
(reference visit) chart. By `R5Same.ae_tendsto_harmRep_capacityReference` that limit is the ambient word at the
reference's original time, corrected by the limit of the lift difference "old lift − ambient lift". What is left is
pathwise:

* `VisitReferenceAmbientCoverPosExc` (named input, purely pathwise — no local-set mean, no conditional law): the
  selection
  of the reference, its collar and transition (as in `VisitReferenceHeightCoverPosExc`), the physical hull point of the
  old access inside the pocket, the ambient image `x'` of the old access, the limit `ℓ` of the lift difference and the
  word identity `β_s(x') + χ ℓ = current word + phase − offset`;
* **`visitReferenceHeightCoverPosExc_of_ambient`**: with the inputs of the late raw reference law
  (`Wire.Current.SideTest.raw_reference_law_at_original_time`) for every `Ready` test and the identification of the
  side-limit harmonic function with the coupled mean (`hHarm`), the pathwise cover gives
  `VisitReferenceHeightCoverPosExc`.

This is a conditional helper with a distinct name; it replaces no source theorem. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H chiC fwdMap logDerivFwd)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Current.SideTest Sec7 LocalSets Sec7.PocketStopSide Sec7.PocketStopWallsFin Sec7.PocketStop
  Sec7.PocketTraversal Sec7.Lemma71C Sec7.Aux119Heights WholeField

/-- **The pathwise remainder of the late reference-height cover** (named input; no local-set mean or conditional law
appears): for every positive relative capacity and every current real coordinate off the jumps whose physical landing
avoids `X`, a reference with an unfilled incident collar and transition (as in `VisitReferenceHeightCoverPosExc`), the
physical point `z₀` of the counterflow hull inside the pocket reached by the old access, staying in the reference
complement, the ambient image `x'` of the old access off the ambient jumps, the limit `ℓ` of "old lift − ambient lift",
and the word identity `β_s(x') + χ ℓ = current word + phase − offset`. -/
def VisitReferenceAmbientCoverPosExc {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let e := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ q : ℝ≥0, 0 < q →
    ∀ᵐ ω ∂d.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      let current := relChart target.baseChart target.curve q ω;
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a q ω -
          segDriver (target.curve ω) q)
        (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a q ω -
          segDriver (target.curve ω) q) →
        extendFrom H current.2.1 (ξ : ℂ) ∉ X j q ω →
        ∃ (r : ℕ) (x ε x' ℓ : ℝ) (z₀ : ℂ), let old := j.referenceVisitChart i d ω (s j r);
          let w : ℝ → ℝ := fun t => d.driver t.toNNReal ω;
          d.curve ω (s j r) ∈ target.domain ω ∧
          (j.visitCapacity d ω (s j r)).toNNReal ≤ q ∧ 0 < ε ∧
          old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (current.dom : Set ℂ) ∧
          Tendsto (fun z => old.1 (current.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          z₀ ∈ target.domain ω ∩ regHull d.driver d.lifetime (s j r) ω ∧
          Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 z₀) ∧
          (∀ᶠ y in 𝓝[H] (x : ℂ), old.2.1 y ∈ H \ j.capacityReference i d (s j r) ω) ∧
          x' ∉ forceJumpSet (fun a => d.forceL a (s j r) ω - d.driver (s j r) ω)
            (fun a => d.forceR a (s j r) ω - d.driver (s j r) ω) ∧
          Tendsto (fun y => fwdMap w (s j r) (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) ∧
          Tendsto (fun y => old.2.2 (old.2.1 y) - (logDerivFwd w (s j r) (old.2.1 y)).im)
            (𝓝[H] (x : ℂ)) (𝓝 ℓ) ∧
          forceBoundaryData i.kappa d.rhoL d.rhoR (fun a => d.forceL a (s j r) ω - d.driver (s j r) ω)
              (fun a => d.forceR a (s j r) ω - d.driver (s j r) ω) x' + chiC i.kappa * ℓ =
            forceBoundaryData target.kappa target.rhoL target.rhoR
              (fun a => geomLW (fun t ω => segDriver (target.curve ω) t)
                target.marksL a q ω - segDriver (target.curve ω) q)
              (fun a => geomRW (fun t ω => segDriver (target.curve ω) t)
                target.marksR a q ω - segDriver (target.curve ω) q)
              ξ + e.phase q ω * (Ioo
                (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL q ω -
                  segDriver (target.curve ω) q)
                (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR q ω -
                  segDriver (target.curve ω) q)).indicator 1 ξ - e.offset

/-- **`VisitReferenceHeightCoverPosExc` from the ambient heights and the pathwise cover.** The heights of every
version of the old hull references' means, read in the old chart, are the ambient words at the references' original
times corrected by the lift difference (`R5Same.ae_tendsto_harmRep_capacityReference`, intersected over the countably
many references); the pathwise cover supplies everything else. `hHarm` identifies the side-limit harmonic function
with the coupled mean (the field is the coupled mean plus the centred field). -/
theorem visitReferenceHeightCoverPosExc_of_ambient {Ω : Type} [mΩ : MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ j : SideTest Ω, j.Ready d → ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ j : SideTest Ω, j.Ready d → ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ j : SideTest Ω, j.Ready d → ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j : SideTest Ω, j.Ready d → ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure)
    (hHarm : EqOn d.harmonic d.coupledMean H)
    (hCov : VisitReferenceAmbientCoverPosExc i d side s X) :
    VisitReferenceHeightCoverPosExc i d side s X := by
  intro j hj target e zL zR q hq gB hgB
  have hκ0 : i.kappa ≠ 0 := (lt_trans (by norm_num) i.kappa_gt_four).ne'
  have hall := ae_all_iff.2 fun r => R5Same.ae_tendsto_harmRep_capacityReference hj hTransport hTranslate hu hh
    hCoupling hu' hKilled hLife (hCont j hj) (hStart j hj) (hMeas j hj) (hDetermined j hj) (hLocal j hj) (s j r)
    (hgB r)
  filter_upwards [hall, hCov j hj q hq] with ω hH hC hωE hlive current ξ hξ hX
  obtain ⟨r, x, ε, x', ℓ, z₀, h1, h2, h3, h4, h5, hz₀, hinv, hev, hx', hfx, hℓ, hword⟩ := hC hωE hlive ξ hξ hX
  have hωE' : ω ∈ j.event := by rwa [target_event] at hωE
  have hHt := hH r hωE' z₀ hz₀ _ (x : ℂ) x' hx' hinv hev hfx
  have hsum := hHt.add (hℓ.const_mul (chiC i.kappa))
  rw [hword] at hsum
  refine ⟨r, x, ε, _, h1, h2, h3, h4, h5, hsum.congr' ?_, rfl⟩
  filter_upwards [hev] with y hy
  have hk : (j.target i d).kappa = i.kappa := by
    rw [Late.target_kappa]
    field_simp
  have hharmT : (j.target i d).harmonic = d.harmonic := by
    cases h : j.twoLeft <;> simp only [SideTest.target, h, Bool.false_eq_true, ↓reduceIte]
  have htg : target = j.target i d := rfl
  simp only [sideMean, htg, hk, hharmT, hHarm hy.1]
  ring

end InteractingSLE.Wire

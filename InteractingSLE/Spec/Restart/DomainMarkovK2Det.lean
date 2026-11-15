/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2
import InteractingSLE.Spec.Restart.CondDet
import InteractingSLE.Spec.Supplement.Disintegrate

/-!
# K2, last step: (Det) from flow lines under the regular conditional law

Packet PROVE-DOMAINMARKOV5. The general kernel assembly (`ae_isOptionalHullCoupling_k`) produces couplings under the
regular conditional law `condExpKernel P 𝒢 ω₀` on the original space. The (Det) clauses of the consumers
(`RetainedCanonCondDetStatement`, `FirstContactCanonCondDetStatement`, `Lemma76DetStatement`) are code matches with
canonical flow codes (`IsCanonicalFlowCode`, PROVE-CONDDET) holding `P`-almost surely. PROVE-CONDDET's lift
(`ae_codeMatch_of_ae_isFlowLine`) goes through a disintegration kernel on a code space; this file gives the direct lift
from `condExpKernel P 𝒢`:

* **`ae_codeMatch_of_ae_condExpKernel_isFlowLine`**: if, for `P`-almost every `ω₀` in a `𝒢`-event `M`, the path `γ` with
  lifetime `U` is, under `condExpKernel P 𝒢 ω₀`, the angle-`θ` flow line from `(β ω₀).2` of the field `Hc` with the
  boundary word `(β ω₀).1` (`β` is `𝒢`-measurable), then `P`-almost surely on `M`, `γ` with lifetime `U` is the decoded
  canonical flow code of `(β, Hc)`.

The canonical codes certify determination on spaces in `Type` (universe `0`), so `Ω : Type` here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open LQGMetric (DistOn)
open scoped ENNReal NNReal

namespace InteractingSLE.Restart.DomainMarkov.K2

/-- **(Det) from flow lines under the regular conditional law.** -/
theorem ae_codeMatch_of_ae_condExpKernel_isFlowLine {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω}
    (hM : MeasurableSet[𝒢] M) {β : Ω → BoundaryWord × ℝ} (hβ : Measurable[𝒢] β)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hH : Measurable Hc) {γ : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ t, Measurable fun ω => γ ω t) {U : Ω → ℝ≥0∞} (hU : Measurable U)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ U ω}) {κ θ : ℝ}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F)
    (hfl : ∀ᵐ ω₀ ∂P, ω₀ ∈ M →
      IsFlowLine κ (β ω₀).1.fn (β ω₀).1.jumps (β ω₀).2 θ (condExpKernel P 𝒢 ω₀) Hc γ U) :
    ∀ᵐ ω ∂P, ω ∈ M → IsCodeMatch (F (β ω, Hc ω)) (γ ω) (U ω) := by
  set G : (BoundaryWord × ℝ) × Ω → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞ :=
    fun p => F (p.1, Hc p.2) with hGdef
  have hGm : Measurable G := hF.1.comp (measurable_fst.prodMk (hH.comp measurable_snd))
  have hA : MeasurableSet (codeMatchSet G γ U) := measurableSet_codeMatchSet hGm hγ hU
  have h : ∀ᵐ ω₀ ∂P, ω₀ ∈ M → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (β ω₀, ω) ∈ codeMatchSet G γ U := by
    filter_upwards [hfl] with ω₀ hfl₀ hω₀
    have hd := hF.2.2 (β ω₀).1 (β ω₀).2 (condExpKernel P 𝒢 ω₀) Hc γ U (hfl₀ hω₀)
    filter_upwards [hd] with ω hω
    exact mem_codeMatchSet_of_codeMatch (G := G) (p := (β ω₀, ω)) hω
  filter_upwards [Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param h𝒢 hβ hA hM h] with ω hω hωM
  exact codeMatch_of_mem_codeMatchSet (G := G) (p := (β ω, ω)) (hγc ω) (hω hωM)

end InteractingSLE.Restart.DomainMarkov.K2

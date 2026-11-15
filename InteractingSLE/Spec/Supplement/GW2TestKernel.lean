/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootTest
import InteractingSLE.Spec.Sec5.Prop59StageLaw

/-!
# Conditional comparison estimates for GW2's per-candidate tests

Packet PROVE-GW2-TEST. These are conditional helpers, not a proof of
`GW2RootTestStatement`. They convert the comparison form of a retained stage law
into the conditional probability estimate needed by `TestClaims.hnounit`.
The stage law must concern the complete retained stage-start sigma-algebra.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace InteractingSLE.Theorem14.GW2TipSystem

namespace TestKernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- A lower comparison estimate on every past event gives an almost-sure lower
bound for the regular conditional probability on the reached event. -/
theorem ae_le_condExpKernel_of_comparison (h𝒢 : 𝒢 ≤ mΩ) {R E : Set Ω}
    (hR : MeasurableSet[𝒢] R) (hE : MeasurableSet E) {p : ℝ≥0∞}
    (hcomp : ∀ C : Set Ω, MeasurableSet[𝒢] C → C ⊆ R →
      p * P C ≤ P (C ∩ E)) :
    ∀ᵐ ω ∂P, ω ∈ R → p ≤ condExpKernel P 𝒢 ω E := by
  have hf : Measurable[𝒢] (R.indicator fun _ : Ω => p) :=
    measurable_const.indicator hR
  have hg : Measurable[𝒢] fun ω => condExpKernel P 𝒢 ω E :=
    measurable_condExpKernel hE
  have hle : (R.indicator fun _ : Ω => p) ≤ᵐ[P.trim h𝒢]
      fun ω => condExpKernel P 𝒢 ω E := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf fun C hC _ => ?_
    rw [setLIntegral_trim h𝒢 hf hC, setLIntegral_trim h𝒢 hg hC,
      setLIntegral_indicator (h𝒢 _ hR), lintegral_const,
      Measure.restrict_apply_univ, KernelTower.setLIntegral_condExpKernel h𝒢 hC hE]
    exact (hcomp (R ∩ C) (hR.inter hC) inter_subset_left).trans
      (measure_mono fun ω hω => ⟨hω.1.2, hω.2⟩)
  filter_upwards [ae_of_ae_trim h𝒢 hle] with ω hω hωR
  rwa [indicator_of_mem hωR] at hω

/-- A positive-probability slow event bounds all successful tests without a unit.
The exclusion is required only almost surely, so null modifications of the
underlying paths do not create exact pointwise obligations. -/
theorem ae_no_unit_le_of_comparison (h𝒢 : 𝒢 ≤ mΩ) {R E : Set Ω}
    (hR : MeasurableSet[𝒢] R) (hE : MeasurableSet E) {p : ℝ} (hp : 0 ≤ p)
    (hcomp : ∀ C : Set Ω, MeasurableSet[𝒢] C → C ⊆ R →
      ENNReal.ofReal p * P C ≤ P (C ∩ E))
    {ι : Type*} {T V : ι → Set Ω}
    (hexcl : ∀ᵐ ω ∂P, ω ∈ R → ω ∈ E → ∀ q, ω ∈ T q → ω ∈ V q) :
    ∀ᵐ ω ∂P, ω ∈ R →
      condExpKernel P 𝒢 ω (⋃ q, T q \ V q) ≤ ENNReal.ofReal (1 - p) := by
  filter_upwards [ae_le_condExpKernel_of_comparison h𝒢 hR hE hcomp,
    KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hR,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hexcl] with ω₀ hbound hR₀ hexcl₀ hω₀R
  have hmem : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ R := by
    exact ae_iff.2 (hR₀.1 hω₀R)
  have hsub : (⋃ q, T q \ V q) ≤ᵐ[condExpKernel P 𝒢 ω₀] Eᶜ := by
    filter_upwards [hexcl₀, hmem] with ω hω hωR
    intro hωT hωE
    obtain ⟨q, hq⟩ := mem_iUnion.1 hωT
    exact hq.2 (hω hωR hωE q hq.1)
  calc
    condExpKernel P 𝒢 ω₀ (⋃ q, T q \ V q) ≤ condExpKernel P 𝒢 ω₀ Eᶜ :=
      measure_mono_ae hsub
    _ = 1 - condExpKernel P 𝒢 ω₀ E := by
      rw [measure_compl hE (measure_ne_top _ _), measure_univ]
    _ ≤ 1 - ENNReal.ofReal p :=
      tsub_le_tsub le_rfl (hbound hω₀R)
    _ = ENNReal.ofReal (1 - p) := by
      rw [ENNReal.ofReal_sub _ hp, ENNReal.ofReal_one]

/-- The retained stage law and a comparison premise for a slow event imply the
no-unit estimate. The start restriction and the geometric implication from the
slow event to a unit are only almost-sure assertions. -/
theorem ae_no_unit_le_of_stageLaw (h𝒢 : 𝒢 ≤ mΩ) {R : Set Ω}
    (hR : MeasurableSet[𝒢] R) {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {y : Ω → Sec5.Prop59Stage.Start nL nR} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hL : Sec5.Prop59Stage.IsStageLaw κ P 𝒢 R ρL ρR y W VL VR B ζ)
    (hobs : Measurable fun ω =>
      (y ω, Sec5.Prop59Stage.samp (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (ζ ω)))
    {D : Set (Sec5.Prop59Stage.Start nL nR)} (hD : MeasurableSet D)
    {S : Set (Sec5.Prop59Stage.Start nL nR × Sec5.Prop59Stage.Samp nL nR)}
    (hS : MeasurableSet S) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hprem : Sec5.Prop59Stage.CompPremise κ ρL ρR D S (ENNReal.ofReal p))
    (hstart : ∀ᵐ ω ∂P, ω ∈ R → y ω ∈ D)
    {ι : Type*} {T V : ι → Set Ω}
    (hunit : ∀ᵐ ω ∂P, ω ∈ R →
      (y ω, Sec5.Prop59Stage.samp (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (ζ ω)) ∈ S → ∀ q, ω ∈ T q → ω ∈ V q) :
    ∀ᵐ ω ∂P, ω ∈ R →
      condExpKernel P 𝒢 ω (⋃ q, T q \ V q) ≤ ENNReal.ofReal (1 - p) := by
  let E : Set Ω := {ω | y ω ∈ D →
    (y ω, Sec5.Prop59Stage.samp (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (ζ ω)) ∈ S}
  have hE : MeasurableSet E := by
    have heq : E = (fun ω =>
        (y ω, Sec5.Prop59Stage.samp (W · ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (ζ ω))) ⁻¹' ((Prod.fst ⁻¹' D)ᶜ ∪ S) := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_preimage, mem_union, mem_compl_iff]
      exact imp_iff_not_or
    rw [heq]
    exact hobs ((measurable_fst hD).compl.union hS)
  refine ae_no_unit_le_of_comparison h𝒢 hR hE hp
    (fun C hC hCR => hL.le_measure hD hS (ENNReal.ofReal_le_one.2 hp1) hprem hC hCR) ?_
  filter_upwards [hstart, hunit] with ω hωstart hωunit hωR hωE
  exact hωunit hωR (hωE (hωstart hωR))

end TestKernel

end InteractingSLE.Theorem14.GW2TipSystem

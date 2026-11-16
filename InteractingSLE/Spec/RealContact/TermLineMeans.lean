/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermPrefixMean

/-!
# The two individual means at a line

Packet PROVE-RC-TERM, second run (ruling R124). For line data at `(t, N)` and regular measurable drivers of the two
flow lines:

* `IsLineData.comap_recOf_ret_le`, `IsLineData.comap_recOf_expl_le`: the record of the second driver at own time `N`
  (of the first driver at own time `t`) is, up to null sets, a function of the killed pair history at `(0, N)`
  (at `(t, 0)`) of the versions (`Term.ae_eq_measurable_recOf`);
* **`IsLineData.ae_eqOn_retMean`**, **`IsLineData.ae_eqOn_explMean`**: every harmonic representative of the local-set
  mean of the retained filled prefix `fill(ηc₂([0, N]))` (of the explored filled prefix `fill(ηc₁([0, t]))`) is the
  candidate mean `Term.prefixMeanFn` of the record (`Term.ae_eqOn_prefixMean`).

R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F Exist.Staged Exist.StagedLaw Sec2.Assembly LocalSets
  WholeField

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}
  {t N : ℝ≥0} {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}

namespace IsLineData

variable (d : IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ t N ηc₁ ηc₂)
include d

/-- The record of the second driver at own time `N` is, up to null sets, a function of the killed pair history at
`(0, N)`. -/
theorem comap_recOf_ret_le {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ} {g : Ω → DistOn upperHalfPlaneOpens}
    {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : ∀ ω, IsRegularDriver (E ω)) (hE2 : ∀ ω, (E ω).2 = ζ₂ ω)
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₂ ω) (fun s => η₂ ω s - x₂)) :
    MeasurableSpace.comap (fun ω => recOf (N : ℝ≥0∞) (E ω)) inferInstance ≤
      aeSigma (MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
        (fun ω => cutLife (ζ₂ ω) (capR t N)) 0 N) inferInstance) P := by
  have htrace' : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (E ω).2 (fun s => η₂ ω s - x₂) := by
    filter_upwards [htrace] with ω hω
    rw [hE2]
    exact hω
  have ha' : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR t N) (E ω).2 s) := by
    filter_upwards [d.ae₂] with ω hω s
    rw [hE2]
    exact hω s
  have hlife : MeasurableSet[MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
      (fun ω => cutLife (ζ₂ ω) (capR t N)) 0 N) inferInstance] {ω | lifeRec (E ω).2 N = ⊤} := by
    have h1 : MeasurableSet[MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
        (fun ω => cutLife (ζ₂ ω) (capR t N)) 0 N) inferInstance]
        ((fun ω => (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
          (fun ω => cutLife (ζ₂ ω) (capR t N)) 0 N ω).2.2) ⁻¹' {⊤}) :=
      (measurable_snd.comp (measurable_snd.comp (comap_measurable _))) (measurableSet_singleton ⊤)
    have e : {ω | lifeRec (E ω).2 N = ⊤} =
        (fun ω => (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
          (fun ω => cutLife (ζ₂ ω) (capR t N)) 0 N ω).2.2) ⁻¹' {⊤} := by
      ext ω
      show lifeRec (E ω).2 N = ⊤ ↔ lifeRec (cutLife (ζ₂ ω) (capR t N)) N = ⊤
      rw [lifeRec_cutLife_eq (lt_capR_right t N), hE2]
    rw [e]
    exact h1
  obtain ⟨G, hGm, hae⟩ := ae_eq_measurable_recOf hκ hreg hfl htrace' (lt_capR_right t N) ha'
    (𝒦 := MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
      (fun ω => cutLife (ζ₂ ω) (capR t N)) 0 N) inferInstance)
    (fun s hs => measurable_coord_cstHist_right d.cont₂ hs) hlife
  exact (WholeField.measurable_aeSigma_of_ae_eq' hGm hae).comap_le

/-- The record of the first driver at own time `t` is, up to null sets, a function of the killed pair history at
`(t, 0)`. -/
theorem comap_recOf_expl_le {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ} {g : Ω → DistOn upperHalfPlaneOpens}
    {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : ∀ ω, IsRegularDriver (E ω)) (hE2 : ∀ ω, (E ω).2 = ζ₁ ω)
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₁ ω) (fun s => η₁ ω s - x₁)) :
    MeasurableSpace.comap (fun ω => recOf (t : ℝ≥0∞) (E ω)) inferInstance ≤
      aeSigma (MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
        (fun ω => cutLife (ζ₂ ω) (capR t N)) t 0) inferInstance) P := by
  have htrace' : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (E ω).2 (fun s => η₁ ω s - x₁) := by
    filter_upwards [htrace] with ω hω
    rw [hE2]
    exact hω
  have ha' : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR t N) (E ω).2 s) := by
    filter_upwards [d.ae₁] with ω hω s
    rw [hE2]
    exact hω s
  have hlife : MeasurableSet[MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
      (fun ω => cutLife (ζ₂ ω) (capR t N)) t 0) inferInstance] {ω | lifeRec (E ω).2 t = ⊤} := by
    have h1 : MeasurableSet[MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
        (fun ω => cutLife (ζ₂ ω) (capR t N)) t 0) inferInstance]
        ((fun ω => (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
          (fun ω => cutLife (ζ₂ ω) (capR t N)) t 0 ω).1.2) ⁻¹' {⊤}) :=
      (measurable_snd.comp (measurable_fst.comp (comap_measurable _))) (measurableSet_singleton ⊤)
    have e : {ω | lifeRec (E ω).2 t = ⊤} =
        (fun ω => (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
          (fun ω => cutLife (ζ₂ ω) (capR t N)) t 0 ω).1.2) ⁻¹' {⊤} := by
      ext ω
      show lifeRec (E ω).2 t = ⊤ ↔ lifeRec (cutLife (ζ₁ ω) (capR t N)) t = ⊤
      rw [lifeRec_cutLife_eq (lt_capR_left t N), hE2]
    rw [e]
    exact h1
  obtain ⟨G, hGm, hae⟩ := ae_eq_measurable_recOf hκ hreg hfl htrace' (lt_capR_left t N) ha'
    (𝒦 := MeasurableSpace.comap (cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR t N))
      (fun ω => cutLife (ζ₂ ω) (capR t N)) t 0) inferInstance)
    (fun s hs => measurable_coord_cstHist_left d.cont₁ hs) hlife
  exact (WholeField.measurable_aeSigma_of_ae_eq' hGm hae).comap_le

/-- **The mean of the retained filled prefix** (the completed second path on `{ζ₂ ≤ N}`). -/
theorem ae_eqOn_retMean {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hh : IsGFFWithBoundaryData P h b jumps) (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {c : BoundaryWord} {θ : ℝ} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω)) (hE2 : ∀ ω, (E ω).2 = ζ₂ ω)
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P (fun ω => Exist.flowField x₂ 0 (h ω)) (fun s ω => (E ω).1 s)
      (fun ω => (E ω).2))
    (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₂ ω) (fun s => η₂ ω s - x₂))
    {g₁ : Ω → DistOn upperHalfPlaneOpens} (hg₁ : IsLocalSetMean (fillOf ηc₂ N) (centredField h u₀) P g₁) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ fillOf ηc₂ N ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fillOf ηc₂ N ω → g₁ ω φ = ∫ z, v z * φ z) →
      EqOn v (prefixMeanFn κ c θ x₂ u₀ (recOf (N : ℝ≥0∞) (E ω))) (H \ fillOf ηc₂ N ω) := by
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have htrace' : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (E ω).2 (fun s => η₂ ω s - x₂) := by
    filter_upwards [htrace] with ω hω
    rw [hE2]
    exact hω
  have ha' : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR t N) (E ω).2 s) := by
    filter_upwards [d.ae₂] with ω hω s
    rw [hE2]
    exact hω s
  exact ae_eqOn_prefixMean hκ hh hu₀ hEm hreg hfl htrace' (lt_capR_right t N) ha'
    (d.measurable_ret.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl) (d.isLocalSet_ret hh0)
    (isHistoryAvoidanceLocal_of_le_aeSigma (d.comap_recOf_ret_le hκ hreg hE2 hfl htrace)
      d.isHistoryAvoidanceLocal_ret) hg₁

/-- **The mean of the explored filled prefix** (the first path up to `min t ζ₁`). -/
theorem ae_eqOn_explMean {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hh : IsGFFWithBoundaryData P h b jumps) (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {c : BoundaryWord} {θ : ℝ} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω)) (hE2 : ∀ ω, (E ω).2 = ζ₁ ω)
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P (fun ω => Exist.flowField x₁ 0 (h ω)) (fun s ω => (E ω).1 s)
      (fun ω => (E ω).2))
    (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₁ ω) (fun s => η₁ ω s - x₁))
    {g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₂ : IsLocalSetMean (fillOf ηc₁ t) (centredField h u₀) P g₂) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ fillOf ηc₁ t ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fillOf ηc₁ t ω → g₂ ω φ = ∫ z, v z * φ z) →
      EqOn v (prefixMeanFn κ c θ x₁ u₀ (recOf (t : ℝ≥0∞) (E ω))) (H \ fillOf ηc₁ t ω) := by
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have htrace' : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (E ω).2 (fun s => η₁ ω s - x₁) := by
    filter_upwards [htrace] with ω hω
    rw [hE2]
    exact hω
  have ha' : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR t N) (E ω).2 s) := by
    filter_upwards [d.ae₁] with ω hω s
    rw [hE2]
    exact hω s
  exact ae_eqOn_prefixMean hκ hh hu₀ hEm hreg hfl htrace' (lt_capR_left t N) ha'
    (d.measurable_expl.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl) (d.isLocalSet_expl hh0)
    (isHistoryAvoidanceLocal_of_le_aeSigma (d.comap_recOf_expl_le hκ hreg hE2 hfl htrace)
      d.isHistoryAvoidanceLocal_expl) hg₂

end IsLineData

end Term

end InteractingSLE.RealContact

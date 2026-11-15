/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsWalls
import InteractingSLE.Spec.Restart.MarkovChart
import InteractingSLE.WangWu.ReverseContactLocal

/-!
# The walls' locality transported through `R(z) = −1/z`

Packet PROVE-STRIPSYS41 (PROVE-STRIPSYS37 §5.1). PROVE-STRIPSYS37's `walls_determinedLocal` gives Lemma 6.2's
determined locality of the walls (fully explored) for the field of their own chart (the flow chart). Theorem 1.3's
pocket word reads the walls in the counterflow chart `m = R`, `R(z) = −1/z`, with the field `h₂` of that chart,
`h₂ = −h₁ ∘ R + m` (`reflectField`, plus a deterministic term). Here the criterion is transported once:

* `isZBGFFExtOn_neg`, `isHarmonicDistOn_neg`: sign changes;
* `negInvOpens`, `chartPreOpens_return`: `R(U')` and its pre-image through the return chart;
* **`ae_markovCompl_reflect`**: for Markov decompositions of `h₁` along `R(U')` and of `h₂` along `U'`, the harmonic
  parts satisfy `Y₂ = −Y₁ ∘ R + m` at every test function, almost surely (from PROVE-STAGEDLOC's chart transport
  `Restart.MarkovChart.ae_markovCompl_pushTest_eq`);
* `exists_ae_markovCompl_reflect`: the same as distributions, with the deterministic term a distribution `M`;
* **`walls_reflect`**: Lemma 6.2's walls criterion for `h₁` (all open `U ⊆ ℍ`) gives it for `h₂` and the reflected
  walls `R(S)`.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopWallsFin

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open WangWu (negInv reflectField)
open LocalSets

/-! ### Sign changes -/

section Neg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem measurable_neg_distOn {D : TopologicalSpace.Opens ℂ} : Measurable fun f : DistOn D => -f :=
  LQGMetric.measurable_distOn_iff.2 fun φ => by
    have e : (fun f : DistOn D => (-f) φ) = fun f => -(f φ) := funext fun f => neg_apply f φ
    rw [e]
    exact (LQGMetric.measurable_distOn_apply φ).neg

theorem measurable_sub_const_distOn {D : TopologicalSpace.Opens ℂ} (M : DistOn D) :
    Measurable fun f : DistOn D => f - M :=
  LQGMetric.measurable_distOn_iff.2 fun φ => by
    have e : (fun f : DistOn D => (f - M) φ) = fun f => f φ - M φ := funext fun f => sub_apply f M φ
    rw [e]
    exact (LQGMetric.measurable_distOn_apply φ).sub_const _

/-- A zero-boundary GFF extended by zero stays one after a sign change. -/
theorem isZBGFFExtOn_neg {U D : TopologicalSpace.Opens ℂ} {X : Ω → DistOn D} (hX : GFF.IsZBGFFExtOn U D X P) :
    GFF.IsZBGFFExtOn U D (fun ω => -X ω) P where
  measurable := measurable_neg_distOn.comp hX.measurable
  gaussian := by
    have e : (fun (φ : TestOn D) (ω : Ω) => (-X ω) φ) = (fun (φ : TestOn D) (ω : Ω) => X ω φ) ∘ fun φ => -φ := by
      funext φ ω
      simp only [neg_apply, Function.comp_apply, map_neg]
    rw [e]
    exact hX.gaussian.comp_right _
  centered := fun φ => by
    simp only [neg_apply, integral_neg, hX.centered φ, neg_zero]
  covariance_eq := fun φ ψ => by
    have e1 : (fun ω => (-X ω) φ) = -fun ω => X ω φ := by
      funext ω; simp only [neg_apply, Pi.neg_apply]
    have e2 : (fun ω => (-X ω) ψ) = -fun ω => X ω ψ := by
      funext ω; simp only [neg_apply, Pi.neg_apply]
    rw [e1, e2, covariance_neg_left, covariance_neg_right, neg_neg]
    exact hX.covariance_eq φ ψ

/-- A harmonic distribution stays harmonic after a sign change. -/
theorem isHarmonicDistOn_neg {T : DistOn upperHalfPlaneOpens} {U : Set ℂ} (hT : IsHarmonicDistOn T U) :
    IsHarmonicDistOn (-T) U := by
  obtain ⟨v, hv, hrep⟩ := hT
  refine ⟨-v, fun z hz => (hv z hz).neg, fun φ hφ => ?_⟩
  rw [neg_apply, hrep φ hφ, ← integral_neg]
  congr 1
  funext z
  simp only [Pi.neg_apply, neg_mul]

end Neg

/-! ### The Markov decomposition along `R(U')` -/

section Transport

open Sec7.StripSysField (infinityReturnChart isConformal_infinityReturnChart coe_dom_infinityReturnChart)

/-- `R(U')` as an open set, for an open `U' ⊆ ℍ`. -/
def negInvOpens (U' : TopologicalSpace.Opens ℂ) (hU' : (U' : Set ℂ) ⊆ H) : TopologicalSpace.Opens ℂ :=
  ⟨negInv '' U', WangWu.isOpen_image_negInv U'.isOpen hU'⟩

theorem coe_negInvOpens (U' : TopologicalSpace.Opens ℂ) (hU' : (U' : Set ℂ) ⊆ H) :
    (negInvOpens U' hU' : Set ℂ) = negInv '' U' := rfl

theorem negInvOpens_subset_H (U' : TopologicalSpace.Opens ℂ) (hU' : (U' : Set ℂ) ⊆ H) :
    (negInvOpens U' hU' : Set ℂ) ⊆ H := by
  rintro _ ⟨w, hw, rfl⟩
  exact WangWu.negInv_mem_H (hU' hw)

/-- The pre-image of `R(U')` through the return chart is `U'`. -/
theorem chartPreOpens_return (U' : TopologicalSpace.Opens ℂ) (hU' : (U' : Set ℂ) ⊆ H) :
    Restart.MarkovChart.chartPreOpens isConformal_infinityReturnChart (negInvOpens U' hU') = U' := by
  ext w
  change w ∈ H ∧ negInv w ∈ negInv '' (U' : Set ℂ) ↔ w ∈ U'
  rw [WangWu.negInv_involutive.injective.mem_set_image]
  exact ⟨fun h => h.2, fun h => ⟨hU' h, h⟩⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The harmonic parts along `R(U')` and `U'`** (chart transport of the Markov decomposition through `R`): if
`h₂ = −h₁ ∘ R + m` at every test function almost surely, then for Markov decompositions of `h₁` along `R(U')` and of
`h₂` along `U'`, `Y₂ = −Y₁ ∘ R + m` at every test function almost surely. -/
theorem ae_markovCompl_reflect {h₁ h₂ : Ω → DistOn upperHalfPlaneOpens} (m : TestOn upperHalfPlaneOpens → ℝ)
    (hrel : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, h₂ ω φ = reflectField (h₁ ω) φ + m φ)
    {U' : TopologicalSpace.Opens ℂ} (hU'H : (U' : Set ℂ) ⊆ H)
    {G₁ G₂ : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd₁ : GFF.IsMarkovDecomposition (negInvOpens U' hU'H) upperHalfPlaneOpens h₁ (fun ω => G₁ (h₁ ω)) P)
    (hd₂ : GFF.IsMarkovDecomposition U' upperHalfPlaneOpens h₂ (fun ω => G₂ (h₂ ω)) P)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, markovCompl G₂ (h₂ ω) φ = reflectField (markovCompl G₁ (h₁ ω)) φ + m φ := by
  have hUH := negInvOpens_subset_H U' hU'H
  have hUD : IsOpen ((negInvOpens U' hU'H : Set ℂ) \ (infinityReturnChart.dom : Set ℂ)) := by
    rw [coe_dom_infinityReturnChart, Set.sdiff_eq_empty.2 hUH]
    exact isOpen_empty
  have hUle : negInvOpens U' hU'H ≤ upperHalfPlaneOpens := hUH
  have hX := isZBGFFExtOn_neg hd₁.isZBGFFExtOn
  have hY : ∀ᵐ ω ∂P, IsHarmonicDistOn ((-h₁ ω) - (-G₁ (h₁ ω))) (negInvOpens U' hU'H) := by
    filter_upwards [ae_isHarmonicDistOn_of_isMarkovDecomposition hUle hd₁] with ω hω
    have e : (-h₁ ω) - (-G₁ (h₁ ω)) = -(h₁ ω - G₁ (h₁ ω)) := by abel
    rw [e]
    exact isHarmonicDistOn_neg hω
  have hd₂' : GFF.IsMarkovDecomposition (Restart.MarkovChart.chartPreOpens isConformal_infinityReturnChart
      (negInvOpens U' hU'H)) upperHalfPlaneOpens h₂ (fun ω => G₂ (h₂ ω)) P := by
    rw [chartPreOpens_return]
    exact hd₂
  have hh' : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      h₂ ω ψ = (-h₁ ω) (Chart.pushTest isConformal_infinityReturnChart ψ) + m ψ := fun ψ => by
    filter_upwards [hrel ψ] with ω hω
    rw [hω, WangWu.reflectField_apply, neg_apply]
  filter_upwards [Restart.MarkovChart.ae_markovCompl_pushTest_eq isConformal_infinityReturnChart hUH hUD hX hY
    hd₂' m hh' φ] with ω hω
  rw [markovCompl, sub_apply, hω, WangWu.reflectField_apply, markovCompl, sub_apply]
  simp only [neg_apply]
  ring

/-- **The harmonic parts along `R(U')` and `U'` as distributions**: `Y₂ = −Y₁ ∘ R + M` almost surely, for a
deterministic distribution `M`. -/
theorem exists_ae_markovCompl_reflect {h₁ h₂ : Ω → DistOn upperHalfPlaneOpens} (m : TestOn upperHalfPlaneOpens → ℝ)
    (hrel : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, h₂ ω φ = reflectField (h₁ ω) φ + m φ)
    {U' : TopologicalSpace.Opens ℂ} (hU'H : (U' : Set ℂ) ⊆ H)
    {G₁ G₂ : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd₁ : GFF.IsMarkovDecomposition (negInvOpens U' hU'H) upperHalfPlaneOpens h₁ (fun ω => G₁ (h₁ ω)) P)
    (hd₂ : GFF.IsMarkovDecomposition U' upperHalfPlaneOpens h₂ (fun ω => G₂ (h₂ ω)) P) :
    ∃ M : DistOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      markovCompl G₂ (h₂ ω) = reflectField (markovCompl G₁ (h₁ ω)) + M := by
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ × ℕ, markovCompl G₂ (h₂ ω) (LQGMetric.distGen upperHalfPlaneOpens j) =
      reflectField (markovCompl G₁ (h₁ ω)) (LQGMetric.distGen upperHalfPlaneOpens j) +
        m (LQGMetric.distGen upperHalfPlaneOpens j) :=
    ae_all_iff.2 fun j => ae_markovCompl_reflect m hrel hU'H hd₁ hd₂ _
  obtain ⟨ω₀, hω₀⟩ := hall.exists
  refine ⟨markovCompl G₂ (h₂ ω₀) - reflectField (markovCompl G₁ (h₁ ω₀)), ?_⟩
  filter_upwards [hall] with ω hω
  refine LQGMetric.injective_distOn_pairings upperHalfPlaneOpens (funext fun j => ?_)
  change markovCompl G₂ (h₂ ω) (LQGMetric.distGen upperHalfPlaneOpens j) =
    (reflectField (markovCompl G₁ (h₁ ω)) + (markovCompl G₂ (h₂ ω₀) - reflectField (markovCompl G₁ (h₁ ω₀))))
      (LQGMetric.distGen upperHalfPlaneOpens j)
  rw [add_apply, sub_apply, hω j, hω₀ j]
  ring

/-- `R(S)` avoids `U' ⊆ ℍ` iff `S ∩ ℍ` avoids `R(U')`. -/
theorem disjoint_image_negInv_iff {S U : Set ℂ} (hU : U ⊆ H) :
    Disjoint (negInv '' S) U ↔ Disjoint (S ∩ H) (negInv '' U) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, WangWu.image_negInv_inter_nonempty_iff]
  refine not_congr ⟨fun ⟨z, hzS, hzU⟩ => ⟨z, ⟨hzS, ?_⟩, hzU⟩, fun ⟨z, hz, hzU⟩ => ⟨z, hz.1, hzU⟩⟩
  obtain ⟨w, hw, rfl⟩ := hzU
  exact WangWu.negInv_mem_H (hU hw)

/-- **Lemma 6.2's walls criterion through `R`** (PROVE-STRIPSYS37 §5.1): if the walls `S` with information `X` satisfy
the determined-locality criterion for the zero-boundary GFF `h₁` (their own chart) along every open `U ⊆ ℍ`, and
`h₂ = −h₁ ∘ R + m` at every test function almost surely, then the reflected walls `R(S)` satisfy it for `h₂`. -/
theorem walls_reflect {𝒳 : Type*} [MeasurableSpace 𝒳] {X : Ω → 𝒳} {S : Ω → Set ℂ}
    {h₁ h₂ : Ω → DistOn upperHalfPlaneOpens} (hh₁ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₁ P)
    (m : TestOn upperHalfPlaneOpens → ℝ)
    (hrel : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, h₂ ω φ = reflectField (h₁ ω) φ + m φ)
    (hW₁ : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h₁ (fun ω => G (h₁ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (S ω ∩ H) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => markovCompl G (h₁ ω)) ⁻¹' B')
    (U' : TopologicalSpace.Opens ℂ) (G' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hU'H : (U' : Set ℂ) ⊆ H) (_hG' : Measurable G')
    (hd' : GFF.IsMarkovDecomposition U' upperHalfPlaneOpens h₂ (fun ω => G' (h₂ ω)) P)
    (B : Set 𝒳) (hB : MeasurableSet B) :
    ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
      {ω | Disjoint (negInv '' S ω) U'} ∩ X ⁻¹' B =ᵐ[P] (fun ω => markovCompl G' (h₂ ω)) ⁻¹' B' := by
  obtain ⟨G₁, hG₁m, hG₁⟩ := exists_markovMap (negInvOpens U' hU'H) (negInvOpens_subset_H U' hU'H)
  have hd₁ := hG₁ hh₁
  obtain ⟨B'', hB''m, hB''⟩ := hW₁ _ G₁ (negInvOpens_subset_H U' hU'H) hG₁m hd₁ B hB
  obtain ⟨M, hM⟩ := exists_ae_markovCompl_reflect m hrel hU'H hd₁ hd'
  refine ⟨(fun f => reflectField (f - M)) ⁻¹' B'',
    (WangWu.measurable_reflectField.comp (measurable_sub_const_distOn M)) hB''m, ?_⟩
  have e : {ω | Disjoint (negInv '' S ω) U'} ∩ X ⁻¹' B =
      {ω | Disjoint (S ω ∩ H) (negInvOpens U' hU'H)} ∩ X ⁻¹' B := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, coe_negInvOpens, disjoint_image_negInv_iff hU'H]
  rw [e]
  refine hB''.trans ?_
  filter_upwards [hM] with ω hω
  change (markovCompl G₁ (h₁ ω) ∈ B'') = (reflectField (markovCompl G' (h₂ ω) - M) ∈ B'')
  rw [hω, add_sub_cancel_right, WangWu.reflectField_reflectField]

end Transport

/-! ### The field of the counterflow chart -/

section Strip

open Sec7.StripSysField (infinityReturnChart isConformal_infinityReturnChart coe_dom_infinityReturnChart
  coe_dom_infinitySourceChart)

/-- The return chart and the infinity-source chart transport test functions in the same way. -/
theorem pushTest_return_eq_source' (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest isConformal_infinityReturnChart φ = Chart.pushTest Chart.isConformal_infinitySourceChart φ := by
  ext z
  rw [Chart.coe_pushTest, Chart.coe_pushTest, coe_dom_infinitySourceChart, coe_dom_infinityReturnChart]
  rfl

variable {Ω : Type*}

/-- **The centred counterflow-chart field is `−h_c ∘ R` plus a deterministic term** (from the frozen
`IsCenteredCounterflowDriver`'s infinity-source transport `h ↦ h'` and `IsFlowLineDriver`'s translate `h' ↦ h''`):
`centredField h'' u₀' = reflectField (centredField h u₀) + m` at every test function and every sample. -/
theorem exists_centredField_counterflow_eq {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ u₀' : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀' : InnerProductSpace.HarmonicOnNhd u₀' H) :
    ∃ m : TestOn upperHalfPlaneOpens → ℝ, ∀ (φ : TestOn upperHalfPlaneOpens) (ω : Ω),
      WholeField.centredField h'' u₀' ω φ = reflectField (WholeField.centredField h u₀ ω) φ + m φ := by
  refine ⟨fun φ => a * (∫ w, φ w) + k * (∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ w) +
    c * (∫ w, φ w) - (∫ z, u₀' z * φ z) - ∫ z, u₀ z * Chart.pushTest isConformal_infinityReturnChart φ z,
    fun φ ω => ?_⟩
  have htr : h'' ω φ = h' ω φ + c * ∫ z, φ z := hTr ω φ φ fun z => by rw [Complex.ofReal_zero, add_zero]
  have hch := (hT ω).apply_eq Chart.isConformal_infinitySourceChart φ
  rw [WholeField.centredField_apply h'' hu₀' ω φ, WangWu.reflectField_apply,
    WholeField.centredField_apply h hu₀ ω, htr, hch, ← pushTest_return_eq_source']
  ring

/-- **Lemma 6.2's walls criterion in the counterflow chart** (PROVE-STRIPSYS37 §5.1, blocker (b)): walls `η i` that
are determined by and entrance-history local for the centred flow-chart field `centredField h u₀` (a zero-boundary
GFF; `StripWall.lemma62_walls`) satisfy, after `R`, the determined-locality criterion for the centred field
`centredField h'' u₀'` of the counterflow chart, where `h'` is the infinity-source transport of `h` and `h''` its
translate by `0` (the frozen `IsCenteredCounterflowDriver`/`IsFlowLineDriver` data). This is the hypothesis `hW` of
`PocketStopWalls.pocketStopWallsLaw_of_coupling` with `X = fullHist η`. -/
theorem walls_hW_counterflow [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ u₀' : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀' : InnerProductSpace.HarmonicOnNhd u₀' H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    {n : ℕ} {η : Fin n → Ω → ℝ≥0 → ℂ} {x : Fin n → ℂ} (hc : ∀ i ω, Continuous (η i ω))
    (h0 : ∀ i ω, η i ω 0 = x i) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hloc : ∀ i, Sec6.IsEntranceHistoryLocal (η i) (WholeField.centredField h u₀) P)
    (U' : TopologicalSpace.Opens ℂ) (G' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hU'H : (U' : Set ℂ) ⊆ H) (hG' : Measurable G')
    (hd' : GFF.IsMarkovDecomposition U' upperHalfPlaneOpens (WholeField.centredField h'' u₀')
      (fun ω => G' (WholeField.centredField h'' u₀' ω)) P)
    (B : Set (Fin n → Sec6.Hist)) (hB : MeasurableSet B) :
    ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
      {ω | Disjoint (negInv '' ⋃ i, range (η i ω)) U'} ∩ Sec7.PocketStopWalls.fullHist η ⁻¹' B =ᵐ[P]
        (fun ω => markovCompl G' (WholeField.centredField h'' u₀' ω)) ⁻¹' B' := by
  obtain ⟨m, hm⟩ := exists_centredField_counterflow_eq hT hTr hu₀ hu₀'
  exact walls_reflect hh m (fun φ => ae_of_all _ fun ω => hm φ ω)
    (Sec7.PocketStopWalls.walls_determinedLocal hh.1 hc h0 hηm hdet hloc) U' G' hU'H hG' hd' B hB

end Strip

end InteractingSLE.Sec7.PocketStopWallsFin

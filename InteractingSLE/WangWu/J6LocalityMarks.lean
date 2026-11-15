/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72EDatum
import InteractingSLE.WangWu.J5ChartClausePocket

/-!
# Wang–Wu at `κ = 4`, (J6), I: the per-time history marks of the chamber on every three-line space

Packet PROVE-WW-B23. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.24
(text dump L1816–1867): "Proposition 4.20 applies at every stopping time in the filtration enlarged by the walls.
Therefore the transformed middle line `X` satisfies the local Markov coupling with these values."; the locality of the
hulls of the transformed middle line for the conditional field `h_ψ` rests on the history locality of the explored
union "walls ∪ middle prefix" (Proposition 4.20's "single-line determinism … give locality").

The specification's Lemma 7.1 proves the same per-time datum for its pocket (PROVE-LEMMA72E,
`Sec7.Lemma72E.exists_marks_of_isPocketConstruction`: Lemma 6.2 with labels for the stopped union
`β ∪ α ∪ γ[0, τ_t]` at the capacity stopping time `τ_t`, and G7). Those proofs use the three-curve space only through
Lemma 6.2's hypotheses on the three curves, the zero-boundary GFF property of the centred field and the pathwise good
event, i.e. through WW-B22's three-line space `SeedThree.IsThreeLineSpace`. This file restates them on every
three-line space (same proofs; each declaration notes its source):

* `comap_pair_le_three`, `isPrefixAdapted_three`, `adaptedBefore_three`, `measurableSet_lt_capLife_three`,
  `measurable_markedSet_three`: the measurability of the mapped middle segment in the filtration of the walls and the
  mapped middle prefix;
* **`exists_marks_three`** (R2′): for every capacity time `t` a σ-algebra of marks `ℋ_t` (the labelled stopped histories
  of the walls and the middle line, with the null sets) for which `B_t = ℍ ∖ ψ⁻¹(ℍ ∖ K_t)` is a history-marked local set
  of the centred field and `𝓐_t ≤ ℋ_t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.WangWu.ChamberCond

open Sec7 Sec7.Lemma71C Sec7.Lemma71E Sec7.Lemma71K Sec7.Lemma72E Sec6 LocalSets WholeField SeedThree

section Datum

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

-- mirrored from `Sec7.Lemma72E.comap_pair_le`
/-- `σ(β, α) ≤ mΩ` on a three-line space. -/
theorem comap_pair_le_three (hS : IsThreeLineSpace P h u₀ β α γ) :
    MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ mΩ := by
  obtain ⟨-, -, -, hβ62, hα62, -, -⟩ := hS
  exact ((measurable_pi_iff.2 hβ62.2.2.2.1).prodMk (measurable_pi_iff.2 hα62.2.2.2.1)).comap_le

-- mirrored from `Sec7.Lemma72E.isPrefixAdapted_of_isPocketConstruction`
/-- The mapped segment is prefix-adapted to its prefix filtration. -/
theorem isPrefixAdapted_three (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') :
    IsPrefixAdapted (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      γ' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hseg, hγ'm, -⟩ := hpc
  obtain ⟨-, -, -, hβ62, hα62, hγ62, -⟩ := hS
  have hβm : Measurable β := measurable_pi_iff.2 hβ62.2.2.2.1
  have hαm : Measurable α := measurable_pi_iff.2 hα62.2.2.2.1
  have hγm : Measurable γ := measurable_pi_iff.2 hγ62.2.2.2.1
  have h𝓑 : MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P ≤ mΩ :=
    sup_le (sup_le (sup_le hβm.comap_le hαm.comap_le) hγm.comap_le) (Ito.nullSets_le P)
  have hγ'mΩ : ∀ u, Measurable fun ω => γ' ω u := fun u => (hγ'm u).mono h𝓑 le_rfl
  exact isPrefixAdapted_prefixFiltrationOf _ γ' fun r n k =>
    measurableSet_prefixEvent hseg (fun u _ => hγ'mΩ u) r n k

-- mirrored from `Sec7.Lemma72E.adaptedBefore_of_isPocketConstruction`
/-- The capacity driver of the mapped segment is adapted before its terminal capacity to the prefix filtration. -/
theorem adaptedBefore_three (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') :
    AdaptedBefore (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun ω => capLife (γ' ω)) (fun s ω => segDriver (γ' ω) s) :=
  adaptedBefore_segDriver hpc.2.2.2.2.2.2.2.2.2.2.1 (isPrefixAdapted_three hS hpc)

-- mirrored from `Sec7.Lemma72E.measurableSet_lt_capLife_of_isPocketConstruction`
/-- `{t < T} ∈ 𝓐_t`. -/
theorem measurableSet_lt_capLife_three (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (t : ℝ≥0) :
    MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t]
      {ω | (t : ℝ≥0∞) < capLife (γ' ω)} :=
  measurableSet_lt_capLife (isPrefixAdapted_three hS hpc)
    (fun ω => (hpc.2.2.2.2.2.2.2.2.2.2.1 ω).2.2.2.1) t

-- mirrored from `Sec7.Lemma72E.measurable_markedSet_of_isPocketConstruction`
/-- **`B_t` is `𝓐_t`-measurable for the hitting σ-algebra.** -/
theorem measurable_markedSet_three (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (t : ℝ≥0) :
    Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t,
      hittingSigma] (markedSet (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) c t) :=
  measurable_markedSet (mΩ := mΩ) hpc.2.2.1 (measurableSet_closedBall_dom hpc) hpc.2.2.2.2.1
    (adaptedBefore_three hS hpc) (fun ω => (hpc.2.2.2.2.2.2.2.2.2.2.1 ω).segDriver_spec.2.1) t
    (le_prefixFiltrationOf (comap_pair_le_three hS) γ' t) (measurableSet_lt_capLife_three hS hpc t)

-- mirrored from `Sec7.Lemma72E.exists_marks_of_isPocketConstruction`
/-- **(R2′) on a three-line space: the per-time history-marked datum.** For every capacity time `t`, the σ-algebra
`ℋ_t` of the labelled stopped histories `(β, α, γ|[0, τ_t])` with the null sets (`τ_t` the capacity stopping time,
a path functional with Galmarino's property) makes `B_t = markedSet W T c t` a history-marked local set of the centred
field `h − u₀`, and contains the prefix filtration `𝓐_t` of the walls and the mapped middle prefix (G7). -/
theorem exists_marks_three [IsProbabilityMeasure P] (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (t : ℝ≥0) :
    ∃ ℋ : MeasurableSpace Ω, ℋ ≤ mΩ ∧
      IsHistoryAvoidanceLocal (mΩ := mΩ) ℋ (markedSet (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) c t)
        (centredField h u₀) P ∧
      prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t ≤ ℋ := by
  obtain ⟨G, M, Y, hG, hM, hY, hMiff, hGeq, hYeq⟩ := exists_capData_three hS hpc
  have hS' := hS
  obtain ⟨-, -, hh0, hβ62, hα62, hγ62, -⟩ := hS'
  obtain ⟨hc, h0, -, hηm, hdet, hloc, -⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  set τ : Ω → ℝ≥0∞ := Lemma71L.capTime G M Y β α γ t with hτdef
  have hSm := Three.measurable_threeRule (Lemma71L.measurable_capStop hG hM hY t)
  have hSg := Three.isGalmarino_threeRule (Lemma71L.capStop_galmarino (G := G) (M := M) (Y := Y) t)
  have hτ := Three.threeStops_eq_threeRule (β := β) (α := α) (γ := γ) (τ := τ)
    (S := Lemma71L.capStop G M Y t) (fun _ => rfl)
  have hstops : ∀ i, Measurable (Three.threeStops τ i) := measurable_of_galmarino hηm hSm hSg hτ
  have hℋ₀ : stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ) ≤ mΩ :=
    stoppedHistSigma_le hηm hstops
  have hHA : IsHistoryAvoidanceLocal (stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ))
      (explored (Three.threeCurves β α γ) (Three.threeStops τ)) (centredField h u₀) P :=
    isHistoryAvoidanceLocal_explored hh0.measurable hc h0 hηm hdet hloc hSm hSg hτ
  have hHA' := isHistoryAvoidanceLocal_sup_nullSets (P := P) (isHistoryAvoidanceLocal_inter_H hHA)
  -- G7
  have h𝓐ℋ : prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t ≤
      stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ) ⊔ Ito.nullSets P :=
    le_sup_nullSets_of_le_aeSigma ((prefixFiltrationOf (mΩ := mΩ) _ γ').le t) hℋ₀
      (prefixFiltrationOf_le_aeSigma_three hS hpc hG hM hY hMiff hGeq hYeq t)
  refine ⟨stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ) ⊔ Ito.nullSets P,
    sup_le hℋ₀ (Ito.nullSets_le P), ?_, h𝓐ℋ⟩
  refine Lemma72C.isHistoryAvoidanceLocal_mono_set hHA'
    ((measurable_markedSet_three hS hpc t).mono h𝓐ℋ le_rfl) ?_
  -- the explored set lies in `B_t`
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, hseg, -, -⟩ := hpc'
  filter_upwards [ae_pocketGood_three hS hpc] with ω hg
  rintro z ⟨hzA, hzH⟩
  refine ⟨hzH, ?_⟩
  by_cases ht : (t : ℝ≥0∞) < capLife (γ' ω)
  · rw [openPart_of_lt (ζ := fun ω => capLife (γ' ω)) (ω := ω) ht]
    intro hz
    obtain ⟨hz', -⟩ := Lemma71L.connectedComponentIn_eq_image hg (hC ω).1 (hC ω).2.2.2 (hconf ω) (hdom ω)
      (fun s => hγ62.2.2.1 ω s) (hγ62.1 ω) (hγ62.2.1 ω) (hseg ω) (hMiff ω) (hGeq ω) (hYeq ω) ht hz
    exact hz'.2 hzA
  · rw [openPart_of_not_lt (ζ := fun ω => capLife (γ' ω)) (ω := ω) ht, image_empty]
    exact notMem_empty z

end Datum

end InteractingSLE.WangWu.ChamberCond

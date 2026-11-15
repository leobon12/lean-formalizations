/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72EHit
import InteractingSLE.Spec.Sec7.Lemma71LComp
import InteractingSLE.Spec.Sec7.Lemma71KData
import InteractingSLE.Spec.Sec6.Prop61BMarked
import InteractingSLE.Spec.Sec6.Prop61Three

/-!
# Lemma 7.1's joint law, last steps, III: the per-time history-marked datum (R2′)

Packet PROVE-LEMMA72E. Specification §7.1, proof of Lemma 7.1 (`source/spec/p193-240.md` L598–L606, pp. 224–225):
"For each bounded stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies to the
revealed outer curves and the middle prefix. Their original prefixes have no original-boundary contacts, so their
stopped ranges equal their stopped hulls; the optional history marking of the original coupling supplies the required
history locality."

On a three-curve space with a pocket construction `(C, c, γ')` (PROVE-LEMMA71K), let `𝓐 = prefixFiltrationOf σ(β, α) γ'`
be the prefix filtration of the mapped segment, `W` its capacity driver, `T` its terminal capacity and
`B_t = markedSet W T c t = ℍ ∖ ψ⁻¹(V_t)`. For every fixed `t` (`exists_marks_of_isPocketConstruction`) there is a
σ-algebra of marks `ℋ_t ≤ mΩ` with
* `B_t` a history-marked local set of the centred field `h − u₀` for the marks `ℋ_t`;
* `𝓐_t ≤ ℋ_t` (G7).

Here `ℋ_t` is the σ-algebra of the labelled stopped histories `(β, α, γ|[0, τ_t])` with the null sets added, `τ_t` the
capacity stopping time of PROVE-LEMMA71L (`Lemma71L.capTime`, a path functional with Galmarino's property, ruling
R37). Proof: Lemma 6.2 with labels (`Sec6.isHistoryAvoidanceLocal_explored`) for the explored set
`A(τ_t) = β ∪ α ∪ γ([0, τ_t])`; its trace in `ℍ` lies in `B_t` almost surely (before the terminal capacity, every point
of `ψ⁻¹(ℍ ∖ K_t)` lies off `A(τ_t)`: `Lemma71L.connectedComponentIn_eq_image`; after it `B_t = ℍ`); `B_t` is
`𝓐_t`-measurable for the hitting σ-algebra (`measurable_markedSet`); G7 is PROVE-LEMMA71L's
`prefixFiltrationOf_le_aeSigma` (the same G7 as in its fixed-time clause), with the null sets made explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.Lemma72E

open Lemma71C Lemma71E Lemma71K Sec6 LocalSets WholeField

section Datum

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- `σ(β, α) ≤ mΩ` on a three-curve space. -/
theorem comap_pair_le (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) :
    MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ mΩ := by
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, -, -⟩ := hS
  exact ((measurable_pi_iff.2 hβ62.2.2.2.1).prodMk (measurable_pi_iff.2 hα62.2.2.2.1)).comap_le

/-- The mapped segment is prefix-adapted to its prefix filtration. -/
theorem isPrefixAdapted_of_isPocketConstruction (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') :
    IsPrefixAdapted (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      γ' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hseg, hγ'm, -⟩ := hpc
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, hγ62, -⟩ := hS
  have hβm : Measurable β := measurable_pi_iff.2 hβ62.2.2.2.1
  have hαm : Measurable α := measurable_pi_iff.2 hα62.2.2.2.1
  have hγm : Measurable γ := measurable_pi_iff.2 hγ62.2.2.2.1
  have h𝓑 : MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P ≤ mΩ :=
    sup_le (sup_le (sup_le hβm.comap_le hαm.comap_le) hγm.comap_le) (Ito.nullSets_le P)
  have hγ'mΩ : ∀ u, Measurable fun ω => γ' ω u := fun u => (hγ'm u).mono h𝓑 le_rfl
  exact isPrefixAdapted_prefixFiltrationOf _ γ' fun r n k =>
    measurableSet_prefixEvent hseg (fun u _ => hγ'mΩ u) r n k

/-- The capacity driver of the mapped segment is adapted before its terminal capacity to the prefix filtration. -/
theorem adaptedBefore_of_isPocketConstruction (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') :
    AdaptedBefore (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun ω => capLife (γ' ω)) (fun s ω => segDriver (γ' ω) s) :=
  adaptedBefore_segDriver hpc.2.2.2.2.2.2.2.2.2.2.1 (isPrefixAdapted_of_isPocketConstruction hS hpc)

/-- `{t < T} ∈ 𝓐_t`. -/
theorem measurableSet_lt_capLife_of_isPocketConstruction
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) (hpc : IsPocketConstruction P β α γ C c γ')
    (t : ℝ≥0) :
    MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t]
      {ω | (t : ℝ≥0∞) < capLife (γ' ω)} :=
  measurableSet_lt_capLife (isPrefixAdapted_of_isPocketConstruction hS hpc)
    (fun ω => (hpc.2.2.2.2.2.2.2.2.2.2.1 ω).2.2.2.1) t

/-- Closed-ball events of the chart domain are `σ(β, α)`-events. -/
theorem measurableSet_closedBall_dom (hpc : IsPocketConstruction P β α γ C c γ') (z : ℂ) (r : ℝ) :
    MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | closedBall z r ⊆ ((c ω).dom : Set ℂ)} := by
  obtain ⟨-, hCm, -, hdom, -⟩ := hpc
  have e : {ω | closedBall z r ⊆ ((c ω).dom : Set ℂ)} = {ω | closedBall z r ⊆ C ω} := by
    ext ω
    show closedBall z r ⊆ ((c ω).dom : Set ℂ) ↔ _
    rw [hdom ω]
    exact Iff.rfl
  rw [e]
  exact hCm z r

/-- **`B_t` is `𝓐_t`-measurable for the hitting σ-algebra.** -/
theorem measurable_markedSet_of_isPocketConstruction
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) (hpc : IsPocketConstruction P β α γ C c γ')
    (t : ℝ≥0) :
    Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t,
      hittingSigma] (markedSet (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) c t) :=
  measurable_markedSet (mΩ := mΩ) hpc.2.2.1 (measurableSet_closedBall_dom hpc) hpc.2.2.2.2.1
    (adaptedBefore_of_isPocketConstruction hS hpc) (fun ω => (hpc.2.2.2.2.2.2.2.2.2.2.1 ω).segDriver_spec.2.1) t
    (le_prefixFiltrationOf (comap_pair_le hS) γ' t) (measurableSet_lt_capLife_of_isPocketConstruction hS hpc t)

/-- **(R2′): the per-time history-marked datum** (see the module docstring). -/
theorem exists_marks_of_isPocketConstruction [IsProbabilityMeasure P]
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) (hpc : IsPocketConstruction P β α γ C c γ')
    (t : ℝ≥0) :
    ∃ ℋ : MeasurableSpace Ω, ℋ ≤ mΩ ∧
      IsHistoryAvoidanceLocal (mΩ := mΩ) ℋ (markedSet (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) c t)
        (centredField h u₀) P ∧
      prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t ≤ ℋ := by
  obtain ⟨G, M, Y, hG, hM, hY, hMiff, hGeq, hYeq⟩ := Lemma71L.exists_capData hS hpc
  have hS' := hS
  obtain ⟨-, -, hh0, -, -, -, hβ62, hα62, hγ62, -⟩ := hS'
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
      (Lemma71L.prefixFiltrationOf_le_aeSigma hS hpc hG hM hY hMiff hGeq hYeq t)
  refine ⟨stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ) ⊔ Ito.nullSets P,
    sup_le hℋ₀ (Ito.nullSets_le P), ?_, h𝓐ℋ⟩
  refine Lemma72C.isHistoryAvoidanceLocal_mono_set hHA'
    ((measurable_markedSet_of_isPocketConstruction hS hpc t).mono h𝓐ℋ le_rfl) ?_
  -- the explored set lies in `B_t`
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, hseg, -, -⟩ := hpc'
  filter_upwards [Lemma71L.ae_pocketGood hS hpc] with ω hg
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

end InteractingSLE.Sec7.Lemma72E

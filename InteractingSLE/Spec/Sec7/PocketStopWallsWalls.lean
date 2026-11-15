/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsCore
import InteractingSLE.Spec.Sec6.CondMeanStop

/-!
# The walls' input of the union law: Lemma 6.2 for fully explored, field-determined paths

Packet PROVE-STRIPSYS37. Specification §6.1, Lemma 6.2 (`source/spec/p145-192.md#lem-6.2`, p. 155): for paths
`η_1, …, η_k` with deterministic starts, determined by `h` and history-sensitively local, "the event
`{⋃ η_i([0, τ_i]) ∩ U = ∅}` and, on this event, the entire ordered tuple of stopped histories are determined by
`h_{U^c}`". With every `τ_i = ∞` (the walls fully explored) this is exactly the walls' hypothesis `hW` of
`PocketStopWalls.isHistoryAvoidanceLocal_walls_hull`:

* `fullHist η ω`: the ordered tuple of full histories `(∞, η_i|_{ℚ≥0})`;
* **`walls_determinedLocal`**: for every open `U ⊆ ℍ`, every Borel version `G` of the projection onto `H(U)` and every
  measurable set `B` of history tuples, `{⋃ range η_i ∩ U = ∅} ∩ {fullHist η ∈ B}` is almost surely an event of
  `h − G h` (`Sec6.le_aeSigma_explored` with the constant stopping times `∞`);
* `measurable_wallsRange`: the walls' union `⋃ range η_i ∩ ℍ` is hitting-measurable.

For the strip walls `α`, `β^{(q)}` the hypotheses of Lemma 6.2 are `StripWall.lemma62_walls` (field determination and
entrance-history locality for the centred flow-chart field). Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopWalls

open QuantumZipper (H)
open LQGMetric (DistOn)
open LocalSets Sec6

section Walls

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ} {x : Fin k → ℂ}

/-- The ordered tuple of the full histories `(∞, η_i|_{ℚ≥0})`. -/
def fullHist (η : Fin k → Ω → ℝ≥0 → ℂ) (ω : Ω) : Fin k → Hist :=
  fun i => histOf (pathCoord (η i ω)) ⊤

omit [IsProbabilityMeasure P] in
theorem measurable_fullHist (hηm : ∀ i t, Measurable fun ω => η i ω t) : Measurable (fullHist η) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hc : Measurable fun ω => pathCoord (η i ω) := Measurable.of_eval fun q => hηm i (q : ℝ≥0)
  exact measurable_histOf.comp (measurable_const.prodMk hc)

omit mΩ [IsProbabilityMeasure P] in
/-- The explored set of the fully explored paths is the union of their ranges in `ℍ`. -/
theorem explored_top (η : Fin k → Ω → ℝ≥0 → ℂ) (ω : Ω) :
    explored η (fun _ _ => ⊤) ω = (⋃ i, range (η i ω)) ∩ H := by
  simp only [explored, le_top, ofPred_true, image_univ]

omit [IsProbabilityMeasure P] in
/-- The walls' union in `ℍ` is hitting-measurable. -/
theorem measurable_wallsRange (hc : ∀ i ω, Continuous (η i ω)) (hηm : ∀ i t, Measurable fun ω => η i ω t) :
    Measurable[mΩ, hittingSigma] fun ω => (⋃ i, range (η i ω)) ∩ H := by
  have h := measurable_explored (η := η) (τ := fun _ _ => (⊤ : ℝ≥0∞)) hc hηm (fun _ => measurable_const)
  rwa [show explored η (fun _ _ => (⊤ : ℝ≥0∞)) = fun ω => (⋃ i, range (η i ω)) ∩ H from
    funext (explored_top η)] at h

/-- **Lemma 6.2 for the walls fully explored** (determined locality with the full histories as marks): for every open
`U ⊆ ℍ` and every Markov map `G`, every event `{⋃ range η_i ∩ U = ∅} ∩ {fullHist η ∈ B}` is almost surely an event of
the Markov complement `h − G h`. -/
theorem walls_determinedLocal (hhm : Measurable h) (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i)
    (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (B : Set (Fin k → Hist)) (hB : MeasurableSet B) :
    ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
      {ω | Disjoint ((⋃ i, range (η i ω)) ∩ H) U} ∩ fullHist η ⁻¹' B =ᵐ[P]
        (fun ω => markovCompl G (h ω)) ⁻¹' B' := by
  have hle := (le_aeSigma_explored (τ := fun _ _ => ⊤) (S := fun _ _ _ => ⊤) hhm hc h0 hηm hdet hloc
    (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) U G hUH hG hd).1
  have hmem : MeasurableSet[markedHistSigma {ω | Disjoint (explored η (fun _ _ => ⊤) ω) U}
      (fun ω i => histOf (pathCoord (η i ω)) ⊤)]
      ({ω | Disjoint (explored η (fun _ _ => ⊤) ω) U} ∩ fullHist η ⁻¹' B) :=
    MeasurableSpace.measurableSet_generateFrom ⟨B, hB, rfl⟩
  obtain ⟨S', hS', hSe⟩ := hle _ hmem
  obtain ⟨B', hB', rfl⟩ := hS'
  refine ⟨B', hB', ?_⟩
  simpa only [explored_top] using hSe

end Walls

end InteractingSLE.Sec7.PocketStopWalls

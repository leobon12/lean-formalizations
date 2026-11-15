/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.DeterminationMixture
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Sec4.Special3Thin

/-!
# One common graph, and a unique field–history law (§D.2.3)

Packet PROVE-AUX52-55. Source: §D.2.3 of `source/external/AstraIG1/ig1_followup_proofs.txt` (ruling R38),
lines 2028–2042:

"Suppose every coupling with the fixed original optional-hull specification has a field-determined driver. Then all
those couplings use the same measurable graph modulo the fixed field law. Indeed, mix two such couplings by an
independent fair coin. […] If the two graphs differed on a positive-field-measure set, the mixed conditional driver
law there would not be a point mass. This contradicts the assumed universal determination. Hence the full
field–driver joint law is unique."

The same step closes the proof of Aux. lemma 55 (`source/spec/p241-288.md` L224, p. 250: "Its determining function is
the same for every such reference coupling").

## Main results

* `exists_common_graph`: under universal determination for the force word (`LP.HasFieldDeterminedHistories`), any
  two couplings satisfying the frozen optional hull specification have **one** measurable graph `Ψ` of the killed
  driving history: the mixture of the two couplings (`IsOptionalHullCoupling.mix`, `DeterminationMixture.lean`) is
  again a coupling, its graph serves both pieces;
* `map_field_eq`: the field has the same law in every coupling (the centred field is a zero-boundary GFF, whose law
  is unique: `LQGMetric.IsZBGFFProcess.map_eq`);
* `map_field_killedHistory_eq`: under universal determination, **the joint law of the field and the killed driving
  history is the same in every coupling** of the force word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Determination

open LQGMetric

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω₁ Ω₂ : Type u} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
  {W₁ : ℝ≥0 → Ω₁ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
  {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₁ : Ω₁ → ℝ≥0∞} {ζ₂ : Ω₂ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- `Ψ` is a graph of the killed driving history `(ζ, W, V^L, V^R)` of a coupling with field `h`: almost surely
`Ψ(h)` is the lifetime, and the driving and force coordinates at every time before the lifetime (the body of
`LP.IsFieldDeterminedHistory`). -/
def IsHistoryGraph {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (Ψ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) : Prop :=
  ∀ᵐ ω ∂P, (Ψ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
    (Ψ (h ω)).2.1 t = W t ω ∧ (∀ i, (Ψ (h ω)).2.2.1 i t = VL i t ω) ∧ ∀ i, (Ψ (h ω)).2.2.2 i t = VR i t ω

theorem isFieldDeterminedHistory_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    LP.IsFieldDeterminedHistory P h W VL VR ζ ↔ ∃ Ψ, Measurable Ψ ∧ IsHistoryGraph P h W VL VR ζ Ψ :=
  Iff.rfl

/-- **One common graph** (§D.2.3). Under universal determination for the force word, two couplings satisfying the
frozen optional hull specification have one measurable graph of their killed driving histories. -/
theorem exists_common_graph [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR)
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    ∃ Ψ, Measurable Ψ ∧ IsHistoryGraph P₁ h₁ W₁ VL₁ VR₁ ζ₁ Ψ ∧ IsHistoryGraph P₂ h₂ W₂ VL₂ VR₂ ζ₂ Ψ := by
  obtain ⟨Ψ, hΨ, hgraph⟩ := hdet (mixMeasure P₁ P₂) (sumFiltration 𝓕₁ 𝓕₂) (mixProc W₁ W₂)
    (fun i => mixProc (VL₁ i) (VL₂ i)) (fun i => mixProc (VR₁ i) (VR₂ i)) (mixProc B₁ B₂) (Sum.elim ζ₁ ζ₂)
    (Sum.elim h₁ h₂) (IsOptionalHullCoupling.mix hC₁ hC₂)
  obtain ⟨g₁, g₂⟩ := ae_mixMeasure_iff.1 hgraph
  exact ⟨Ψ, hΨ, g₁, g₂⟩

/-- **The field law is the same in every coupling** of a force word: the centred field is a zero-boundary GFF, whose
law on the cylinder σ-algebra is unique. -/
theorem map_field_eq [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    P₁.map h₁ = P₂.map h₂ := by
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have g₁ := hC₁.2.2.1 u₀ hu₀
  have g₂ := hC₂.2.2.1 u₀ hu₀
  have e := g₁.map_eq g₂
  obtain ⟨c, hc⟩ : ∃ c : TestOn upperHalfPlaneOpens → ℝ, c = fun φ => ∫ z, u₀ z * φ z := ⟨_, rfl⟩
  have hadd : Measurable fun f : TestOn upperHalfPlaneOpens → ℝ => f + c := measurable_id.add_const c
  have hd₁ : distEval upperHalfPlaneOpens ∘ h₁ = (fun f => f + c) ∘ zbPath (fun φ ω => h₁ ω φ - ∫ z, u₀ z * φ z) := by
    funext ω φ; simp [zbPath, distEval, hc]
  have hd₂ : distEval upperHalfPlaneOpens ∘ h₂ = (fun f => f + c) ∘ zbPath (fun φ ω => h₂ ω φ - ∫ z, u₀ z * φ z) := by
    funext ω φ; simp [zbPath, distEval, hc]
  have hz₁ : Measurable (zbPath (fun φ ω => h₁ ω φ - ∫ z, u₀ z * φ z)) := measurable_pi_iff.2 g₁.measurable
  have hz₂ : Measurable (zbPath (fun φ ω => h₂ ω φ - ∫ z, u₀ z * φ z)) := measurable_pi_iff.2 g₂.measurable
  have hD : P₁.map (distEval upperHalfPlaneOpens ∘ h₁) = P₂.map (distEval upperHalfPlaneOpens ∘ h₂) := by
    rw [hd₁, hd₂, ← Measure.map_map hadd hz₁, ← Measure.map_map hadd hz₂, e]
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hS : MeasurableSet (distEval upperHalfPlaneOpens ⁻¹' t) := measurable_distEval _ ht
  have := congrArg (fun μ : Measure (TestOn upperHalfPlaneOpens → ℝ) => μ t) hD
  rw [Measure.map_apply ((measurable_distEval _).comp hC₁.2.1) ht,
    Measure.map_apply ((measurable_distEval _).comp hC₂.2.1) ht] at this
  change (P₁.map h₁) (distEval upperHalfPlaneOpens ⁻¹' t) = (P₂.map h₂) (distEval upperHalfPlaneOpens ⁻¹' t)
  rw [Measure.map_apply hC₁.2.1 hS, Measure.map_apply hC₂.2.1 hS]
  exact this

/-- The killed driving history `(ζ, t ↦ (W_t, V^L_t, V^R_t) 1_{t < ζ})` (the value `0` from `ζ` on). -/
def killedHistory {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ × (ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  (ζ ω, fun t => if (t : ℝ≥0∞) < ζ ω then (W t ω, (fun i => VL i t ω), fun i => VR i t ω) else 0)

/-- The killed history read from a graph value. -/
def graphHistory (p : ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) :
    ℝ≥0∞ × (ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  (p.1, fun t => if (t : ℝ≥0∞) < p.1 then (p.2.1 t, (fun i => p.2.2.1 i t), fun i => p.2.2.2 i t) else 0)

theorem measurable_graphHistory : Measurable (graphHistory (nL := nL) (nR := nR)) := by
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun t => ?_)
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  refine ((measurable_pi_apply t).comp measurable_snd.fst).prodMk
    ((measurable_pi_iff.2 fun i => (measurable_pi_apply t).comp ((measurable_pi_apply i).comp
      measurable_snd.snd.fst)).prodMk
    (measurable_pi_iff.2 fun i => (measurable_pi_apply t).comp ((measurable_pi_apply i).comp
      measurable_snd.snd.snd)))

theorem IsHistoryGraph.killedHistory_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {Ψ} (hΨ : IsHistoryGraph P h W VL VR ζ Ψ) :
    killedHistory W VL VR ζ =ᵐ[P] fun ω => graphHistory (Ψ (h ω)) := by
  filter_upwards [hΨ] with ω ⟨hz, hpath⟩
  refine Prod.ext hz.symm (funext fun t => ?_)
  simp only [killedHistory, graphHistory, hz]
  split_ifs with ht
  · obtain ⟨e1, e2, e3⟩ := hpath t ht
    simp only [e1, e2, e3]
  · rfl

/-- **The field–history joint law is unique** (§D.2.3: "Hence the full field–driver joint law is unique"). Under
universal determination for the force word, any two couplings satisfying the frozen optional hull specification
have the same joint law of the field and the killed driving history. -/
theorem map_field_killedHistory_eq [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR)
    (hC₁ : IsOptionalHullCoupling κ xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (hC₂ : IsOptionalHullCoupling κ xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂) :
    P₁.map (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      P₂.map (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
  obtain ⟨Ψ, hΨ, g₁, g₂⟩ := exists_common_graph hdet hC₁ hC₂
  have hG : Measurable fun d => (d, graphHistory (Ψ d)) := measurable_id.prodMk (measurable_graphHistory.comp hΨ)
  have a₁ : (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =ᵐ[P₁]
      (fun d => (d, graphHistory (Ψ d))) ∘ h₁ := by
    filter_upwards [g₁.killedHistory_ae_eq] with ω hω
    simp only [Function.comp_apply, hω]
  have a₂ : (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =ᵐ[P₂]
      (fun d => (d, graphHistory (Ψ d))) ∘ h₂ := by
    filter_upwards [g₂.killedHistory_ae_eq] with ω hω
    simp only [Function.comp_apply, hω]
  rw [Measure.map_congr a₁, Measure.map_congr a₂, ← Measure.map_map hG hC₁.2.1, ← Measure.map_map hG hC₂.2.1,
    map_field_eq hC₁ hC₂]

end Determination

end InteractingSLE

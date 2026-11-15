/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedContBM
import InteractingSLE.Spec.Restart.StoppedContPos
import InteractingSLE.Spec.Restart.StoppedExtendWFLaw

/-!
# (CONT): the continuation of a stopped evolution

Packet PROVE-WFS0, input (CONT) of `planning/handoffs/PROVE-DOMAINMARKOV10.md` §4.1, proved for every `κ > 0`
(**`stoppedContinuationStatement`**). Let `(W, V^{·,L}, V^{·,R})` be a local integrated evolution before `V`
(`Sec2.IsSLEEvolutionUpTo`), continuous through a finite `V`. On `Ω × Ω₀`, with `P ⊗ P₀`, where `(Ω₀, P₀)` carries a
full integrated evolution `E₀` of the same word (Theorem 2.2's existence), the continuation is

* on `{V = 0}`: the evolution `E₀` of the second factor, driven by its own Brownian motion;
* on `{V > 0}`: the positive part `StoppedCont.exists_posCont` of the first factor (the local path, completed at
  `V = ∞`, stopped at a bad `V`, and continued by the maximal solution after a good `V`), driven by a continuous version
  of `B`.

The filtration is the product of the usual augmentation of `𝓕` and the filtration of `E₀`; the switched Brownian
motion is Brownian there (`IsFilteredBrownianReal.switch`, the event `{V = 0}` being in `𝓕₀`), and the switched
coordinates are adapted before the switched lifetime. The first marginal is `P`, the lifetime is at least `V`, and the
coordinates agree with the local ones before `V`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace StoppedCont

open WholeField StoppedExtendWF

section Switch

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀]

/-- **Adaptedness before the lifetime, switched on a first-factor event of `𝓖₀`.** -/
theorem adaptedBefore_switch {𝓖 : Filtration ℝ≥0 mΩ} {𝓦 : Filtration ℝ≥0 m₀} {Z : Set Ω} [DecidablePred (· ∈ Z)]
    (hZ : MeasurableSet[𝓖 0] Z) {ζ₁ : Ω → ℝ≥0∞} {X₁ : ℝ≥0 → Ω → ℝ} (h₁ : AdaptedBefore 𝓖 ζ₁ X₁)
    {ζ₀ : Ω₀ → ℝ≥0∞} {X₀ : ℝ≥0 → Ω₀ → ℝ} (h₀ : AdaptedBefore 𝓦 ζ₀ X₀) :
    AdaptedBefore (prodFiltration 𝓖 𝓦) (fun p => if p.1 ∈ Z then ζ₀ p.2 else ζ₁ p.1)
      (fun t p => if p.1 ∈ Z then X₀ t p.2 else X₁ t p.1) := by
  intro t A hA
  have hZt : MeasurableSet[prodFiltration 𝓖 𝓦 t] (Prod.fst ⁻¹' Z) :=
    comap_fst_le_prodFiltration 𝓖 𝓦 t _ ⟨Z, 𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t) Z hZ, rfl⟩
  have h0 : MeasurableSet[prodFiltration 𝓖 𝓦 t]
      (Prod.snd ⁻¹' {ω₀ | (t : ℝ≥0∞) < ζ₀ ω₀ ∧ X₀ t ω₀ ∈ A}) :=
    (le_sup_right : (𝓦 t).comap Prod.snd ≤ prodFiltration 𝓖 𝓦 t) _ ⟨_, h₀ t A hA, rfl⟩
  have h1 : MeasurableSet[prodFiltration 𝓖 𝓦 t]
      (Prod.fst ⁻¹' {ω | (t : ℝ≥0∞) < ζ₁ ω ∧ X₁ t ω ∈ A}) :=
    comap_fst_le_prodFiltration 𝓖 𝓦 t _ ⟨_, h₁ t A hA, rfl⟩
  have e : {p : Ω × Ω₀ | (t : ℝ≥0∞) < (if p.1 ∈ Z then ζ₀ p.2 else ζ₁ p.1) ∧
      (if p.1 ∈ Z then X₀ t p.2 else X₁ t p.1) ∈ A} =
      (Prod.fst ⁻¹' Z ∩ Prod.snd ⁻¹' {ω₀ | (t : ℝ≥0∞) < ζ₀ ω₀ ∧ X₀ t ω₀ ∈ A}) ∪
        ((Prod.fst ⁻¹' Z)ᶜ ∩ Prod.fst ⁻¹' {ω | (t : ℝ≥0∞) < ζ₁ ω ∧ X₁ t ω ∈ A}) := by
    ext p
    by_cases hp : p.1 ∈ Z <;> simp [hp]
  rw [e]
  exact (hZt.inter h0).union (hZt.compl.inter h1)

end Switch

/-- **(CONT) holds for every `κ > 0`**: a local integrated evolution before `V`, continuous through a finite `V`, is
the restriction of a full integrated evolution on `Ω × Ω₀` whose lifetime is at least `V`. -/
theorem stoppedContinuationStatement {κ : ℝ} (hκ : 0 < κ) : StoppedContinuationStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF Ω mΩ P hP 𝓕 W VL VR B V hE hc
  classical
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled (ρL := ρL) (ρR := ρR) hκ hF
  obtain ⟨B₁, W₁, VL₁, VR₁, ζ₁, hB₁, hW₁, hL₁, hR₁, hpath₁⟩ := exists_posCont hκ hF hE hc
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  set Z : Set Ω := {ω | V ω = 0} with hZdef
  have hZ : MeasurableSet[𝓖 0] Z := by
    have h := (hE.adapted_W 0 univ MeasurableSet.univ).compl
    have e : {ω | ((0 : ℝ≥0) : ℝ≥0∞) < V ω ∧ W 0 ω ∈ univ}ᶜ = Z := by
      ext ω
      simp only [hZdef, mem_compl_iff, mem_ofPred_eq, mem_univ, and_true, ENNReal.coe_zero, not_lt,
        nonpos_iff_eq_zero]
    rw [e] at h
    exact Ito.le_usualAugmentation 𝓕 P 0 _ h
  -- the product space and the switched processes
  have hmap₁ : (P.prod P₀).map Prod.fst = P := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmap₀ : (P.prod P₀).map Prod.snd = P₀ := by rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hq₁ : Measure.QuasiMeasurePreserving Prod.fst (P.prod P₀) P :=
    ⟨measurable_fst, hmap₁.le.absolutelyContinuous⟩
  have hq₀ : Measure.QuasiMeasurePreserving Prod.snd (P.prod P₀) P₀ :=
    ⟨measurable_snd, hmap₀.le.absolutelyContinuous⟩
  have hZ' : MeasurableSet[prodFiltration 𝓖 𝓕₀ 0] (Prod.fst ⁻¹' Z) :=
    comap_fst_le_prodFiltration 𝓖 𝓕₀ 0 _ ⟨Z, hZ, rfl⟩
  have hBM := IsFilteredBrownianReal.switch (isFilteredBrownianReal_prod_fst (P₀ := P₀) 𝓕₀ hB₁)
    (isFilteredBrownianReal_prod_snd (P := P) 𝓖 hE₀.1) hZ'
  refine ⟨Ω × Ω₀, inferInstance, P.prod P₀, inferInstance, Prod.fst, measurable_fst, prodFiltration 𝓖 𝓕₀,
    fun t p => if p.1 ∈ Z then W₀ t p.2 else W₁ t p.1,
    fun i t p => if p.1 ∈ Z then VL₀ i t p.2 else VL₁ i t p.1,
    fun j t p => if p.1 ∈ Z then VR₀ j t p.2 else VR₁ j t p.1,
    fun t p => if p ∈ Prod.fst ⁻¹' Z then B₀ t p.2 else B₁ t p.1,
    fun p => if p.1 ∈ Z then ζ₀ p.2 else ζ₁ p.1, hmap₁, ⟨hBM, adaptedBefore_switch hZ hW₁ hE₀.2.1,
      fun i => adaptedBefore_switch hZ (hL₁ i) (hE₀.2.2.1 i), fun j => adaptedBefore_switch hZ (hR₁ j) (hE₀.2.2.2.1 j),
      ?_⟩, ?_⟩
  · filter_upwards [hq₁.ae hpath₁, hq₀.ae hE₀.2.2.2.2] with p h1 h0
    by_cases hp : p.1 ∈ Z
    · have hp' : p ∈ Prod.fst ⁻¹' Z := hp
      simp only [hp, hp', ↓reduceIte]
      exact h0
    · have hp' : p ∉ Prod.fst ⁻¹' Z := hp
      have hV0 : 0 < V p.1 := pos_iff_ne_zero.2 hp
      simp only [hp, hp', ↓reduceIte]
      exact (h1 hV0).1
  · filter_upwards [hq₁.ae hpath₁] with p h1
    by_cases hp : p.1 ∈ Z
    · have hV0 : V p.1 = 0 := hp
      simp only [hp, ↓reduceIte, hV0, zero_le, true_and]
      intro t ht
      exact absurd ht ENNReal.not_lt_zero
    · have hV0 : 0 < V p.1 := pos_iff_ne_zero.2 hp
      simp only [hp, ↓reduceIte]
      exact ⟨(h1 hV0).2.1, (h1 hV0).2.2⟩

end StoppedCont

end Restart

end InteractingSLE

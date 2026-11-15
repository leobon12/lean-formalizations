/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.OneForceLaw

/-!
# No force point: Theorem 2.2 for the plain driving function `W = √a B`

Packet PROVE-SEC2-ONE (companion of the one-force-point case). With no force points the
integrated equation of Definition 2.1 reads `W_t = √a B_t`, the continuation-threshold condition
never holds (both sums are empty), and the lifetime is infinite (Specification p. 24, proof of
Aux. lemma 3: "The case with no force points is immediate from the Brownian driving equation").

* `isIntegratedSLEEvolution_none`: `W = √a B`, `ζ = ∞` is an evolution, for every filtered
  Brownian motion `B`;
* `ae_eq_none`: every evolution with no force points has `ζ = ∞` and `W = √a B` almost surely;
* `exists_isIntegratedSLEEvolution_none`, `measure_killedState_eq_none`: the frozen statements of
  Theorem 2.2 with `nL = nR = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace OneForce

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {a : ℝ}

/-- With no force points the continuation-threshold condition never holds. -/
theorem not_thresholdCondition_none {ρL ρR : Fin 0 → ℝ} {w : ℝ} {vL vR : Fin 0 → ℝ} :
    ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  unfold ForceWord.ThresholdCondition
  simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
  norm_num

/-- **No force point, the path**: `w = √a b` with infinite lifetime is an integrated path of
Definition 2.1, for every continuous `b` with `b 0 = 0`. -/
theorem isIntegratedSLEPath_none {xL xR ρL ρR : Fin 0 → ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    (hb0 : b 0 = 0) (vL vR : Fin 0 → ℝ≥0 → ℝ) :
    IsIntegratedSLEPath a xL xR ρL ρR (fun t => Real.sqrt a * b t) vL vR b ⊤ := by
  refine ⟨by simp [hb0], fun i => i.elim0, fun i => i.elim0,
    (continuous_const.mul hb).continuousOn, fun i => i.elim0, fun i => i.elim0,
    fun t _ => Subsingleton.antitone _, fun t _ i => i.elim0, fun t _ i => i.elim0,
    fun t _ => Subsingleton.monotone _, fun t _ i => i.elim0, fun t _ i => i.elim0,
    fun t _ => by simp, fun t _ i => i.elim0, fun t _ i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, fun t _ => not_thresholdCondition_none, fun h => absurd h ENNReal.top_ne_zero,
    fun T _ hT => absurd hT ENNReal.coe_ne_top⟩

/-- **Theorem 2.2, no force point, existence**: `W = √a B` with `ζ = ∞` is an integrated
evolution for every filtered Brownian motion `B`. -/
theorem isIntegratedSLEEvolution_none {xL xR ρL ρR : Fin 0 → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P) (VL VR : Fin 0 → ℝ≥0 → Ω → ℝ) :
    IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 (fun t ω => Real.sqrt a * B t ω) VL VR B
      (fun _ => ⊤) := by
  refine ⟨hB, fun t A hA => ?_, fun i => i.elim0, fun i => i.elim0, ?_⟩
  · have heq : {ω | (t : ℝ≥0∞) < ⊤ ∧ Real.sqrt a * B t ω ∈ A}
        = (fun ω => Real.sqrt a * B t ω) ⁻¹' A := by
      ext ω; simp
    rw [heq]
    exact ((hB.2.1 t).const_mul _) hA
  filter_upwards [hB.1.cont, hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hc h0
  exact isIntegratedSLEPath_none hc h0 (fun i t => VL i t ω) fun i t => VR i t ω

/-- **No force point, uniqueness**: almost surely an evolution with no force points has infinite
lifetime and `W = √a B`. -/
theorem ae_eq_none {xL xR ρL ρR : Fin 0 → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t, W t ω = Real.sqrt a * B t ω := by
  filter_upwards [h.2.2.2.2, h.1.1.cont] with ω hpath hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, -, -, -, -, -, hzero, hlim⟩ := hpath
  have hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω = Real.sqrt a * B t ω := fun t ht => by
    simpa using hweq t ht
  have hζ : ζ ω = ⊤ := by
    by_contra hne
    obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω := ⟨(ζ ω).toNNReal, ENNReal.coe_toNNReal hne⟩
    rcases (zero_le (a := T)).lt_or_eq with hT0 | hT0
    · have hW : Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 (Real.sqrt a * B T ω)) :=
        (((continuous_const.mul hc).tendsto T).mono_left nhdsWithin_le_nhds).congr'
          (eventually_nhdsWithin_of_forall fun t ht =>
            (hw t (by rw [← hT]; exact_mod_cast ht)).symm)
      have hL : Tendsto (fun t => fun i : Fin 0 => VL i t ω) (𝓝[<] T)
          (𝓝 (fun i : Fin 0 => i.elim0)) := tendsto_pi_nhds.2 fun i => i.elim0
      have hR : Tendsto (fun t => fun i : Fin 0 => VR i t ω) (𝓝[<] T)
          (𝓝 (fun i : Fin 0 => i.elim0)) := tendsto_pi_nhds.2 fun i => i.elim0
      exact not_thresholdCondition_none (hlim T hT0 hT _ _ _ (hW.prodMk_nhds (hL.prodMk_nhds hR)))
    · rw [← hT0] at hT
      exact not_thresholdCondition_none (hzero (by rw [← hT]; simp))
  exact ⟨hζ, fun t => hw t (by rw [hζ]; exact ENNReal.coe_lt_top)⟩

/-- **Theorem 2.2, existence, no force point** (the frozen statement with `nL = nR = 0`). -/
theorem exists_isIntegratedSLEEvolution_none (xL xR ρL ρR : Fin 0 → ℝ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, -, -⟩ := exists_filteredBrownian
  exact ⟨Ω, mΩ, P, hP, 𝓕, _, fun i => i.elim0, fun i => i.elim0, B, _,
    isIntegratedSLEEvolution_none hB (fun i => i.elim0) fun i => i.elim0⟩

section Law

open QuantumZipper.RS (CPath canonBM toCPath)

/-- The killed-state event with no force point on the canonical space `CPath`. -/
def noneStateSet (a : ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin 0 → ℝ) × (Fin 0 → ℝ) × ℝ)) : Set CPath :=
  {f | ∀ j, (Real.sqrt a * canonBM (ts j) f, (fun i : Fin 0 => i.elim0),
    (fun i : Fin 0 => i.elim0), canonBM (ts j) f) ∈ A j}

theorem measurableSet_noneStateSet (a : ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    {A : Fin n → Set (ℝ × (Fin 0 → ℝ) × (Fin 0 → ℝ) × ℝ)} (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (noneStateSet a ts A) := by
  have : noneStateSet a ts A = ⋂ j, (fun f => (Real.sqrt a * canonBM (ts j) f,
      (fun i : Fin 0 => i.elim0), (fun i : Fin 0 => i.elim0), canonBM (ts j) f)) ⁻¹' A j := by
    ext f; simp [noneStateSet]
  rw [this]
  have hm := QuantumZipper.RS.measurable_canonBM
  exact MeasurableSet.iInter fun j => (((hm (ts j)).const_mul _).prodMk
    (measurable_const.prodMk (measurable_const.prodMk (hm (ts j))))) (hA j)

/-- The killed-state probabilities with no force point are those of the law of a continuous
version `B'` of the Brownian motion on `CPath`, evaluated on `noneStateSet`. -/
theorem measure_killedState_none_eq_map {xL xR ρL ρR : Fin 0 → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB'm : ∀ t, Measurable (B' t)) (hB'c : ∀ ω, Continuous (B' · ω))
    (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin 0 → ℝ) × (Fin 0 → ℝ) × ℝ)) (hA : ∀ j, MeasurableSet (A j)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
      (P.map (toCPath B' hB'c)) (noneStateSet a ts A) := by
  rw [Measure.map_apply (QuantumZipper.RS.measurable_toCPath hB'm hB'c)
    (measurableSet_noneStateSet a ts hA)]
  refine measure_congr ?_
  filter_upwards [ae_eq_none h, hae] with ω ⟨hζ, hW⟩ hBeq
  refine propext (forall_congr' fun j => ?_)
  change _ ↔ (Real.sqrt a * B' (ts j) ω, (fun i : Fin 0 => i.elim0),
    (fun i : Fin 0 => i.elim0), B' (ts j) ω) ∈ A j
  have hVL : (fun i => VL i (ts j) ω) = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
  have hVR : (fun i => VR i (ts j) ω) = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
  rw [hζ, hW, hVL, hVR, hBeq]
  simp

/-- **Theorem 2.2, uniqueness in law, no force point** (the frozen statement with
`nL = nR = 0`). -/
theorem measure_killedState_eq_none {xL xR ρL ρR : Fin 0 → ℝ}
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 0 → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin 0 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 0 → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin 0 → ℝ) × (Fin 0 → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈
          A j} := by
  obtain ⟨B₁', hm₁, hc₁, -, hB₁', hae₁⟩ := QuantumZipper.RS.exists_good_version0 h₁.1.1
  obtain ⟨B₂', hm₂, hc₂, -, hB₂', hae₂⟩ := QuantumZipper.RS.exists_good_version0 h₂.1.1
  rw [measure_killedState_none_eq_map h₁ hm₁ hc₁ hae₁ ts A hA,
    measure_killedState_none_eq_map h₂ hm₂ hc₂ hae₂ ts A hA,
    QuantumZipper.RS.map_toCPath_eq hB₁'.toIsPreBrownianReal hB₂'.toIsPreBrownianReal hm₁ hm₂
      hc₁ hc₂]

end Law

end OneForce

end InteractingSLE

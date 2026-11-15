/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux122DisintMart
import InteractingSLE.Frozen.Spec.IsGeneratingTrace

/-!
# §7.4, Aux. lemma 122: disintegration of an evolution with an initially measurable random word

Packet PROVE-AUX119-130. Specification §7.4.1, Aux. lemma 122 (`source/spec/p385-432.md` L104–L139, pp. 389–391):
"Conditional on initial information fixing the word and its marked positions, the coordinates satisfy this SDE with
Brownian noise independent of that initial information … Disintegration over that initial information preserves the
integrated SDE and this Brownian property." Aux. lemma 125 (p. 395): "conditionally on `𝓔`, … this kernel has the
canonical integrated SLE driving marginal".

* `IsRandomWordEvolution a P 𝓔 F ΘL ΘR ρL ρR 𝓕 W VL VR B ζ`: the form in which Aux. lemma 122 delivers the relative
  driver: an initial σ-algebra `𝓔 ≤ 𝓕 0`, an `𝓔`-event `F`, an `𝓔`-measurable word `(ΘL, ΘR)`, a Brownian motion in
  `𝓕`, coordinates adapted before `ζ`, and on `F`, almost surely, the integrated equations of the word `Θ ω`.
* **`IsRandomWordEvolution.exists_ae_condExpKernel`** (standard Borel `Ω`): there are a measurable null set `N` and
  modified processes, equal to the given ones off `N` on `F`, with one filtration `𝓖`, such that for `P`-almost every
  `ω₀ ∈ F` the modified processes form an integrated `SLE_a(Θ ω₀)` evolution (`IsIntegratedSLEEvolution`, the frozen
  definition, with the deterministic word `Θ ω₀`) under the conditional law `condExpKernel P 𝓔 ω₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux122Disint

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **An integrated evolution with an initially measurable random word** (the conclusion form of Aux. lemma 122):
`𝓔 ≤ 𝓕 0`, `F ∈ 𝓔`, `ΘL`, `ΘR` are `𝓔`-measurable, `B` is a Brownian motion in `𝓕`, the coordinates are adapted
before `ζ`, and almost surely on `F` the pathwise conditions of the word `(ΘL ω, ΘR ω)` hold. -/
def IsRandomWordEvolution (a : ℝ) {nL nR : ℕ} (P : Measure Ω) (𝓔 : MeasurableSpace Ω) (F : Set Ω)
    (ΘL : Ω → Fin nL → ℝ) (ΘR : Ω → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  𝓔 ≤ 𝓕 0 ∧ MeasurableSet[𝓔] F ∧ Measurable[𝓔] ΘL ∧ Measurable[𝓔] ΘR ∧
    IsFilteredBrownianReal 𝓕 B P ∧ AdaptedBefore 𝓕 ζ W ∧ (∀ i, AdaptedBefore 𝓕 ζ (VL i)) ∧
      (∀ i, AdaptedBefore 𝓕 ζ (VR i)) ∧
        ∀ᵐ ω ∂P, ω ∈ F → IsIntegratedSLEPath a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)

/-- A process adapted before `ζ` has `𝓕_t`-measurable killed values. -/
theorem measurable_killAt_of_adaptedBefore {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ}
    (hY : AdaptedBefore 𝓕 ζ Y) (t : ℝ≥0) : Measurable[𝓕 t] (killAt ζ Y t) := by
  intro S hS
  have e : killAt ζ Y t ⁻¹' S =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ Y t ω ∈ S} ∪ ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ S}) := by
    ext ω
    simp only [killAt, mem_preimage, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [h]
  have hlt : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    have := hY t univ MeasurableSet.univ
    simpa using this
  rw [e]
  refine (hY t S hS).union (hlt.compl.inter ?_)
  by_cases h0 : (0 : ℝ) ∈ S
  · simp only [h0, ofPred_true]
    exact MeasurableSet.univ
  · simp only [h0, ofPred_false]
    exact MeasurableSpace.measurableSet_empty (𝓕 t)

open scoped Classical in
/-- `Y` on `F`, `0` off `F`. -/
def onF (F : Set Ω) (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ F then Y t ω else 0

/-- The data family of the driving coordinates: `W`, `VL i`, `VR j` on `F`, and `0` off `F`. -/
def wordData {nL nR : ℕ} (F : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) :
    Option (Fin nL ⊕ Fin nR) → ℝ≥0 → Ω → ℝ
  | none => onF F W
  | some (Sum.inl i) => onF F (VL i)
  | some (Sum.inr j) => onF F (VR j)

open scoped Classical in
theorem measurable_killAt_onF {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {F : Set Ω} {Y : ℝ≥0 → Ω → ℝ}
    (hY : AdaptedBefore 𝓕 ζ Y) {t : ℝ≥0} (hF : MeasurableSet[𝓕 t] F) : Measurable[𝓕 t] (killAt ζ (onF F Y) t) := by
  have e : killAt ζ (onF F Y) t = fun ω => if ω ∈ F then killAt ζ Y t ω else 0 := by
    funext ω
    by_cases h1 : ω ∈ F <;> by_cases h2 : (t : ℝ≥0∞) < ζ ω <;> simp [killAt, onF, h1, h2]
  rw [e]
  exact Measurable.ite hF (measurable_killAt_of_adaptedBefore hY t) measurable_const

omit mΩ in
theorem onF_of_mem {F : Set Ω} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ω ∈ F) (t : ℝ≥0) : onF F Y t ω = Y t ω := by
  simp [onF, h]

omit mΩ in
theorem onF_of_notMem {F : Set Ω} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ω ∉ F) (t : ℝ≥0) : onF F Y t ω = 0 := by
  simp [onF, h]

section Main

variable [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {a : ℝ}
  {nL nR : ℕ} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Disintegration over the initial information** (Aux. lemma 122, p. 391; Aux. lemma 125, p. 395). For an
evolution with an initially measurable random word on a standard Borel space, there are a measurable null set `N`,
one filtration `𝓖` and processes that agree with `W` off `N` on `F` (and with `VL`, `VR`, `B` likewise) such that for
`P`-almost every `ω₀ ∈ F` they form an integrated `SLE_a(ΘL ω₀; ΘR ω₀)` evolution under the conditional law
`condExpKernel P 𝓔 ω₀`. -/
theorem IsRandomWordEvolution.exists_ae_condExpKernel
    (h : IsRandomWordEvolution a P 𝓔 F ΘL ΘR ρL ρR 𝓕 W VL VR B ζ) :
    ∃ (N : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      MeasurableSet N ∧ P N = 0 ∧ (∀ ω, ω ∉ N → ω ∈ F → ∀ t, W' t ω = W t ω) ∧
      ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
        IsIntegratedSLEEvolution a (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝓔 ω₀) 𝓖 W' VL' VR' B' ζ := by
  obtain ⟨h0, hF, hΘL, hΘR, hB, hW, hVL, hVR, hpath⟩ := h
  have hgood : ∀ᵐ ω ∂P, (Continuous (fun t => B t ω) ∧ B 0 ω = 0) ∧
      (ω ∈ F → IsIntegratedSLEPath a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) :=
    (hB.1.cont.and hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero).and hpath
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hoff : ∀ ω, ω ∉ N → (Continuous (fun t => B t ω) ∧ B 0 ω = 0) ∧
      (ω ∈ F → IsIntegratedSLEPath a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  set X := wordData F W VL VR with hX
  have hF𝓕 : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] F := fun t => 𝓕.mono (by positivity) _ (h0 _ hF)
  have hlt : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := fun t => by
    have := hW t univ MeasurableSet.univ
    simpa using this
  have hkill : ∀ i t, Measurable[𝓕 t] (killAt ζ (X i) t) := by
    rintro (_ | i | j) t
    · exact measurable_killAt_onF hW (hF𝓕 t)
    · exact measurable_killAt_onF (hVL i) (hF𝓕 t)
    · exact measurable_killAt_onF (hVR j) (hF𝓕 t)
  have hS : DisintSetting P 𝓔 𝓕 B N ζ X :=
    ⟨h0, hB, hNm, hN0, fun ω hω => (hoff ω hω).1.1, fun ω hω => (hoff ω hω).1.2, hlt, hkill⟩
  have hXc : ∀ ω, ω ∉ N → ∀ i, ContinuousOn (fun t => X i t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    intro ω hω i
    by_cases hωF : ω ∈ F
    · have hp := (hoff ω hω).2 hωF
      rcases i with _ | i | j
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.2.2.2.1
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.2.2.2.2.1 i
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.2.2.2.2.2.1 j
    · rcases i with _ | i | j <;> simp only [hX, wordData, onF_of_notMem hωF] <;> exact continuousOn_const
  have hle : 𝓔 ≤ mΩ := hS.le_mΩ
  refine ⟨N, dataFilt N ζ B X, zeroOn N (X none), fun i => zeroOn N (X (some (Sum.inl i))),
    fun j => zeroOn N (X (some (Sum.inr j))), zeroOn N B, hNm, hN0, ?_, ?_⟩
  · intro ω hω hωF t
    simp only [zeroOn_of_notMem hω, hX, wordData, onF_of_mem hωF]
  filter_upwards [hS.ae_isFilteredBrownianReal, hS.ae_condExpKernel_N, ae_ae_condExpKernel_mem hle hF,
    ae_ae_condExpKernel_eq hle hΘL, ae_ae_condExpKernel_eq hle hΘR] with ω₀ hBr hνN hmemF hL hR hω₀F
  refine ⟨hBr, hS.dataMeas.adaptedBefore_zeroOn hXc none,
    fun i => hS.dataMeas.adaptedBefore_zeroOn hXc (some (Sum.inl i)),
    fun j => hS.dataMeas.adaptedBefore_zeroOn hXc (some (Sum.inr j)), ?_⟩
  filter_upwards [hmemF hω₀F, hL, hR, measure_eq_zero_iff_ae_notMem.1 hνN] with ω hωF hωL hωR hωN
  have hp := (hoff ω hωN).2 hωF
  rw [hωL, hωR] at hp
  have e1 : (fun t => zeroOn N (X none) t ω) = fun t => W t ω := funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e2 : (fun i t => zeroOn N (X (some (Sum.inl i))) t ω) = fun i t => VL i t ω := funext fun i => funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e3 : (fun j t => zeroOn N (X (some (Sum.inr j))) t ω) = fun j t => VR j t ω := funext fun j => funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e4 : (fun t => zeroOn N B t ω) = fun t => B t ω := funext fun t => zeroOn_of_notMem hωN t
  rw [e1, e2, e3, e4]
  exact hp

end Main

end Aux122Disint

end Sec7

end InteractingSLE

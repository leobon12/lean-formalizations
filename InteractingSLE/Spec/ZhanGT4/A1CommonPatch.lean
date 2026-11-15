/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MargSpace
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# Zhan's A.1: null-set patching of a regular marginal

Packet PROVE-A1-COMMON. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L300–L425): the
seeded calculus is run pathwise, so its pathwise premises (continuity of the driving Brownian path, the
non-collisions of the force points, the exit before the lifetime) must hold at **every** sample, while the marginal
supplies them only almost surely.

A regular marginal (`A1Marg.IsRegMarginal`) is modified on a measurable null set: every sample outside a measurable
full-measure set `G` is replaced by one fixed good sample `x₀ ∈ G` (`patchSel`). In the usual augmentation of the
filtration (which contains the null sets, so `G ∈ 𝓕⁺₀`) this keeps:

* the Brownian property (`isFilteredBrownianReal_comp_patchSel`: a.e. equal finite-dimensional laws, adaptedness,
  independent increments);
* adaptedness before the lifetime and strong progressiveness (`adaptedBefore_comp_patchSel`,
  `isStronglyProgressive_comp_patchSel`);
* the pathwise relation at every sample (the patched paths are paths of the original marginal).

**`IsRegMarginal.exists_patch`**: for every pathwise property `Good` of the path tuple that holds almost surely, there
is a regular marginal in the usual augmentation, equal to the original one on a measurable full-measure set, whose
driving Brownian path is continuous and whose path tuple is `Good` at every sample.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Common

/-! ### The sample selector -/

section Select

variable {X : Type*}

open Classical in
/-- **The patching selector**: a sample of `G` is kept, every other sample is replaced by `x₀`. -/
def patchSel (G : Set X) (x₀ : X) (x : X) : X := if x ∈ G then x else x₀

theorem patchSel_of_mem {G : Set X} {x₀ x : X} (hx : x ∈ G) : patchSel G x₀ x = x := by
  classical
  simp only [patchSel, hx, ↓reduceIte]

theorem patchSel_of_notMem {G : Set X} {x₀ x : X} (hx : x ∉ G) : patchSel G x₀ x = x₀ := by
  classical
  simp only [patchSel, hx, ↓reduceIte]

/-- The selected sample lies in `G` when `x₀` does. -/
theorem patchSel_mem {G : Set X} {x₀ : X} (h₀ : x₀ ∈ G) (x : X) : patchSel G x₀ x ∈ G := by
  by_cases hx : x ∈ G
  · rw [patchSel_of_mem hx]; exact hx
  · rw [patchSel_of_notMem hx]; exact h₀

/-- **The selector is measurable** from any σ-algebra `m'` containing `G` and a smaller `m`, to `m`. -/
theorem measurable_patchSel {m m' : MeasurableSpace X} (hmm : m ≤ m') {G : Set X} (hG : MeasurableSet[m'] G)
    (x₀ : X) : Measurable[m', m] (patchSel G x₀) := by
  classical
  intro A hA
  have e : patchSel G x₀ ⁻¹' A = (G ∩ A) ∪ (Gᶜ ∩ {_x | x₀ ∈ A}) := by
    ext x
    by_cases hx : x ∈ G
    · simp [patchSel_of_mem hx, hx]
    · simp [patchSel_of_notMem hx, hx]
  rw [e]
  by_cases h₀ : x₀ ∈ A
  · simp only [h₀, ofPred_true, inter_univ]
    exact (hG.inter (hmm A hA)).union hG.compl
  · simp only [h₀, ofPred_false, inter_empty, union_empty]
    exact hG.inter (hmm A hA)

/-- The selector is the identity almost everywhere when `G` has full measure. -/
theorem ae_patchSel_eq {mX : MeasurableSpace X} {P : Measure X} {G : Set X} (hGc : P Gᶜ = 0) (x₀ : X) :
    ∀ᵐ x ∂P, patchSel G x₀ x = x := by
  have : ∀ᵐ x ∂P, x ∈ G := by rw [ae_iff]; exact hGc
  filter_upwards [this] with x hx
  exact patchSel_of_mem hx

end Select

/-! ### Patched processes -/

section Process

variable {X : Type*} {mX : MeasurableSpace X} {𝓕 𝓖 : Filtration ℝ≥0 mX}

/-- **A patched Brownian motion.** If `B` is a `𝓖`-Brownian motion and the selector `s` is `𝓖_t`-measurable at every
time and the identity almost everywhere, then `B ∘ s` is a `𝓖`-Brownian motion. -/
theorem isFilteredBrownianReal_comp_patchSel {P : Measure X} {B : ℝ≥0 → X → ℝ} (hB : IsFilteredBrownianReal 𝓖 B P)
    {s : X → X} (hs : ∀ t, Measurable[𝓖 t, 𝓖 t] s) (hae : ∀ᵐ x ∂P, s x = x) :
    IsFilteredBrownianReal 𝓖 (fun t x => B t (s x)) P := by
  have hBae : ∀ t, B t =ᵐ[P] fun x => B t (s x) := fun t => by
    filter_upwards [hae] with x hx
    rw [hx]
  refine ⟨⟨hB.1.toIsPreBrownianReal.congr hBae, ?_⟩, fun t => ?_, fun u t hut => ?_⟩
  · filter_upwards [hB.1.cont, hae] with x hx hsx
    rw [hsx]; exact hx
  · exact (hB.2.1 t).comp (hs t)
  · rw [Indep_iff]
    rintro _ A ⟨S, hS, rfl⟩ hA
    have he : (fun x => B t (s x) - B u (s x)) ⁻¹' S =ᵐ[P] (fun x => B t x - B u x) ⁻¹' S := by
      filter_upwards [hae] with x hx
      simp only [mem_preimage, hx]
    have hind := Indep_iff _ _ _ |>.1 (hB.2.2 u t hut) ((fun x => B t x - B u x) ⁻¹' S) A ⟨S, hS, rfl⟩ hA
    rw [measure_congr (he.inter (EventuallyEq.refl _ A)), measure_congr he]
    exact hind

/-- A process adapted before `ζ` stays adapted before `ζ ∘ s` after composing with a measurable selector. -/
theorem adaptedBefore_comp_patchSel {ζ : X → ℝ≥0∞} {U : ℝ≥0 → X → ℝ} (hU : AdaptedBefore 𝓕 ζ U) {s : X → X}
    (hs : ∀ t, Measurable[𝓖 t, 𝓕 t] s) : AdaptedBefore 𝓖 (fun x => ζ (s x)) (fun t x => U t (s x)) :=
  fun t A hA => hs t (hU t A hA)

/-- A strongly progressive process stays strongly progressive after composing with a measurable selector. -/
theorem isStronglyProgressive_comp_patchSel {U : ℝ≥0 → X → ℝ} (hU : IsStronglyProgressive 𝓕 U) {s : X → X}
    (hs : ∀ t, Measurable[𝓖 t, 𝓕 t] s) : IsStronglyProgressive 𝓖 fun t x => U t (s x) := fun i => by
  have hm : Measurable[Subtype.instMeasurableSpace.prod (𝓖 i), Subtype.instMeasurableSpace.prod (𝓕 i)]
      fun p : Set.Iic i × X => (p.1, s p.2) :=
    Measurable.prodMk measurable_fst ((hs i).comp measurable_snd)
  exact (hU i).comp_measurable hm

end Process

/-! ### Patching a regular marginal -/

section Marginal

variable {nL nR : ℕ} {X : Type*} {mX : MeasurableSpace X}

/-- **Null-set patching of a regular marginal.** For every pathwise property `Good` of the path tuple
`(W, V^L, V^R, B, ζ)` that holds almost surely, there are a measurable full-measure set `G` and a regular marginal on
the usual augmentation of the filtration that agrees with the original one on `G`, whose driving Brownian path is
continuous at every sample, and whose path tuple is `Good` at every sample. -/
theorem _root_.InteractingSLE.ZhanGT4.A1Marg.IsRegMarginal.exists_patch {a : ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {P : Measure X} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mX} {W : ℝ≥0 → X → ℝ} {VL : Fin nL → ℝ≥0 → X → ℝ} {VR : Fin nR → ℝ≥0 → X → ℝ}
    {B : ℝ≥0 → X → ℝ} {ζ : X → ℝ≥0∞} (h : A1Marg.IsRegMarginal a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (Good : (ℝ≥0 → ℝ) → (Fin nL → ℝ≥0 → ℝ) → (Fin nR → ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop)
    (hGood : ∀ᵐ x ∂P, Good (W · x) (fun i t => VL i t x) (fun i t => VR i t x) (B · x) (ζ x)) :
    ∃ (G : Set X) (W' : ℝ≥0 → X → ℝ) (VL' : Fin nL → ℝ≥0 → X → ℝ) (VR' : Fin nR → ℝ≥0 → X → ℝ)
      (B' : ℝ≥0 → X → ℝ) (ζ' : X → ℝ≥0∞),
      MeasurableSet G ∧ P Gᶜ = 0 ∧
      A1Marg.IsRegMarginal a xL xR ρL ρR P (usualAugmentation 𝓕 P) W' VL' VR' B' ζ' ∧
      (∀ x, Continuous (B' · x)) ∧
      (∀ x, Good (W' · x) (fun i t => VL' i t x) (fun i t => VR' i t x) (B' · x) (ζ' x)) ∧
      ∀ x ∈ G, (∀ t, W' t x = W t x) ∧ (∀ i t, VL' i t x = VL i t x) ∧ (∀ i t, VR' i t x = VR i t x) ∧
        (∀ t, B' t x = B t x) ∧ ζ' x = ζ x := by
  set 𝓖 := usualAugmentation 𝓕 P
  set bad : Set X := {x | ¬ (Good (W · x) (fun i t => VL i t x) (fun i t => VR i t x) (B · x) (ζ x) ∧
    Continuous (B · x))} with hbad
  have hbad0 : P bad = 0 := ae_iff.1 (hGood.and h.evol.1.1.cont)
  set G : Set X := (toMeasurable P bad)ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P bad).compl
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hbad0
  have hGgood : ∀ x ∈ G, Good (W · x) (fun i t => VL i t x) (fun i t => VR i t x) (B · x) (ζ x) ∧
      Continuous (B · x) := fun x hx => by
    by_contra hn
    exact hx (subset_toMeasurable P bad hn)
  have hGne : G.Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty] at he
    rw [he, compl_empty, measure_univ] at hGc
    exact one_ne_zero hGc
  obtain ⟨x₀, hx₀⟩ := hGne
  set s := patchSel G x₀
  have hG𝓖 : ∀ t, MeasurableSet[𝓖 t] G := fun t => by
    have := Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc t
    simpa using this.compl
  have hs : ∀ t, Measurable[𝓖 t, 𝓕 t] s := fun t =>
    measurable_patchSel (Ito.le_usualAugmentation 𝓕 P t) (hG𝓖 t) x₀
  have hs' : ∀ t, Measurable[𝓖 t, 𝓖 t] s := fun t => measurable_patchSel le_rfl (hG𝓖 t) x₀
  have hae := ae_patchSel_eq hGc x₀
  have hpath : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t (s x)) (fun i t => VL i t (s x))
      (fun i t => VR i t (s x)) (fun t => B t (s x)) (ζ (s x)) := fun x => h.path (s x)
  refine ⟨G, fun t x => W t (s x), fun i t x => VL i t (s x), fun i t x => VR i t (s x), fun t x => B t (s x),
    fun x => ζ (s x), hGm, hGc, ⟨⟨isFilteredBrownianReal_comp_patchSel
      (Ito.isFilteredBrownianReal_usualAugmentation h.evol.1) hs' hae,
      adaptedBefore_comp_patchSel h.evol.2.1 hs, fun i => adaptedBefore_comp_patchSel (h.evol.2.2.1 i) hs,
      fun i => adaptedBefore_comp_patchSel (h.evol.2.2.2.1 i) hs, Eventually.of_forall hpath⟩, hpath,
      isStronglyProgressive_comp_patchSel h.progW hs, fun i => isStronglyProgressive_comp_patchSel (h.progVL i) hs,
      fun i => isStronglyProgressive_comp_patchSel (h.progVR i) hs⟩,
    fun x => (hGgood _ (patchSel_mem hx₀ x)).2, fun x => (hGgood _ (patchSel_mem hx₀ x)).1, fun x hx => ?_⟩
  have e : s x = x := patchSel_of_mem hx
  refine ⟨fun t => ?_, fun i t => ?_, fun i t => ?_, fun t => ?_, ?_⟩ <;> simp only [e]

end Marginal

end InteractingSLE.ZhanGT4.A1Common

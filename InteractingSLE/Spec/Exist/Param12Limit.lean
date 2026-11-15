/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12Kernel

/-!
# Theorem 1.1's coupling law as a kernel in the word: uniqueness turns a Borel set of descriptions into a kernel

Packet PROVE-PARAM12B (ruling R44; `planning/handoffs/PROVE-PARAM12.md` §5). PROVE-PARAM12 reduced Theorem 1.2 with a
word-measurable determination map to `CouplingLawKernelStatement`: a Borel kernel `μ` from word data to (field, killed
driver code) such that, for every ordered word, some optional hull coupling has joint law `μ w`.

By Theorems 1.2–1.3 the joint law of the field and the killed driver code is the **same** for every coupling of a
word (`map_fieldCode_eq`). This file shows that uniqueness alone turns a *Borel set of descriptions* into a kernel, with
no measurable selection and no limit along approximating couplings:

* `measurableSet_lt_of_unique` (Souslin): let `C ⊆ Θ × Z` be a measurable subset of a product of standard Borel
  spaces and `f` measurable on `Θ × Z`. If every `θ ∈ Θ₀` has a description `z` with `(θ, z) ∈ C`, and all of them give
  the same value `f (θ, z) = g θ`, then `{θ ∈ Θ₀ | q < g θ}` is measurable. It and its complement in `Θ₀` are
  projections of measurable sets, hence analytic, and disjoint analytic sets are separated by a measurable set (Lusin).
* `exists_kernel_of_unique`: the same for a kernel `L` on `Θ × Z`; the common values form a kernel on `Θ₀`.
* **`BorelCouplingDescriptionStatement`** (named input): for `κ > 0` and numbers of marks, a standard Borel space `Z`
  of descriptions, a measurable set `C ⊆ WordData × Z` and a kernel `L` such that every ordered word has a description,
  and every description `z` of an ordered word `w` is realized by an optional hull coupling of `w` whose joint law of
  field and killed driver code is `L (w, z)`. Many descriptions per word are allowed; nothing is chosen measurably.
* **`couplingLawKernelStatement_of_borelDescription`**: Theorems 1.2–1.3 and the named input give
  `CouplingLawKernelStatement`; `borelDescription_of_couplingLawKernel` is the converse (`Z = Unit`), so the named input
  is equivalent to the target given Theorems 1.2–1.3.

The intended description space is the standard Borel space of probability laws of canonical couplings (field, driver
code, Brownian path): a law is a description of `w` when it satisfies countably many Borel conditions that make the
canonical process an optional hull coupling of `w`. Then Theorem 2.2 needs no Yamada–Watanabe argument and Theorem 1.1
no measurable finite-family construction; see the handoff `PROVE-PARAM12B.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly LQGMetric Staged

/-! ### Souslin's theorem for a value that is the same on every description -/

section Souslin

variable {Θ Z X : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ] [MeasurableSpace Z] [StandardBorelSpace Z]
  [MeasurableSpace X]

/-- **Souslin.** Let `C ⊆ Θ × Z` be measurable (standard Borel spaces) and `f` measurable on `Θ × Z`. If every
`θ ∈ Θ₀` has a description `(θ, z) ∈ C` and every description gives the value `g θ`, then `{θ ∈ Θ₀ | q < g θ}` is
measurable: it and its complement in `Θ₀` are disjoint projections of measurable sets, and Lusin's separation theorem
applies. -/
theorem measurableSet_lt_of_unique {C : Set (Θ × Z)} (hC : MeasurableSet C) {Θ₀ : Set Θ} (hΘ₀ : MeasurableSet Θ₀)
    {f : Θ × Z → ℝ≥0∞} (hf : Measurable f) {g : Θ → ℝ≥0∞} (hne : ∀ θ ∈ Θ₀, ∃ z, (θ, z) ∈ C)
    (hval : ∀ θ ∈ Θ₀, ∀ z, (θ, z) ∈ C → f (θ, z) = g θ) (q : ℝ≥0∞) :
    MeasurableSet {θ | θ ∈ Θ₀ ∧ q < g θ} := by
  let := upgradeStandardBorel Θ
  have hD : MeasurableSet (C ∩ Prod.fst ⁻¹' Θ₀) := hC.inter (measurable_fst hΘ₀)
  have h1 : AnalyticSet (Prod.fst '' (C ∩ Prod.fst ⁻¹' Θ₀ ∩ {p | q < f p})) :=
    (hD.inter (measurableSet_lt measurable_const hf)).analyticSet_image measurable_fst
  have h2 : AnalyticSet (Prod.fst '' (C ∩ Prod.fst ⁻¹' Θ₀ ∩ {p | f p ≤ q})) :=
    (hD.inter (measurableSet_le hf measurable_const)).analyticSet_image measurable_fst
  have e1 : Prod.fst '' (C ∩ Prod.fst ⁻¹' Θ₀ ∩ {p | q < f p}) = {θ | θ ∈ Θ₀ ∧ q < g θ} := by
    ext θ
    simp only [mem_image, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨θ', z⟩, ⟨⟨hz, hθ⟩, hq⟩, rfl⟩
      exact ⟨hθ, (hval θ' hθ z hz) ▸ hq⟩
    · rintro ⟨hθ, hq⟩
      obtain ⟨z, hz⟩ := hne θ hθ
      exact ⟨(θ, z), ⟨⟨hz, hθ⟩, (hval θ hθ z hz).symm ▸ hq⟩, rfl⟩
  have e2 : Prod.fst '' (C ∩ Prod.fst ⁻¹' Θ₀ ∩ {p | f p ≤ q}) = {θ | θ ∈ Θ₀ ∧ g θ ≤ q} := by
    ext θ
    simp only [mem_image, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨θ', z⟩, ⟨⟨hz, hθ⟩, hq⟩, rfl⟩
      exact ⟨hθ, (hval θ' hθ z hz) ▸ hq⟩
    · rintro ⟨hθ, hq⟩
      obtain ⟨z, hz⟩ := hne θ hθ
      exact ⟨(θ, z), ⟨⟨hz, hθ⟩, (hval θ hθ z hz).symm ▸ hq⟩, rfl⟩
  rw [e1] at h1
  rw [e2] at h2
  have hdis : Disjoint {θ | θ ∈ Θ₀ ∧ q < g θ} {θ | θ ∈ Θ₀ ∧ g θ ≤ q} :=
    Set.disjoint_left.2 fun θ h h' => absurd h'.2 (not_le.2 h.2)
  obtain ⟨M, hM1, hM2, hMm⟩ := h1.measurablySeparable h2 hdis
  have e : {θ | θ ∈ Θ₀ ∧ q < g θ} = Θ₀ ∩ M := by
    ext θ
    refine ⟨fun h => ⟨h.1, hM1 h⟩, fun h => ⟨h.1, ?_⟩⟩
    by_contra hq
    exact Set.disjoint_left.1 hM2 ⟨h.1, not_lt.1 hq⟩ h.2
  rw [e]
  exact hΘ₀.inter hMm

/-- The common value of the descriptions is measurable on `Θ₀` (extended by `0`). -/
theorem measurable_indicator_of_unique {C : Set (Θ × Z)} (hC : MeasurableSet C) {Θ₀ : Set Θ}
    (hΘ₀ : MeasurableSet Θ₀) {f : Θ × Z → ℝ≥0∞} (hf : Measurable f) {g : Θ → ℝ≥0∞}
    (hne : ∀ θ ∈ Θ₀, ∃ z, (θ, z) ∈ C) (hval : ∀ θ ∈ Θ₀, ∀ z, (θ, z) ∈ C → f (θ, z) = g θ) :
    Measurable (Θ₀.indicator g) := by
  refine measurable_of_Ioi fun q => ?_
  have e : Θ₀.indicator g ⁻¹' Ioi q = {θ | θ ∈ Θ₀ ∧ q < g θ} := by
    ext θ
    simp only [mem_preimage, mem_Ioi, mem_ofPred_eq]
    by_cases hθ : θ ∈ Θ₀
    · simp only [indicator_of_mem hθ, hθ, true_and]
    · simp only [indicator_of_notMem hθ, hθ, false_and, iff_false, not_lt, zero_le]
  rw [e]
  exact measurableSet_lt_of_unique hC hΘ₀ hf hne hval q

/-- **A kernel from descriptions with a unique value.** If every `θ ∈ Θ₀` has a description in the measurable set `C`
and the kernel `L` takes the same value `m θ` at all of them, then some kernel equals `m` on `Θ₀` (and `0` off it). -/
theorem exists_kernel_of_unique {C : Set (Θ × Z)} (hC : MeasurableSet C) {Θ₀ : Set Θ} (hΘ₀ : MeasurableSet Θ₀)
    (L : Kernel (Θ × Z) X) (m : Θ → Measure X) (hne : ∀ θ ∈ Θ₀, ∃ z, (θ, z) ∈ C)
    (hval : ∀ θ ∈ Θ₀, ∀ z, (θ, z) ∈ C → L (θ, z) = m θ) :
    ∃ μ : Kernel Θ X, (∀ θ ∈ Θ₀, μ θ = m θ) ∧ ∀ θ ∉ Θ₀, μ θ = 0 := by
  classical
  have hmeas : Measurable fun θ => if θ ∈ Θ₀ then m θ else 0 := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have e : (fun θ => (if θ ∈ Θ₀ then m θ else 0 : Measure X) s) = Θ₀.indicator fun θ => m θ s := by
      funext θ
      by_cases hθ : θ ∈ Θ₀
      · simp only [hθ, ↓reduceIte, indicator_of_mem hθ]
      · simp only [hθ, ↓reduceIte, indicator_of_notMem hθ, Measure.coe_zero, Pi.zero_apply]
    rw [e]
    exact measurable_indicator_of_unique hC hΘ₀ (L.measurable_coe hs) hne
      fun θ hθ z hz => by rw [hval θ hθ z hz]
  refine ⟨⟨fun θ => if θ ∈ Θ₀ then m θ else 0, hmeas⟩, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · show (if θ ∈ Θ₀ then m θ else 0) = m θ
    simp only [hθ, ↓reduceIte]
  · show (if θ ∈ Θ₀ then m θ else 0) = 0
    simp only [hθ, ↓reduceIte]

end Souslin

/-! ### The ordered words form a measurable set -/

theorem measurableSet_isOrderedForceWord (nL nR : ℕ) :
    MeasurableSet {w : WordData nL nR | IsOrderedForceWord w.1.1 w.1.2} := by
  have hL : ∀ i : Fin nL, Measurable fun w : WordData nL nR => w.1.1 i := fun i =>
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  have hR : ∀ j : Fin nR, Measurable fun w : WordData nL nR => w.1.2 j := fun j =>
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)
  have hle : ∀ {f g : WordData nL nR → ℝ}, Measurable f → Measurable g → Measurable fun w => f w ≤ g w :=
    fun hf hg => measurableSet_setOfPred.1 (measurableSet_le hf hg)
  refine measurableSet_setOfPred.2 ?_
  unfold IsOrderedForceWord Antitone Monotone
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_))
  · exact Measurable.forall fun i => Measurable.forall fun j => measurable_const_imp _ (hle (hL j) (hL i))
  · exact Measurable.forall fun i => hle (hL i) measurable_const
  · exact Measurable.forall fun i => Measurable.forall fun j => measurable_const_imp _ (hle (hR i) (hR j))
  · exact Measurable.forall fun i => hle measurable_const (hR i)

/-! ### Couplings described by a Borel set -/

/-- **Named input: Borel descriptions of Theorem 1.1's couplings.** For `κ > 0` and numbers of marks: a standard
Borel space `Z` of descriptions, a measurable set `C` of (word, description) pairs and a kernel `L`, such that every
ordered word `w` has a description, and every description `z` of `w` is realized by an optional hull coupling of `w`
(at universe `u`) whose joint law of field and killed driver code is `L (w, z)`. -/
def BorelCouplingDescriptionStatement : Prop :=
  ∀ (κ : ℝ) (_ : 0 < κ) (nL nR : ℕ),
    ∃ (Z : Type) (_ : MeasurableSpace Z) (_ : StandardBorelSpace Z) (C : Set (WordData nL nR × Z))
      (L : Kernel (WordData nL nR × Z) (DistOn upperHalfPlaneOpens × DCode)), MeasurableSet C ∧
      ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
        (∃ z, ((((xL, xR), (ρL, ρR)) : WordData nL nR), z) ∈ C) ∧
          ∀ z, ((((xL, xR), (ρL, ρR)) : WordData nL nR), z) ∈ C →
            ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
              (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
              (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
              (h : Ω → DistOn upperHalfPlaneOpens),
              IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧
                P.map (fieldCode h W ζ) = L ((((xL, xR), (ρL, ρR)) : WordData nL nR), z)

/-- **Theorem 1.1's coupling law is a Borel kernel in the word**, from Theorems 1.2–1.3 and Borel descriptions of the
couplings. All descriptions of an ordered word give the same law (`map_fieldCode_eq`), so `exists_kernel_of_unique`
applies with `Θ₀` the ordered words. -/
theorem couplingLawKernelStatement_of_borelDescription (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (hD : BorelCouplingDescriptionStatement.{u}) :
    CouplingLawKernelStatement.{u} := by
  classical
  intro κ hκ nL nR
  obtain ⟨Z, mZ, hZ, C, L, hC, hdesc⟩ := hD κ hκ nL nR
  set Θ₀ : Set (WordData nL nR) := {w | IsOrderedForceWord w.1.1 w.1.2} with hΘ₀def
  have hΘ₀ : MeasurableSet Θ₀ := measurableSet_isOrderedForceWord nL nR
  have hne : ∀ w ∈ Θ₀, ∃ z, (w, z) ∈ C := fun w hw => (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw).1
  let m : WordData nL nR → Measure (DistOn upperHalfPlaneOpens × DCode) := fun w =>
    if hw : w ∈ Θ₀ then L (w, (hne w hw).choose) else 0
  have hval : ∀ w ∈ Θ₀, ∀ z, (w, z) ∈ C → L (w, z) = m w := by
    intro w hw z hz
    obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁, hC₁, hl₁⟩ :=
      (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw).2 z hz
    obtain ⟨Ω₂, m₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂, hC₂, hl₂⟩ :=
      (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw).2 _ (hne w hw).choose_spec
    simp only [m, hw, ↓reduceDIte]
    rw [← hl₁, ← hl₂]
    exact map_fieldCode_eq h12 h13 hκ hw hC₁ hC₂
  obtain ⟨μ, hμ, hμ0⟩ := exists_kernel_of_unique hC hΘ₀ L m hne hval
  have hprob : ∀ w ∈ Θ₀, IsProbabilityMeasure (μ w) := by
    intro w hw
    obtain ⟨Ω₂, m₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂, -, hl₂⟩ :=
      (hdesc w.1.1 w.1.2 w.2.1 w.2.2 hw).2 _ (hne w hw).choose_spec
    rw [hμ w hw]
    simp only [m, hw, ↓reduceDIte]
    rw [← hl₂]
    infer_instance
  refine ⟨μ, ⟨⟨1, ENNReal.one_lt_top, fun w => ?_⟩⟩, fun xL xR ρL ρR hF => ?_⟩
  · by_cases hw : w ∈ Θ₀
    · have := hprob w hw
      exact prob_le_one
    · rw [hμ0 w hw]
      exact zero_le
  · have hw : (((xL, xR), (ρL, ρR)) : WordData nL nR) ∈ Θ₀ := hF
    obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hCp, hl⟩ :=
      (hdesc xL xR ρL ρR hF).2 _ (hne _ hw).choose_spec
    refine ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hCp, ?_⟩
    rw [hl, hμ _ hw]
    simp only [m, hw, ↓reduceDIte]

/-- The converse: a kernel is a Borel description with one description per word (`Z = Unit`). -/
theorem borelDescription_of_couplingLawKernel (hK : CouplingLawKernelStatement.{u}) :
    BorelCouplingDescriptionStatement.{u} := by
  intro κ hκ nL nR
  obtain ⟨μ, -, hμ⟩ := hK κ hκ nL nR
  refine ⟨Unit, inferInstance, inferInstance, univ, μ.comap Prod.fst measurable_fst, MeasurableSet.univ,
    fun xL xR ρL ρR hF => ⟨⟨(), mem_univ _⟩, fun z _ => ?_⟩⟩
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, hl⟩ := hμ xL xR ρL ρR hF
  exact ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, by rw [hl]; rfl⟩

/-- Given Theorems 1.2–1.3, Borel descriptions of the couplings are equivalent to the coupling law being a kernel. -/
theorem couplingLawKernelStatement_iff_borelDescription (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) :
    CouplingLawKernelStatement.{u} ↔ BorelCouplingDescriptionStatement.{u} :=
  ⟨borelDescription_of_couplingLawKernel, couplingLawKernelStatement_of_borelDescription h12 h13⟩

end Param12

end Exist

end InteractingSLE

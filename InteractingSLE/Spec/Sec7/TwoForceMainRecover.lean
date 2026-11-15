/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TwoForceMainDetermine
import InteractingSLE.Spec.Sobolev.ThinRange

/-!
# Lemma 7.2: recovering the field off a thin set, and the curve from the pocket field

Packet PROVE-SEC7-A2 (specification §7.1, Lemma 7.2 and its proof, pp. 226–227).

The proof of Lemma 7.2 has two measure-theoretic steps.

1. **Recovery** (`exists_version_of_recorded_off`, `isAEDeterminedBy_comp_of_recorded_off`): "let
   `N = E[h | Q, h_ψ]` as a locally `H^{-ε}` distribution. On every rational ball disjoint from `∂C`,
   countable test coordinates of `h` are already recorded, so `N = h` there. Their difference is
   supported on `∂C`, and Aux. lemma 12 makes it zero. Thus the entire field `h = N` is measurable from the
   recorded pair." Abstractly: a random distribution `h` on `U` with (SR1) whose pairings with tests
   supported off a random thin relatively closed set `A` (dimension `< 2 − 2ε` on compacts) are recorded
   by a `σ`-algebra `𝓡` has an `𝓡`-measurable version. The conditional mean is Aux. lemma 11
   (`Sobolev.exists_condMean_version`) and the support removal is Aux. lemma 12
   (`Sobolev.ae_eq_of_ae_eq_off`).
2. **(CPF3)** (`IsAEDeterminedBy.of_indepFun`, `TwoForceMainDetermine.lean`): a curve determined by
   `(Q, h_ψ)` and such that `(η_ψ, h_ψ)` is independent of `Q` is determined by `h_ψ`.

`lem72_isAEDeterminedBy` combines them: if the field is recorded off a thin set by `(Q, Z)`, the curve
`Y` is a Borel function `Φ` of the field (the non-boundary field-determination theorem, an input), and
`(Y, Z)` is independent of `Q` (Lemma 7.1's component-pair factorization, an input), then `Y` is almost
surely a Borel function of `Z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace InteractingSLE

namespace Sec7

open LQGMetric TopologicalSpace Sobolev

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {U : Opens ℂ}

/-- On a recorded event `S` where `h φ` equals a recorded variable `g`, the conditional expectation of
`h φ` given the record equals `g`. -/
theorem condExp_eq_on_of_eq {𝓡 : MeasurableSpace Ω} (h𝓡 : 𝓡 ≤ mΩ) {f g : Ω → ℝ}
    (hf : Integrable f P) {S : Set Ω} (hS : MeasurableSet[𝓡] S) (hg : StronglyMeasurable[𝓡] g)
    (hfg : ∀ᵐ o ∂P, o ∈ S → f o = g o) : ∀ᵐ o ∂P, o ∈ S → P[f | 𝓡] o = g o := by
  have h1 : S.indicator f =ᵐ[P] S.indicator g := by
    filter_upwards [hfg] with o ho
    by_cases hoS : o ∈ S
    · rw [indicator_of_mem hoS, indicator_of_mem hoS, ho hoS]
    · rw [indicator_of_notMem hoS, indicator_of_notMem hoS]
  have hgi : Integrable (S.indicator g) P := (hf.indicator (h𝓡 _ hS)).congr h1
  have h2 : P[S.indicator g | 𝓡] = S.indicator g :=
    condExp_of_stronglyMeasurable h𝓡 (hg.indicator hS) hgi
  have h3 : P[S.indicator f | 𝓡] =ᵐ[P] S.indicator (P[f | 𝓡]) := condExp_indicator hf hS
  filter_upwards [h3, condExp_congr_ae (m := 𝓡) h1] with o e3 e1 hoS
  have := e3.symm.trans e1
  rw [h2, indicator_of_mem hoS, indicator_of_mem hoS] at this
  exact this

/-- **Recovery of a field off a thin set** (proof of Lemma 7.2, first paragraph, pp. 226–227). Let `h`
be a measurable random distribution on `U` with integrable pairings and (SR1). Let `A` be a random
relatively closed subset of `U` with `dim_H (A ∩ K) < 2 − 2ε` on compacts. Suppose that a sub-`σ`-algebra
`𝓡` records the pairings of `h` with tests supported off `A`: for every test `φ` there are an
`𝓡`-measurable event `S`, containing `{supp φ ∩ A = ∅}` almost surely, and an `𝓡`-measurable `g` with
`h φ = g` on `S`. Then `h` has an `𝓡`-measurable version. -/
theorem exists_version_of_recorded_off {h : Ω → DistOn U} (hh : Measurable h)
    (hint : ∀ φ : TestOn U, Integrable (fun o => h o φ) P) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hSR1 : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h o) ζ ∂P < ⊤)
    {A : Ω → Set ℂ} (hAcl : ∀ᵐ o ∂P, closure (A o) ∩ U ⊆ A o)
    (hdim : ∀ᵐ o ∂P, ∀ K, IsCompact K → K ⊆ U → dimH (A o ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {𝓡 : MeasurableSpace Ω} (h𝓡 : 𝓡 ≤ mΩ)
    (hrec : ∀ φ : TestOn U, ∃ (S : Set Ω) (g : Ω → ℝ), MeasurableSet[𝓡] S ∧
      StronglyMeasurable[𝓡] g ∧ (∀ᵐ o ∂P, Disjoint (tsupport φ) (A o) → o ∈ S) ∧
      ∀ᵐ o ∂P, o ∈ S → h o φ = g o) :
    ∃ N : Ω → DistOn U, Measurable[𝓡] N ∧ ∀ᵐ o ∂P, h o = N o := by
  classical
  have hcut : ∀ k, ∃ ζ : TestOn U, EqOn ζ 1 (exhaustK U k) := fun k => by
    obtain ⟨ζ, -, h1⟩ := exists_cutoff_testOn (exhaustK U k).isCompact (exhaustK_subset U k)
    exact ⟨ζ, h1⟩
  choose ζ hζ using hcut
  obtain ⟨N, hNm, hNv, hNr⟩ := exists_condMean_version hh h𝓡 hint hε0 hε1 hSR1
  -- `h` itself is locally `H^{-ε}` almost surely
  have hhr : ∀ᵐ o ∂P, ∀ k, negSobolevSq ε (h o) (ζ k) < ⊤ := by
    refine ae_all_iff.2 fun k => ?_
    have hm : @Measurable Ω ℝ≥0∞ mΩ _ (fun o => negSobolevSq ε (h o) (ζ k)) :=
      (measurable_negSobolevSq ε (ζ k)).comp hh
    exact ae_lt_top' (@Measurable.aemeasurable Ω ℝ≥0∞ mΩ _ _ P hm) (hSR1 (ζ k)).ne
  let _ : MeasurableSpace Ω := mΩ
  refine ⟨N, hNm, ae_eq_of_ae_eq_off hε0 hε1 hζ hhr (ae_all_iff.2 fun k => hNr (ζ k)) hAcl hdim
    fun φ => ?_⟩
  obtain ⟨S, g, hS, hg, hAS, hSg⟩ := hrec φ
  have h1 := condExp_eq_on_of_eq h𝓡 (hint φ) hS hg hSg
  filter_upwards [hAS, hSg, h1, hNv φ] with o e1 e2 e3 e4 hd
  rw [e4, e3 (e1 hd), e2 (e1 hd)]

/-- **Recovery, determined form.** Under the hypotheses of `exists_version_of_recorded_off` with the
record `𝓡 = σ(R)`, every standard Borel measurable function `Φ(h)` of the field is almost surely a
Borel function of `R`. -/
theorem isAEDeterminedBy_comp_of_recorded_off {γ β : Type*} [mγ : MeasurableSpace γ]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] {R : Ω → γ} (hR : Measurable R)
    {h : Ω → DistOn U} (hh : Measurable h)
    (hint : ∀ φ : TestOn U, Integrable (fun o => h o φ) P) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hSR1 : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h o) ζ ∂P < ⊤)
    {A : Ω → Set ℂ} (hAcl : ∀ᵐ o ∂P, closure (A o) ∩ U ⊆ A o)
    (hdim : ∀ᵐ o ∂P, ∀ K, IsCompact K → K ⊆ U → dimH (A o ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    (hrec : ∀ φ : TestOn U, ∃ (S : Set Ω) (g : Ω → ℝ), MeasurableSet[mγ.comap R] S ∧
      StronglyMeasurable[mγ.comap R] g ∧ (∀ᵐ o ∂P, Disjoint (tsupport φ) (A o) → o ∈ S) ∧
      ∀ᵐ o ∂P, o ∈ S → h o φ = g o)
    {Φ : DistOn U → β} (hΦ : Measurable Φ) : IsAEDeterminedBy P R fun o => Φ (h o) := by
  obtain ⟨N, hNm, hhN⟩ :=
    exists_version_of_recorded_off hh hint hε0 hε1 hSR1 hAcl hdim hR.comap_le hrec
  obtain ⟨g, hg, hgN⟩ := (hΦ.comp hNm).exists_eq_measurable_comp
  refine ⟨g, hg, ?_⟩
  filter_upwards [hhN] with o ho
  rw [ho]
  exact congrFun hgN o

/-- **Lemma 7.2, measure-theoretic form** (specification pp. 226–227). Let `h` be the field on `U`,
`Z` the pocket field `h_ψ`, `Q = (A, h')` the outer curves and the exterior field, and `Y` the curve
`η_ψ` (standard Borel). Assume
* the pair `(Q, Z)` records `h` off a thin random set (`∂C`, contained in the two outer simple curves)
  as in `exists_version_of_recorded_off`;
* `Y = Φ(h)` almost surely for a Borel `Φ` (the non-boundary field-determination theorem);
* `(Y, Z)` is independent of `Q` (the component-pair factorization of Lemma 7.1).
Then `Y` is almost surely a Borel function of `Z`: "`h_ψ` almost surely determines `η_ψ`". -/
theorem lem72_isAEDeterminedBy {γ δ β : Type*} [mγ : MeasurableSpace γ] [mδ : MeasurableSpace δ]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] {Q : Ω → δ} {Z : Ω → γ}
    (hQ : Measurable Q) (hZ : Measurable Z) {h : Ω → DistOn U} (hh : Measurable h)
    (hint : ∀ φ : TestOn U, Integrable (fun o => h o φ) P) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hSR1 : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h o) ζ ∂P < ⊤)
    {A : Ω → Set ℂ} (hAcl : ∀ᵐ o ∂P, closure (A o) ∩ U ⊆ A o)
    (hdim : ∀ᵐ o ∂P, ∀ K, IsCompact K → K ⊆ U → dimH (A o ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    (hrec : ∀ φ : TestOn U, ∃ (S : Set Ω) (g : Ω → ℝ),
      MeasurableSet[(mδ.prod mγ).comap fun o => (Q o, Z o)] S ∧
      StronglyMeasurable[(mδ.prod mγ).comap fun o => (Q o, Z o)] g ∧
      (∀ᵐ o ∂P, Disjoint (tsupport φ) (A o) → o ∈ S) ∧ ∀ᵐ o ∂P, o ∈ S → h o φ = g o)
    {Y : Ω → β} (hY : Measurable Y) {Φ : DistOn U → β} (hΦ : Measurable Φ)
    (hYΦ : Y =ᵐ[P] fun o => Φ (h o)) (hind : IndepFun (fun o => (Y o, Z o)) Q P) :
    IsAEDeterminedBy P Z Y := by
  have hdet : IsAEDeterminedBy P (fun o => (Q o, Z o)) Y :=
    (isAEDeterminedBy_comp_of_recorded_off (hQ.prodMk hZ) hh hint hε0 hε1 hSR1 hAcl hdim hrec
      hΦ).congr_ae hYΦ.symm
  exact hdet.of_indepFun hQ hZ hY hind

end Sec7

end InteractingSLE

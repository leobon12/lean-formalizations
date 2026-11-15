/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.Probability.ConditionalExpectation
import InteractingSLE.Spec.Sec7.TwoForceRestart
import InteractingSLE.Spec.Sec7.TwoForceFreeze

/-!
# Field determination in §7.1: the measure-theoretic steps

Packet PROVE-SEC7-A2 (specification §7.1, `source/spec/p193-240.md` L539–L912 and `p241-288.md` L1–L271,
pp. 221–252). The determination arguments of §7.1 share a few abstract steps, proved here for the
predicate `IsAEDeterminedBy μ H Y` ("`Y` is almost surely a Borel function of `H`", `TwoForceRestart.lean`).

* **Doob–Dynkin, almost-sure form** (`isAEDeterminedBy_of_ae_eq_condExp`,
  `IsAEDeterminedBy.ae_eq_condExp`): a real `Y` is determined by `H` iff `Y = E[Y | σ(H)]` a.s.
* **Removing a conditionally irrelevant coordinate** (`IsAEDeterminedBy.of_condExp_eq`,
  `IsAEDeterminedBy.of_condExp_indicator_eq`): if `Y` is determined by `(A, Z)` and, given `(Y, A)`, the
  conditional law of `Z` depends only on `A`, then `Y` is determined by `A`. This is the last step of
  the proof of Aux. lemma 55 (p. 250: "conditionally on the orthogonal complement … this history is
  independent of that zero-boundary field. Since it is also a function of the full field, its
  conditional law given the complement is a point mass").
* **(CPF3)**, the core of Lemma 7.2 (`IsAEDeterminedBy.of_indepFun`, p. 227): if `Y` is determined by
  `(Q, Z)` and the pair `(Y, Z)` is independent of `Q`, then `Y` is determined by `Z`
  ("`F(η_ψ) = E[F(η_ψ) | Q, h_ψ] = E[F(η_ψ) | h_ψ]`").
* **Transfer along equal joint laws** (`ae_eq_comp_of_map_eq`, `IsAEDeterminedBy.of_map_eq`): the last
  step of Aux. lemma 51 and of Proposition 7.3 (p. 241, p. 243: "If the reference law is concentrated on
  the graph of a measurable function of the field, the identical law in every original coupling is
  concentrated on that same graph"), and uniqueness of the determining function
  (`ae_eq_of_ae_eq_comp`; "the same determining function up to a set of zero GFF probability").
* **Equivalent measures** (`IsAEDeterminedBy.of_absolutelyContinuous`): Aux. lemma 55, p. 250.

Targets are standard Borel spaces (a bounded real code `c` with a measurable left inverse reduces the
statements to real bounded variables).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace InteractingSLE

namespace Sec7

section DoobDynkin

variable {Ω γ : Type*} {mΩ : MeasurableSpace Ω} [mγ : MeasurableSpace γ] {μ : Measure Ω}

/-- **Doob–Dynkin, almost-sure form.** A real random variable equal almost surely to its conditional
expectation given `σ(H)` is almost surely a Borel function of `H`. -/
theorem isAEDeterminedBy_of_ae_eq_condExp {H : Ω → γ} {Y : Ω → ℝ}
    (h : Y =ᵐ[μ] μ[Y | mγ.comap H]) : IsAEDeterminedBy μ H Y := by
  obtain ⟨g, hg, hgY⟩ :=
    (stronglyMeasurable_condExp (m := mγ.comap H) (f := Y) (μ := μ)).exists_eq_measurable_comp
  refine ⟨g, hg.measurable, h.trans (Eventually.of_forall fun ω => ?_)⟩
  rw [hgY]
  rfl

/-- Conversely, an integrable real variable determined by a measurable `H` is almost surely equal to
its conditional expectation given `σ(H)`. -/
theorem IsAEDeterminedBy.ae_eq_condExp [IsFiniteMeasure μ] {H : Ω → γ} (hH : Measurable H)
    {Y : Ω → ℝ} (hdet : IsAEDeterminedBy μ H Y) (hYi : Integrable Y μ) :
    Y =ᵐ[μ] μ[Y | mγ.comap H] := by
  obtain ⟨g, hg, hYg⟩ := hdet
  have hle : mγ.comap H ≤ mΩ := hH.comap_le
  have hgm : StronglyMeasurable[mγ.comap H] (fun ω => g (H ω)) :=
    (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have hint : Integrable (fun ω => g (H ω)) μ := hYi.congr hYg
  calc Y =ᵐ[μ] fun ω => g (H ω) := hYg
    _ = μ[fun ω => g (H ω) | mγ.comap H] := (condExp_of_stronglyMeasurable hle hgm hint).symm
    _ =ᵐ[μ] μ[Y | mγ.comap H] := condExp_congr_ae hYg.symm

end DoobDynkin

section Code

variable {β : Type*} [MeasurableSpace β]

/-- A standard Borel space has a bounded measurable real code with a measurable left inverse. -/
theorem exists_bounded_code [StandardBorelSpace β] [Nonempty β] :
    ∃ (c : β → ℝ) (d : ℝ → β), Measurable c ∧ Measurable d ∧ (∀ x, |c x| ≤ 2) ∧
      ∀ x, d (c x) = x := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real β
  obtain ⟨e', he', he'e⟩ := he.exists_measurable_extend (g := id) measurable_id
    (fun _ => inferInstance)
  refine ⟨fun x => Real.arctan (e x), fun r => e' (Real.sin r / Real.cos r),
    Real.measurable_arctan.comp he.measurable,
    he'.comp (Real.measurable_sin.div Real.measurable_cos), fun x => ?_, fun x => ?_⟩
  · have h1 := Real.arctan_lt_pi_div_two (e x)
    have h2 := Real.neg_pi_div_two_lt_arctan (e x)
    have h3 := Real.pi_le_four
    rw [abs_le]
    constructor <;> linarith
  · show e' (Real.sin (Real.arctan (e x)) / Real.cos (Real.arctan (e x))) = x
    rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
    exact congrFun he'e x

variable {Ω γ : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace γ] {μ : Measure Ω}

/-- Determination of `Y` is determination of any code `c ∘ Y` with a measurable left inverse. -/
theorem isAEDeterminedBy_iff_code {H : Ω → γ} {Y : Ω → β} {c : β → ℝ} {d : ℝ → β}
    (hc : Measurable c) (hd : Measurable d) (hdc : ∀ x, d (c x) = x) :
    IsAEDeterminedBy μ H Y ↔ IsAEDeterminedBy μ H fun ω => c (Y ω) := by
  refine ⟨fun h => h.comp hc, fun h => ?_⟩
  have := h.comp hd
  simp only [hdc] at this
  exact this

end Code

section Remove

variable {Ω γ δ β : Type*} {mΩ : MeasurableSpace Ω} [mγ : MeasurableSpace γ] [mδ : MeasurableSpace δ]
  [mβ : MeasurableSpace β] {μ : Measure Ω}

/-- **Removing a conditionally irrelevant coordinate, general form.** If `Y` (standard Borel) is
determined by `H`, and for every bounded measurable `f` the conditional expectations of `f(Y)` given
`σ(H)` and given `σ(H₀)` agree, then `Y` is determined by `H₀`. -/
theorem IsAEDeterminedBy.of_condExp_eq [IsFiniteMeasure μ] [StandardBorelSpace β] [Nonempty β]
    {H : Ω → γ} {H₀ : Ω → δ} (hH : Measurable H) {Y : Ω → β} (hY : Measurable Y)
    (hdet : IsAEDeterminedBy μ H Y)
    (hce : ∀ f : β → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      μ[fun ω => f (Y ω) | mγ.comap H] =ᵐ[μ] μ[fun ω => f (Y ω) | mδ.comap H₀]) :
    IsAEDeterminedBy μ H₀ Y := by
  obtain ⟨c, d, hc, hd, hcb, hdc⟩ := exists_bounded_code (β := β)
  rw [isAEDeterminedBy_iff_code hc hd hdc] at hdet ⊢
  refine isAEDeterminedBy_of_ae_eq_condExp ?_
  have hi : Integrable (fun ω => c (Y ω)) μ :=
    Integrable.of_bound (hc.comp hY).aestronglyMeasurable 2
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hcb (Y ω))
  exact (hdet.ae_eq_condExp hH hi).trans (hce c hc ⟨2, hcb⟩)

/-- **Removing a conditionally irrelevant coordinate** (last step of the proof of Aux. lemma 55,
specification p. 250). If `Y` (standard Borel) is determined by the pair `(A, Z)` and, conditionally
on `(Y, A)`, the law of `Z` only depends on `A` (`E[1_S(Z) | Y, A] = E[1_S(Z) | A]`, i.e. `Y` and `Z`
are conditionally independent given `A`), then `Y` is determined by `A` alone. -/
theorem IsAEDeterminedBy.of_condExp_indicator_eq [IsFiniteMeasure μ] [StandardBorelSpace β]
    [Nonempty β] {A : Ω → γ} {Z : Ω → δ} {Y : Ω → β} (hA : Measurable A) (hZ : Measurable Z)
    (hY : Measurable Y) (hdet : IsAEDeterminedBy μ (fun ω => (A ω, Z ω)) Y)
    (hlaw : ∀ S : Set δ, MeasurableSet S →
      μ[(Z ⁻¹' S).indicator (fun _ => (1 : ℝ)) | (mβ.prod mγ).comap (fun ω => (Y ω, A ω))] =ᵐ[μ]
        μ[(Z ⁻¹' S).indicator (fun _ => (1 : ℝ)) | mγ.comap A]) :
    IsAEDeterminedBy μ A Y := by
  refine hdet.of_condExp_eq (hA.prodMk hZ) hY fun f hf ⟨C, hC⟩ => ?_
  have hYA : Measurable[(mβ.prod mγ).comap (fun ω => (Y ω, A ω))] (fun ω => (Y ω, A ω)) :=
    Measurable.of_comap_le le_rfl
  have h𝓕𝒢 : mγ.comap A ≤ (mβ.prod mγ).comap (fun ω => (Y ω, A ω)) :=
    (measurable_snd.comp hYA).comap_le
  have h𝒢 : (mβ.prod mγ).comap (fun ω => (Y ω, A ω)) ≤ mΩ := (hY.prodMk hA).comap_le
  have hAZ : Measurable[(mγ.prod mδ).comap (fun ω => (A ω, Z ω))] (fun ω => (A ω, Z ω)) :=
    Measurable.of_comap_le le_rfl
  have h𝓕𝓕' : mγ.comap A ≤ (mγ.prod mδ).comap (fun ω => (A ω, Z ω)) :=
    (measurable_fst.comp hAZ).comap_le
  have h𝓕'Z : (mγ.prod mδ).comap (fun ω => (A ω, Z ω)) ≤ mγ.comap A ⊔ mδ.comap Z :=
    (MeasurableSpace.comap_prodMk A Z).le
  have hfY : StronglyMeasurable[(mβ.prod mγ).comap (fun ω => (Y ω, A ω))] (fun ω => f (Y ω)) :=
    (hf.comp (measurable_fst.comp hYA)).stronglyMeasurable
  exact condExp_eq_of_le_sup_comap h𝓕𝒢 h𝒢 h𝓕𝓕' h𝓕'Z hZ hfY
    (C := C) (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC (Y ω)) hlaw

/-- **(CPF3), the core of Lemma 7.2** (specification pp. 226–227). If `Y` (standard Borel) is
determined by the pair `(Q, Z)` and the pair `(Y, Z)` is independent of `Q`, then `Y` is determined
by `Z`: `F(Y) = E[F(Y) | Q, Z] = E[F(Y) | Z]` for every bounded measurable `F`. (In Lemma 7.2:
`Y = η_ψ`, `Z = h_ψ`, `Q = (A, h')`.) -/
theorem IsAEDeterminedBy.of_indepFun [IsProbabilityMeasure μ] [StandardBorelSpace β] [Nonempty β]
    {Q : Ω → δ} {Z : Ω → γ} {Y : Ω → β} (hQ : Measurable Q) (hZ : Measurable Z) (hY : Measurable Y)
    (hdet : IsAEDeterminedBy μ (fun ω => (Q ω, Z ω)) Y)
    (hind : IndepFun (fun ω => (Y ω, Z ω)) Q μ) : IsAEDeterminedBy μ Z Y := by
  have hdet' : IsAEDeterminedBy μ (fun ω => (Z ω, Q ω)) Y := by
    obtain ⟨g, hg, hYg⟩ := hdet
    exact ⟨fun p => g (p.2, p.1), hg.comp (measurable_snd.prodMk measurable_fst), hYg⟩
  refine hdet'.of_condExp_indicator_eq hZ hQ hY fun S hS => ?_
  have hind' : Indep (mδ.comap Q) ((mβ.prod mγ).comap (fun ω => (Y ω, Z ω))) μ :=
    ((IndepFun_iff_Indep _ _ _).1 hind).symm
  have hYZ : Measurable[(mβ.prod mγ).comap (fun ω => (Y ω, Z ω))] (fun ω => (Y ω, Z ω)) :=
    Measurable.of_comap_le le_rfl
  have hZle : mγ.comap Z ≤ (mβ.prod mγ).comap (fun ω => (Y ω, Z ω)) :=
    (measurable_snd.comp hYZ).comap_le
  have hind'' : Indep (mδ.comap Q) (mγ.comap Z) μ := indep_of_indep_of_le_right hind' hZle
  have hQm : StronglyMeasurable[mδ.comap Q] ((Q ⁻¹' S).indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator ⟨S, hS, rfl⟩
  have e1 := condExp_indep_eq hQ.comap_le (hY.prodMk hZ).comap_le hQm hind'
  have e2 := condExp_indep_eq hQ.comap_le hZ.comap_le hQm hind''
  exact e1.trans e2.symm

end Remove

section Transfer

variable {Ω Ω' γ β : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} [MeasurableSpace γ]
  [MeasurableSpace β] [MeasurableEq β] {μ : Measure Ω} {μ' : Measure Ω'}

/-- **Transfer of a determining function along equal joint laws** (Aux. lemma 51, last step, p. 242;
Proposition 7.3, p. 243). If the joint laws of `(H, Y)` under `μ` and of `(H', Y')` under `μ'` agree and
`Y = g(H)` almost surely, then `Y' = g(H')` almost surely, with the same function `g`. -/
theorem ae_eq_comp_of_map_eq {H : Ω → γ} {Y : Ω → β} {H' : Ω' → γ} {Y' : Ω' → β}
    (hHY : AEMeasurable (fun ω => (H ω, Y ω)) μ) (hHY' : AEMeasurable (fun ω => (H' ω, Y' ω)) μ')
    (hlaw : μ.map (fun ω => (H ω, Y ω)) = μ'.map (fun ω => (H' ω, Y' ω)))
    {g : γ → β} (hg : Measurable g) (h : Y =ᵐ[μ] fun ω => g (H ω)) :
    Y' =ᵐ[μ'] fun ω => g (H' ω) := by
  have hS : MeasurableSet {p : γ × β | p.2 = g p.1} :=
    measurableSet_eq_fun measurable_snd (hg.comp measurable_fst)
  have h1 : ∀ᵐ p ∂(μ.map fun ω => (H ω, Y ω)), p.2 = g p.1 := (ae_map_iff hHY hS).2 h
  rw [hlaw] at h1
  exact (ae_map_iff hHY' hS).1 h1

/-- Determination transfers along equal joint laws. -/
theorem IsAEDeterminedBy.of_map_eq {H : Ω → γ} {Y : Ω → β} {H' : Ω' → γ} {Y' : Ω' → β}
    (hHY : AEMeasurable (fun ω => (H ω, Y ω)) μ) (hHY' : AEMeasurable (fun ω => (H' ω, Y' ω)) μ')
    (hlaw : μ.map (fun ω => (H ω, Y ω)) = μ'.map (fun ω => (H' ω, Y' ω)))
    (hdet : IsAEDeterminedBy μ H Y) : IsAEDeterminedBy μ' H' Y' := by
  obtain ⟨g, hg, hYg⟩ := hdet
  exact ⟨g, hg, ae_eq_comp_of_map_eq hHY hHY' hlaw hg hYg⟩

/-- **Uniqueness of the determining function** up to a null set of the law of `H` ("the same
determining function up to a set of zero GFF probability", Proposition 7.3). -/
theorem ae_eq_of_ae_eq_comp {H : Ω → γ} (hH : AEMeasurable H μ) {Y : Ω → β} {g₁ g₂ : γ → β}
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (h₁ : Y =ᵐ[μ] fun ω => g₁ (H ω))
    (h₂ : Y =ᵐ[μ] fun ω => g₂ (H ω)) : g₁ =ᵐ[μ.map H] g₂ := by
  have hS : MeasurableSet {x : γ | g₁ x = g₂ x} := measurableSet_eq_fun hg₁ hg₂
  refine (ae_map_iff hH hS).2 ?_
  filter_upwards [h₁, h₂] with ω e1 e2
  rw [← e1, ← e2]

end Transfer

section AbsCont

variable {Ω γ β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace γ] [MeasurableSpace β]
  {μ ν : Measure Ω}

/-- Determination transfers to an absolutely continuous measure (Aux. lemma 55, p. 250: "The measures
in (HL3) are equivalent, so this identity holds for the original coupling as well"). -/
theorem IsAEDeterminedBy.of_absolutelyContinuous {H : Ω → γ} {Y : Ω → β}
    (hdet : IsAEDeterminedBy ν H Y) (hμν : μ ≪ ν) : IsAEDeterminedBy μ H Y := by
  obtain ⟨g, hg, hYg⟩ := hdet
  exact ⟨g, hg, hμν.ae_le hYg⟩

end AbsCont

end Sec7

end InteractingSLE

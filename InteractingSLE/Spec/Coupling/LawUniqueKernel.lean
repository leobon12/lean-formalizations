/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.LawUniqueTransfer
import InteractingSLE.Spec.Sec7.TwoForceMainKernel

/-!
# The joint law of an optional hull coupling from the field kernel given the history (ruling R33)

Packet PROVE-OHC-UNIQ. The joint law of the field and the killed driving history is fixed by the
history law and the conditional law of the **whole** field given the history (Wang–Wu document,
Lemma 2.8; specification, Aux. lemma 51, p. 242: "Integrating the equal kernels against the common
stopped driving law proves equality of the full joint laws"). This file proves both directions.

* `IsHistoryFieldKernel P h H Ψ`: the conditional characteristic functions of the field given the
  history are `E[e^{i(h, φ)} | σ(H)] = Ψ(H, φ)` for **every** test function `φ` on `ℍ`.
* `HasOptionalHullFieldKernel κ xL xR ρL ρR Ψ`: every coupling satisfying the frozen optional hull
  specification has this kernel with one common `Ψ` (the specification's Aux. lemma 50, p. 236, at the
  terminal history: canonical mean and raw-range Green covariance as Borel functions of the recorded
  history, the same in every coupling).
* `isOptionalHullLawUnique_of_hasOptionalHullFieldKernel`: Theorem 2.2's uniqueness in law
  (`KilledStateLawUnique`) and a common kernel give `IsOptionalHullLawUnique` (proved, with
  `Sec7.map_prod_eq_of_condExp_exp_eq`).
* `exists_hasOptionalHullFieldKernel_of_isOptionalHullLawUnique`: conversely, uniqueness of the joint
  law and one coupling give a common kernel (Doob–Dynkin on the reference coupling). So
  `HasOptionalHullFieldKernel` is exactly the content of ruling R33's lemma beyond Theorem 2.2.

**Why the frozen predicate does not supply the kernel directly.** `IsOptionalHullCoupling` prescribes
`E[e^{i(h, φ)} | 𝓕_τ]` only on the event `{supp φ ∩ K_τ = ∅}`: the conditional law of the field on the
active domain `ℍ \ K_τ`. Lévy's upward theorem along stopping times `τ_n ↑ T_*` therefore identifies
`E[e^{i(h, φ)} | σ(history)]` only for test functions avoiding the whole hull `⋃_n K_{τ_n}`; the field
on the hull (swallowed pockets, the curve itself) jointly with the later history is not prescribed.
The specification closes this gap with the optional history-marking theorems and Aux. lemmas 47–50
(pp. 227–242; "the SLE marginal and the active-component kernel alone would not imply it", p. 225),
and the Wang–Wu document requires its full ambient-field kernel (Definition 1.5: "an
active-component conditional law alone is not substituted for it").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace LawUnique

open LQGMetric

/-- **The field kernel given a history**: for every test function `φ` on `ℍ`, the conditional
characteristic function of `(h, φ)` given `σ(H)` is `Ψ(H, φ)`. -/
def IsHistoryFieldKernel {Ω Γ : Type*} {mΩ : MeasurableSpace Ω} [mΓ : MeasurableSpace Γ]
    (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (H : Ω → Γ)
    (Ψ : Γ → TestOn upperHalfPlaneOpens → ℂ) : Prop :=
  ∀ φ : TestOn upperHalfPlaneOpens,
    P[fun ω => Complex.exp (↑(h ω φ) * Complex.I) | mΓ.comap H] =ᵐ[P] fun ω => Ψ (H ω) φ

/-- **A common field kernel for all optional hull couplings** (the specification's Aux. lemma 50 at
the terminal recorded history): every coupling satisfying the frozen optional hull specification for
`κ` and the force word, on a probability space in the universe `u`, has the field kernel `Ψ` given its
killed driving history. -/
def HasOptionalHullFieldKernel (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (Ψ : HistorySpace nL nR → TestOn upperHalfPlaneOpens → ℂ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (h : Ω → DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
    IsHistoryFieldKernel P h (killedHistory W VL VR ζ) Ψ

/-- **Uniqueness of the joint law from a common field kernel** (ruling R33; Wang–Wu Lemma 2.8;
specification Aux. lemma 51, last step). Theorem 2.2's uniqueness in law for the word and a common
field kernel `Ψ` given the killed driving history (in both universes) give the uniqueness of the joint
law of the field and the killed driving history over all optional hull couplings. -/
theorem isOptionalHullLawUnique_of_hasOptionalHullFieldKernel {κ : ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ψ : HistorySpace nL nR → TestOn upperHalfPlaneOpens → ℂ}
    (hΨ : ∀ φ, Measurable fun x => Ψ x φ) (hU : KilledStateLawUnique.{u, v} κ xL xR ρL ρR)
    (hK₁ : HasOptionalHullFieldKernel.{u} κ xL xR ρL ρR Ψ)
    (hK₂ : HasOptionalHullFieldKernel.{v} κ xL xR ρL ρR Ψ) :
    IsOptionalHullLawUnique.{u, v} κ xL xR ρL ρR := by
  intro Ω₁ m₁ P₁ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ hc₁ Ω₂ m₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hc₂
  have hH₁ := measurable_killedHistory hc₁.2.2.2.1
  have hH₂ := measurable_killedHistory hc₂.2.2.2.1
  exact Sec7.map_prod_eq_of_condExp_exp_eq hΨ hc₁.2.1 hH₁ le_rfl hH₁.comap_le
    (hK₁ P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ hc₁) hc₂.2.1 hH₂ le_rfl hH₂.comap_le
    (hK₂ P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hc₂)
    (map_killedHistory_eq hU hc₁.1 hc₁.2.2.2.1 hc₂.1 hc₂.2.2.2.1)

/-- **A common field kernel from the uniqueness of the joint law.** If the joint law of the field and
the killed driving history is the same for all optional hull couplings and one such coupling exists
(on a probability space in the universe `v`), then all couplings on probability spaces in the universe
`u` have one common field kernel given the history. Together with
`isOptionalHullLawUnique_of_hasOptionalHullFieldKernel` this shows that `HasOptionalHullFieldKernel` is
exactly what ruling R33's lemma adds to Theorem 2.2. -/
theorem exists_hasOptionalHullFieldKernel_of_isOptionalHullLawUnique {κ : ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hU : IsOptionalHullLawUnique.{v, u} κ xL xR ρL ρR)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ Ψ : HistorySpace nL nR → TestOn upperHalfPlaneOpens → ℂ,
      (∀ φ, Measurable fun x => Ψ x φ) ∧ HasOptionalHullFieldKernel.{u} κ xL xR ρL ρR Ψ := by
  obtain ⟨Ω₀, m₀, P₀, _, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hc₀⟩ := href
  have hH₀ := measurable_killedHistory hc₀.2.2.2.1
  -- Doob–Dynkin on the reference coupling
  have hDD : ∀ φ : TestOn upperHalfPlaneOpens, ∃ g : HistorySpace nL nR → ℂ, StronglyMeasurable g ∧
      P₀[fun ω => Complex.exp (↑(h₀ ω φ) * Complex.I) |
        MeasurableSpace.comap (killedHistory W₀ VL₀ VR₀ ζ₀) inferInstance] =
        g ∘ killedHistory W₀ VL₀ VR₀ ζ₀ :=
    fun φ => stronglyMeasurable_condExp.exists_eq_measurable_comp
  choose g hgm hgeq using hDD
  refine ⟨fun x φ => g φ x, fun φ => (hgm φ).measurable, ?_⟩
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hc φ
  have hH := measurable_killedHistory hc.2.2.2.1
  have hlaw := hU P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hc₀ P 𝓕 W VL VR B ζ h hc
  -- the history marginals agree
  have hlawH : P₀.map (killedHistory W₀ VL₀ VR₀ ζ₀) = P.map (killedHistory W VL VR ζ) := by
    have e₀ : P₀.map (killedHistory W₀ VL₀ VR₀ ζ₀) =
        (P₀.map fun ω => (h₀ ω, killedHistory W₀ VL₀ VR₀ ζ₀ ω)).map Prod.snd := by
      rw [Measure.map_map measurable_snd (hc₀.2.1.prodMk hH₀)]
      rfl
    have e : P.map (killedHistory W VL VR ζ) =
        (P.map fun ω => (h ω, killedHistory W VL VR ζ ω)).map Prod.snd := by
      rw [Measure.map_map measurable_snd (hc.2.1.prodMk hH)]
      rfl
    rw [e₀, e, hlaw]
  -- the reference kernel, integrated over history events
  have hk₀ : ∀ S : Set (HistorySpace nL nR), MeasurableSet S →
      ∫ p in univ ×ˢ S, Complex.exp (↑(p.1 φ) * Complex.I)
        ∂(P₀.map fun ω => (h₀ ω, killedHistory W₀ VL₀ VR₀ ζ₀ ω)) =
        ∫ x in S, g φ x ∂(P₀.map (killedHistory W₀ VL₀ VR₀ ζ₀)) := fun S hS =>
    Sec7.setIntegral_exp_map_eq_of_condExp (Ψ := fun x φ => g φ x) (fun φ => (hgm φ).measurable)
      hc₀.2.1 hH₀ le_rfl hH₀.comap_le φ (Eventually.of_forall fun ω => congrFun (hgeq φ) ω) hS
  have hm1 : Measurable fun p : DistOn upperHalfPlaneOpens × HistorySpace nL nR =>
      Complex.exp (↑(p.1 φ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      ((Sobolev.measurable_distOn_apply φ).comp measurable_fst)).mul_const _)
  have hint : Integrable (fun ω => Complex.exp (↑(h ω φ) * Complex.I)) P :=
    Sobolev.integrable_exp_mul_I ((Sobolev.measurable_distOn_apply φ).comp hc.2.1)
  have hgint : Integrable (g φ) (P.map (killedHistory W VL VR ζ)) := by
    rw [← hlawH, integrable_map_measure (hgm φ).aestronglyMeasurable hH₀.aemeasurable, ← hgeq φ]
    exact integrable_condExp
  have hgint' : Integrable (fun ω => g φ (killedHistory W VL VR ζ ω)) P :=
    (integrable_map_measure (hgm φ).aestronglyMeasurable hH.aemeasurable).1 hgint
  refine (ae_eq_condExp_of_forall_setIntegral_eq hH.comap_le hint
    (fun s _ _ => hgint'.integrableOn) (fun s hs _ => ?_)
    ((hgm φ).comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable).symm
  obtain ⟨S, hS, rfl⟩ := hs
  calc ∫ ω in killedHistory W VL VR ζ ⁻¹' S, g φ (killedHistory W VL VR ζ ω) ∂P
      = ∫ x in S, g φ x ∂(P.map (killedHistory W VL VR ζ)) :=
        (setIntegral_map hS (hgm φ).aestronglyMeasurable hH.aemeasurable).symm
    _ = ∫ x in S, g φ x ∂(P₀.map (killedHistory W₀ VL₀ VR₀ ζ₀)) := by rw [hlawH]
    _ = ∫ p in univ ×ˢ S, Complex.exp (↑(p.1 φ) * Complex.I)
          ∂(P₀.map fun ω => (h₀ ω, killedHistory W₀ VL₀ VR₀ ζ₀ ω)) := (hk₀ S hS).symm
    _ = ∫ p in univ ×ˢ S, Complex.exp (↑(p.1 φ) * Complex.I)
          ∂(P.map fun ω => (h ω, killedHistory W VL VR ζ ω)) := by rw [hlaw]
    _ = ∫ ω in (fun ω => (h ω, killedHistory W VL VR ζ ω)) ⁻¹' (univ ×ˢ S),
          Complex.exp (↑(h ω φ) * Complex.I) ∂P :=
        setIntegral_map (MeasurableSet.univ.prod hS) hm1.aestronglyMeasurable
          (hc.2.1.prodMk hH).aemeasurable
    _ = ∫ ω in killedHistory W VL VR ζ ⁻¹' S, Complex.exp (↑(h ω φ) * Complex.I) ∂P := by
        have hpre : (fun ω => (h ω, killedHistory W VL VR ζ ω)) ⁻¹' (univ ×ˢ S) =
            killedHistory W VL VR ζ ⁻¹' S := by
          ext ω
          simp only [mem_preimage, mem_prod, mem_univ, true_and]
        rw [hpre]

end LawUnique

end InteractingSLE

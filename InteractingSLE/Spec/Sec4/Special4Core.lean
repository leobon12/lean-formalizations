/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Special3Uniqueness

/-!
# Aux. lemma 23: the measure-theoretic core with the thin-hull hypothesis on the probability space

Packet PROVE-SEC4-A4, item (2). PROVE-SEC4-B3's `map_prod_eq_of_condCharFun_off` takes the dimension hypothesis (SR3)
almost surely for the *law* of the history. In Aux. lemma 23 it comes from the trace of the driving process, almost
surely on the probability space; transferring it to the law would need the measurability of a dimension event. Here the
core is proved with (SR3) almost surely in `ω`:

* `map_prod_eq_of_ae_condDistrib_eq`: two joint laws `(X, h)` agree when the history laws agree and the conditional
  laws of `h` agree at `X₁(ω)` for almost every `ω` (rectangles, no measurability of the agreement set needed);
* `map_prod_eq_of_condCharFun_off_ae`: B3's core with `hSR3 : ∀ᵐ o ∂P₁, … A (X₁ o) …`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace InteractingSLE.Sec4

open LQGMetric TopologicalSpace InteractingSLE.Sobolev

/-- **Joint laws from conditional laws along the first history.** If the history laws agree and, for almost every
`ω`, the conditional laws of the two fields given the history agree at `X₁(ω)`, the joint laws agree. -/
theorem map_prod_eq_of_ae_condDistrib_eq {Ω₁ Ω₂ Γ E : Type*} {m₁ : MeasurableSpace Ω₁}
    {m₂ : MeasurableSpace Ω₂} [MeasurableSpace Γ] [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {h₁ : Ω₁ → E} {X₁ : Ω₁ → Γ} {h₂ : Ω₂ → E} {X₂ : Ω₂ → Γ} (hh₁ : Measurable h₁)
    (hX₁ : Measurable X₁) (hh₂ : Measurable h₂) (hX₂ : Measurable X₂)
    (hlaw : P₁.map X₁ = P₂.map X₂)
    (hker : ∀ᵐ o ∂P₁, condDistrib h₂ X₂ P₂ (X₁ o) = condDistrib h₁ X₁ P₁ (X₁ o)) :
    P₁.map (fun o => (X₁ o, h₁ o)) = P₂.map (fun o => (X₂ o, h₂ o)) := by
  rw [← compProd_map_condDistrib hX₁.aemeasurable hh₁.aemeasurable,
    ← compProd_map_condDistrib hX₂.aemeasurable hh₂.aemeasurable, ← hlaw]
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
  rintro _ ⟨B, hB, C, hC, rfl⟩
  rw [Measure.compProd_apply_prod hB hC, Measure.compProd_apply_prod hB hC,
    setLIntegral_map hB ((condDistrib h₁ X₁ P₁).measurable_coe hC) hX₁,
    setLIntegral_map hB ((condDistrib h₂ X₂ P₂).measurable_coe hC) hX₁]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hker] with o ho
  rw [ho]

variable {U : Opens ℂ}

/-- **The core of Aux. lemma 23 with (SR3) almost surely on the probability space** (B3's
`map_prod_eq_of_condCharFun_off`, whose (SR3) is almost sure for the history law). -/
theorem map_prod_eq_of_condCharFun_off_ae {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {Γ : Type*} {mΓ : MeasurableSpace Γ} {A : Γ → Set ℂ}
    (hAcl : ∀ γ, closure (A γ) ∩ U ⊆ A γ)
    (hAm : ∀ K : Set ℂ, IsCompact K → MeasurableSet {γ | Disjoint K (A γ)})
    {G : TestOn U → Γ → ℂ} (hG : ∀ φ, Measurable (G φ))
    {Ω₁ : Type*} {J₁ m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {h₁ : Ω₁ → DistOn U} {X₁ : Ω₁ → Γ} (hh₁ : Measurable h₁) (hX₁ : Measurable X₁)
    (hXJ₁ : MeasurableSpace.comap X₁ mΓ ≤ J₁) (hJ₁ : J₁ ≤ m₁)
    (hSR1₁ : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h₁ o) ζ ∂P₁ < ⊤)
    (hcf₁ : ∀ φ : TestOn U, ∀ᵐ o ∂P₁, Disjoint (tsupport φ) (A (X₁ o)) →
      P₁[fun o => Complex.exp (↑(h₁ o φ) * Complex.I) | J₁] o = G φ (X₁ o))
    {Ω₂ : Type*} {J₂ m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn U} {X₂ : Ω₂ → Γ} (hh₂ : Measurable h₂) (hX₂ : Measurable X₂)
    (hXJ₂ : MeasurableSpace.comap X₂ mΓ ≤ J₂) (hJ₂ : J₂ ≤ m₂)
    (hSR1₂ : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h₂ o) ζ ∂P₂ < ⊤)
    (hcf₂ : ∀ φ : TestOn U, ∀ᵐ o ∂P₂, Disjoint (tsupport φ) (A (X₂ o)) →
      P₂[fun o => Complex.exp (↑(h₂ o φ) * Complex.I) | J₂] o = G φ (X₂ o))
    (hlaw : P₁.map X₁ = P₂.map X₂)
    (hSR3 : ∀ᵐ o ∂P₁, ∀ K, IsCompact K → K ⊆ U →
      dimH (A (X₁ o) ∩ K) < ENNReal.ofReal (2 - 2 * ε)) :
    P₁.map (fun o => (X₁ o, h₁ o)) = P₂.map (fun o => (X₂ o, h₂ o)) := by
  classical
  have hcut : ∀ k, ∃ ζ : TestOn U, EqOn ζ 1 (exhaustK U k) := fun k => by
    obtain ⟨ζ, -, h1⟩ := exists_cutoff_testOn (exhaustK U k).isCompact (exhaustK_subset U k)
    exact ⟨ζ, h1⟩
  choose ζ hζ using hcut
  have hc₁ : ∀ᵐ γ ∂(P₁.map X₁), condDistrib h₁ X₁ P₁ γ (cutoffSet ε ζ)ᶜ = 0 :=
    ae_condDistrib_compl_cutoffSet hX₁ hh₁ hSR1₁
  have hc₂ : ∀ᵐ γ ∂(P₁.map X₁), condDistrib h₂ X₂ P₂ γ (cutoffSet ε ζ)ᶜ = 0 := by
    rw [hlaw]; exact ae_condDistrib_compl_cutoffSet hX₂ hh₂ hSR1₂
  have hF : ∀ F : Finset (TestIdx U × ℚ), ∀ᵐ γ ∂(P₁.map X₁),
      (∀ p ∈ F, Disjoint (ratUnion p.1.1.1 : Set ℂ) (A γ)) →
        ∫ T, Complex.exp (↑(T (ratTest F)) * Complex.I) ∂(condDistrib h₂ X₂ P₂ γ) =
          ∫ T, Complex.exp (↑(T (ratTest F)) * Complex.I) ∂(condDistrib h₁ X₁ P₁ γ) := by
    intro F
    have hB := hAm (tsupport (ratTest F)) (ratTest F).hasCompactSupport
    have e₁ := ae_integral_condDistrib_eq_off hX₁ hXJ₁ hJ₁ hh₁ hB (hG _) (hcf₁ (ratTest F))
    have e₂ := ae_integral_condDistrib_eq_off hX₂ hXJ₂ hJ₂ hh₂ hB (hG _) (hcf₂ (ratTest F))
    rw [← hlaw] at e₂
    filter_upwards [e₁, e₂] with γ g1 g2 hd
    have hd' : γ ∈ {γ | Disjoint (tsupport (ratTest F)) (A γ)} := disjoint_tsupport_ratTest hd
    rw [g1 hd', g2 hd']
  have hlaw' : ∀ᵐ γ ∂(P₁.map X₁), (∀ F : Finset (TestIdx U × ℚ),
      (∀ p ∈ F, Disjoint (ratUnion p.1.1.1 : Set ℂ) (A γ)) →
        ∫ T, Complex.exp (↑(T (ratTest F)) * Complex.I) ∂(condDistrib h₂ X₂ P₂ γ) =
          ∫ T, Complex.exp (↑(T (ratTest F)) * Complex.I) ∂(condDistrib h₁ X₁ P₁ γ)) ∧
      condDistrib h₁ X₁ P₁ γ (cutoffSet ε ζ)ᶜ = 0 ∧ condDistrib h₂ X₂ P₂ γ (cutoffSet ε ζ)ᶜ = 0 := by
    filter_upwards [ae_all_iff.2 hF, hc₁, hc₂] with γ h1 h2 h3 using ⟨h1, h2, h3⟩
  have hker : ∀ᵐ o ∂P₁, condDistrib h₂ X₂ P₂ (X₁ o) = condDistrib h₁ X₁ P₁ (X₁ o) := by
    filter_upwards [ae_of_ae_map hX₁.aemeasurable hlaw', hSR3] with o ho hγ3
    exact eq_of_integral_exp_ratTest hε0 hε1 hζ (hAcl _) hγ3 ho.2.2 ho.2.1 ho.1
  exact map_prod_eq_of_ae_condDistrib_eq hh₁ hX₁ hh₂ hX₂ hlaw hker

end InteractingSLE.Sec4

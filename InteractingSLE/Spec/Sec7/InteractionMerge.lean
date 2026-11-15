/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.AgreeAsCurvesAfter
import InteractingSLE.Spec.Sec7.InteractionFirstContact

/-!
# Merging as ordered unparametrized curves (§7.2, deterministic part of Corollary 7.12E)

Packet PROVE-SEC7-B. The frozen predicate `AgreeAsCurvesAfter η₁ ζ₁ s₀ η₂ ζ₂ t₀` (Corollary 7.12E,
p. 460) says that after the contact `η₁(s₀) = η₂(t₀)` the two available paths agree as ordered
unparametrized curves until the shorter available portion ends.

* `AgreeAsCurvesAfter.symm`: the relation is symmetric.
* **The last step of the proof of Corollary 7.12E** (p. 461: "Write `γ` for the common relative
  path. Restricting by the two reconstructed functionals gives the actual continuations
  `φ⁻¹(γ|[0, Uᵢ])`, with their original clocks. They agree as ordered curves through `U₁ ∧ U₂`."):
  if both available continuations are the common path `Γ` read through strictly increasing clocks
  `cᵢ` mapping `[0, Uᵢ]` onto `[sᵢ, ζᵢ]`, then `AgreeAsCurvesAfter` holds
  (`agreeAsCurvesAfter_of_clocks`). The clocks need not be equal.
* **Merging persists** (Theorem 1.5 (ii) asserts merging at every interior available contact, not
  only at the first one): for injective curves, merging at the first contact gives merging at every
  later contact (`agreeAsCurvesAfter_of_isFirstContact`, via `AgreeAsCurvesAfter.restrict`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- `AgreeAsCurvesAfter` is symmetric (use the inverse order isomorphism). -/
theorem AgreeAsCurvesAfter.symm {s₀ t₀ : ℝ≥0} (h : AgreeAsCurvesAfter η₁ ζ₁ s₀ η₂ ζ₂ t₀) :
    AgreeAsCurvesAfter η₂ ζ₂ t₀ η₁ ζ₁ s₀ := by
  obtain ⟨a, c, hs₀a, haζ, ht₀c, hcζ, hor, e, he⟩ := h
  refine ⟨c, a, ht₀c, hcζ, hs₀a, haζ, hor.symm, e.symm, fun t => ?_⟩
  rw [← he (e.symm t), OrderIso.apply_symm_apply]

/-- A strictly increasing clock `c` mapping `[0, U]` onto `[t₀, ζ]` maps each `[0, V]`, `V ≤ U`, onto
`[t₀, c V]`. -/
theorem image_setOf_coe_le_of_strictMonoOn {c : ℝ≥0 → ℝ≥0} {U ζ : ℝ≥0∞} {t₀ : ℝ≥0}
    (hc : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U})
    (himg : c '' {u | (u : ℝ≥0∞) ≤ U} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ}) {V : ℝ≥0}
    (hV : (V : ℝ≥0∞) ≤ U) :
    c '' {u | (u : ℝ≥0∞) ≤ (V : ℝ≥0∞)} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ (c V : ℝ≥0∞)} := by
  have hmem : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U → t₀ ≤ c u ∧ (c u : ℝ≥0∞) ≤ ζ := fun u hu => by
    have : c u ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := mem_image_of_mem c hu
    rw [himg] at this
    exact this
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have huU : (u : ℝ≥0∞) ≤ U := hu.trans hV
    exact ⟨(hmem u huU).1,
      ENNReal.coe_le_coe.mpr (hc.monotoneOn huU hV (ENNReal.coe_le_coe.mp hu))⟩
  · rintro ⟨ht₀, htV⟩
    have ht : t ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := by
      rw [himg]
      exact ⟨ht₀, htV.trans (hmem V hV).2⟩
    obtain ⟨u, hu, rfl⟩ := ht
    exact ⟨u, ENNReal.coe_le_coe.mpr ((hc.le_iff_le hu hV).mp (ENNReal.coe_le_coe.mp htV)), rfl⟩

/-- `agreeAsCurvesAfter_of_clocks` when the first relative lifetime is the shorter one. -/
theorem agreeAsCurvesAfter_of_clocks_of_le {Γ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0}
    {c₁ c₂ : ℝ≥0 → ℝ≥0} (hc₁ : StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁})
    (hc₂ : StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂})
    (himg₁ : c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁})
    (himg₂ : c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂})
    (h₁ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → η₁ (c₁ u) = Γ u)
    (h₂ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → η₂ (c₂ u) = Γ u) (hU : U₁ ≤ U₂) :
    AgreeAsCurvesAfter η₁ ζ₁ s₀ η₂ ζ₂ t₀ := by
  have hmem₁ : c₁ 0 ∈ c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} := mem_image_of_mem c₁ (by simp)
  rw [himg₁] at hmem₁
  have hmem₂ : c₂ 0 ∈ c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} := mem_image_of_mem c₂ (by simp)
  rw [himg₂] at hmem₂
  have hS : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U₁} ⊆ {u | (u : ℝ≥0∞) ≤ U₂} := fun u hu => hu.trans hU
  obtain ⟨c, hcζ, ht₀c, himg₂'⟩ : ∃ c : ℝ≥0∞, c ≤ ζ₂ ∧ (t₀ : ℝ≥0∞) ≤ c ∧
      c₂ '' {u | (u : ℝ≥0∞) ≤ U₁} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ c} := by
    rcases eq_or_ne U₁ ⊤ with hU₁ | hU₁
    · have hU₂ : U₂ = ⊤ := top_le_iff.mp (hU₁ ▸ hU)
      refine ⟨ζ₂, le_rfl, (ENNReal.coe_le_coe.mpr hmem₂.1).trans hmem₂.2, ?_⟩
      rw [hU₁, ← hU₂]
      exact himg₂
    · obtain ⟨V, rfl⟩ : ∃ V : ℝ≥0, (V : ℝ≥0∞) = U₁ := ⟨U₁.toNNReal, ENNReal.coe_toNNReal hU₁⟩
      have hV := image_setOf_coe_le_of_strictMonoOn hc₂ himg₂ hU
      have hcV : c₂ V ∈ c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} := mem_image_of_mem c₂ hU
      rw [himg₂] at hcV
      exact ⟨c₂ V, hcV.2, ENNReal.coe_le_coe.mpr hcV.1, hV⟩
  let e₁ := hc₁.orderIso c₁ {u | (u : ℝ≥0∞) ≤ U₁}
  let e₂ := (hc₂.mono hS).orderIso c₂ {u | (u : ℝ≥0∞) ≤ U₁}
  let e := (Set.orderIsoOfEq _ _ himg₁).symm.trans
    (e₁.symm.trans (e₂.trans (Set.orderIsoOfEq _ _ himg₂')))
  refine ⟨ζ₁, c, (ENNReal.coe_le_coe.mpr hmem₁.1).trans hmem₁.2, le_rfl, ht₀c, hcζ, Or.inl rfl,
    e, fun s => ?_⟩
  set x := e₁.symm ((Set.orderIsoOfEq _ _ himg₁).symm s) with hx
  have hx₁ : c₁ x = s := by
    have : e₁ x = (Set.orderIsoOfEq _ _ himg₁).symm s := by rw [hx, OrderIso.apply_symm_apply]
    exact congrArg Subtype.val this
  have hx₂ : (e s : ℝ≥0) = c₂ x := rfl
  rw [hx₂, h₂ x (hS x.2), ← h₁ x x.2, hx₁]

/-- **Corollary 7.12E, final step** (p. 461): if the two available continuations after the contact
`η₁(s₀) = η₂(t₀)` are one common path `Γ` read through strictly increasing clocks `cᵢ` mapping the
relative available intervals `[0, Uᵢ]` onto `[s₀, ζ₁]` and `[t₀, ζ₂]` (`ηᵢ(cᵢ u) = Γ(u)`), then they
agree as ordered unparametrized curves until the shorter available portion ends. The clocks need not
be equal. -/
theorem agreeAsCurvesAfter_of_clocks {Γ : ℝ≥0 → ℂ} {U₁ U₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0}
    {c₁ c₂ : ℝ≥0 → ℝ≥0} (hc₁ : StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁})
    (hc₂ : StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂})
    (himg₁ : c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁})
    (himg₂ : c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂})
    (h₁ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → η₁ (c₁ u) = Γ u)
    (h₂ : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → η₂ (c₂ u) = Γ u) :
    AgreeAsCurvesAfter η₁ ζ₁ s₀ η₂ ζ₂ t₀ := by
  rcases le_total U₁ U₂ with hU | hU
  · exact agreeAsCurvesAfter_of_clocks_of_le hc₁ hc₂ himg₁ himg₂ h₁ h₂ hU
  · exact AgreeAsCurvesAfter.symm (agreeAsCurvesAfter_of_clocks_of_le hc₂ hc₁ himg₂ himg₁ h₂ h₁ hU)

/-- Restriction of a merging order isomorphism to a later point `x` of the merged arc. -/
theorem AgreeAsCurvesAfter.restrict {s₀ t₀ : ℝ≥0} {a c : ℝ≥0∞} (haζ : a ≤ ζ₁) (hcζ : c ≤ ζ₂)
    (hor : a = ζ₁ ∨ c = ζ₂)
    (e : {s : ℝ≥0 // s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ a} ≃o {t : ℝ≥0 // t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ c})
    (he : ∀ s, η₂ (e s) = η₁ s) (x : {s : ℝ≥0 // s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ a}) :
    AgreeAsCurvesAfter η₁ ζ₁ x.1 η₂ ζ₂ (e x).1 := by
  let f : {s : ℝ≥0 // x.1 ≤ s ∧ (s : ℝ≥0∞) ≤ a} → {t : ℝ≥0 // (e x).1 ≤ t ∧ (t : ℝ≥0∞) ≤ c} :=
    fun y => ⟨(e ⟨y.1, x.2.1.trans y.2.1, y.2.2⟩).1,
      e.monotone (show x ≤ ⟨y.1, x.2.1.trans y.2.1, y.2.2⟩ from y.2.1), (e _).2.2⟩
  let g : {t : ℝ≥0 // (e x).1 ≤ t ∧ (t : ℝ≥0∞) ≤ c} → {s : ℝ≥0 // x.1 ≤ s ∧ (s : ℝ≥0∞) ≤ a} :=
    fun z => ⟨(e.symm ⟨z.1, (e x).2.1.trans z.2.1, z.2.2⟩).1, by
      have : x ≤ e.symm ⟨z.1, (e x).2.1.trans z.2.1, z.2.2⟩ := by
        rw [← e.le_iff_le, OrderIso.apply_symm_apply]
        exact z.2.1
      exact this, (e.symm _).2.2⟩
  let e' : {s : ℝ≥0 // x.1 ≤ s ∧ (s : ℝ≥0∞) ≤ a} ≃o {t : ℝ≥0 // (e x).1 ≤ t ∧ (t : ℝ≥0∞) ≤ c} :=
    { toFun := f
      invFun := g
      left_inv := fun y => Subtype.ext <| by
        simp only [Subtype.coe_eta, OrderIso.symm_apply_apply, f, g]
      right_inv := fun z => Subtype.ext <| by
        simp only [Subtype.coe_eta, OrderIso.apply_symm_apply, f, g]
      map_rel_iff' := fun {_ _} => e.le_iff_le }
  refine ⟨a, c, x.2.2, haζ, (e x).2.2, hcζ, hor, e', fun y => ?_⟩
  exact he _

/-- **Merging persists.** For injective stopped curves, if they merge at their first contact
`(s₀, t₀)` (`AgreeAsCurvesAfter`), then they merge at every finite-parameter contact `(s, t)`
(the contact lies on the merged arc, `t = e(s)`). This reduces Theorem 1.5 (ii), stated at every
interior available contact, to merging at the first contact. -/
theorem agreeAsCurvesAfter_of_isFirstContact {s₀ t₀ s t : ℝ≥0}
    (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) (hm : AgreeAsCurvesAfter η₁ ζ₁ s₀ η₂ ζ₂ t₀)
    (hst : (s, t) ∈ stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂) :
    AgreeAsCurvesAfter η₁ ζ₁ s η₂ ζ₂ t := by
  obtain ⟨a, c, hs₀a, haζ, ht₀c, hcζ, hor, e, he⟩ := hm
  obtain ⟨-, hsζ, -, htζ, hst'⟩ := hst
  have hle := h₀.2.2.2 s t hsζ htζ hst'
  obtain ⟨x, hxs, hxt⟩ : ∃ x : {s : ℝ≥0 // s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ a}, x.1 = s ∧ (e x).1 = t := by
    rcases hor with rfl | rfl
    · refine ⟨⟨s, hle.1, hsζ⟩, rfl, hi₂ ((e _).2.2.trans hcζ)
        htζ ?_⟩
      rw [he, ← hst']
    · set y := e.symm ⟨t, hle.2, htζ⟩ with hy
      have hys : y.1 = s := by
        refine hi₁ (y.2.2.trans haζ) hsζ ?_
        rw [← he y, hy, OrderIso.apply_symm_apply, hst']
      refine ⟨y, hys, ?_⟩
      rw [hy, OrderIso.apply_symm_apply]
  have := AgreeAsCurvesAfter.restrict haζ hcζ hor e he x
  rw [hxs, hxt] at this
  exact this

/-- **Theorem 1.5 (ii), pointwise reduction.** For injective stopped curves, if an interior available
contact forces a first contact at which the curves merge (Lemma 7.7 with Corollary 7.12E), then they
merge at every interior available contact — the conclusion of `IsFlowLine.merges` for one
realization. -/
theorem agreeAsCurvesAfter_of_firstContact_merge (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hfirst : (∃ s t : ℝ≥0, IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀ ∧ AgreeAsCurvesAfter η₁ ζ₁ s₀ η₂ ζ₂ t₀) :
    ∀ s t : ℝ≥0, IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t →
      AgreeAsCurvesAfter η₁ ζ₁ s η₂ ζ₂ t := by
  intro s t h
  obtain ⟨s₀, t₀, h₀, hm⟩ := hfirst ⟨s, t, h⟩
  exact agreeAsCurvesAfter_of_isFirstContact hi₁ hi₂ h₀ hm
    (IsInteriorAvailableContact.mem_stoppedContactSet h)

end Sec7

end InteractingSLE

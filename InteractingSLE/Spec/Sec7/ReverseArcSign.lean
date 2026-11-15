/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcSide
import InteractingSLE.Foundations.Loewner.Reflect

/-!
# Aux. lemma 69, the side, in the two physical charts

Packet PROVE-LEMMA76B. The centred side lemma `ReverseArc.exists_pos_tendsto` is moved to the physical seeds:

* `ReverseArc.exists_pos_tendsto_phys`: for `α` from `x₁` and `β` from `x₂ < x₁`, the first chart
  `f₁ = f_q(· − x₁)` has a positive limit along every approach to `α(s)` from the joint unbounded domain (the right side
  of `α`);
* `ReverseArc.exists_neg_tendsto_phys`: with the roles exchanged by the reflection `z ↦ −z̄` (`Foundations/Loewner/
  Reflect.lean`), the second chart `f₂ = f_{q'}(· − x₂)` has a negative limit (the left side of `β`).

The planar notions are invariant under the translations `z ↦ z + c` (`c` real) and the reflection
(`fillH_image_homeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart

namespace ReverseArc

/-! ### Invariance of the filling -/

/-- **The filling is invariant under a homeomorphism of `ℂ` preserving `ℍ` and boundedness.** -/
theorem fillH_image_homeomorph (e : ℂ ≃ₜ ℂ) (heH : ∀ z, e z ∈ H ↔ z ∈ H)
    (hb : ∀ S : Set ℂ, IsBounded (e '' S) ↔ IsBounded S) (A : Set ℂ) : fillH (e '' A) = e '' fillH A := by
  have hHd : ∀ S : Set ℂ, H \ e '' S = e '' (H \ S) := by
    intro S
    ext w
    constructor
    · rintro ⟨hwH, hwS⟩
      refine ⟨e.symm w, ⟨(heH _).1 (by rw [e.apply_symm_apply]; exact hwH), fun h => hwS ⟨_, h, e.apply_symm_apply w⟩⟩,
        e.apply_symm_apply w⟩
    · rintro ⟨v, ⟨hvH, hvS⟩, rfl⟩
      exact ⟨(heH v).2 hvH, fun ⟨u, hu, he⟩ => hvS (e.injective he ▸ hu)⟩
  have hcc : ∀ z, connectedComponentIn (H \ closure (e '' A)) (e z) =
      e '' connectedComponentIn (H \ closure A) z := by
    intro z
    rw [← e.image_closure, hHd]
    by_cases hz : z ∈ H \ closure A
    · exact (e.image_connectedComponentIn hz).symm
    · rw [connectedComponentIn_eq_empty hz, image_empty]
      refine connectedComponentIn_eq_empty fun h => hz ?_
      obtain ⟨v, hv, hvz⟩ := h
      rw [← e.injective hvz]
      exact hv
  ext w
  constructor
  · rintro ⟨hwH, hw⟩
    refine ⟨e.symm w, ⟨(heH _).1 (by rw [e.apply_symm_apply]; exact hwH), ?_⟩, e.apply_symm_apply w⟩
    rcases hw with hw | hw
    · left
      rw [← e.image_closure] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      rwa [e.symm_apply_apply]
    · right
      rw [← e.apply_symm_apply w, hcc, hb] at hw
      exact hw
  · rintro ⟨v, ⟨hvH, hv⟩, rfl⟩
    refine ⟨(heH v).2 hvH, ?_⟩
    rcases hv with hv | hv
    · left
      rw [← e.image_closure]
      exact mem_image_of_mem _ hv
    · right
      rw [hcc, hb]
      exact hv

/-- The translation by a real number. -/
def transR (c : ℝ) : ℂ ≃ₜ ℂ := Homeomorph.addRight (c : ℂ)

theorem transR_apply (c : ℝ) (z : ℂ) : transR c z = z + c := rfl

theorem fillH_image_add (c : ℝ) (A : Set ℂ) :
    fillH ((fun z => z + (c : ℂ)) '' A) = (fun z => z + (c : ℂ)) '' fillH A := by
  have := fillH_image_homeomorph (transR c) (fun z => by
    show 0 < (z + (c : ℂ)).im ↔ 0 < z.im
    simp) (fun S => by
      constructor
      · intro h
        have := (isometry_add_right (-(c : ℂ))).lipschitzWith.isBounded_image h
        rwa [← image_comp, show ((fun z => z + -(c : ℂ)) ∘ transR c) = id from funext fun z => by
          simp [transR_apply], image_id] at this
      · exact (isometry_add_right (c : ℂ)).lipschitzWith.isBounded_image) A
  exact this

theorem image_H_diff_homeomorph (e : ℂ ≃ₜ ℂ) (heH : ∀ z, e z ∈ H ↔ z ∈ H) (X : Set ℂ) :
    e '' (H \ X) = H \ e '' X := by
  ext w
  constructor
  · rintro ⟨v, ⟨hvH, hvX⟩, rfl⟩
    exact ⟨(heH v).2 hvH, fun ⟨u, hu, he⟩ => hvX (e.injective he ▸ hu)⟩
  · rintro ⟨hwH, hwX⟩
    exact ⟨e.symm w, ⟨(heH _).1 (by rw [e.apply_symm_apply]; exact hwH),
      fun h => hwX ⟨_, h, e.apply_symm_apply w⟩⟩, e.apply_symm_apply w⟩

theorem transR_mem_H (c : ℝ) (z : ℂ) : transR c z ∈ H ↔ z ∈ H := by
  show 0 < (z + (c : ℂ)).im ↔ 0 < z.im
  simp

/-- **The right side of the first trace in its physical chart**: along every approach to the non-tip point
`α(s) ∈ ℍ` from the joint unbounded domain, `f_q(· − x₁)` has a positive limit. -/
theorem exists_pos_tendsto_phys {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} (hp₁ : IsPathGood α ζ₁ x₁)
    (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁) {W : ℝ≥0 → ℝ}
    (hg : IsGeneratingTrace W ζ₁ (fun t => α t - x₁)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ₁})
    (hW0 : W 0 = 0) {q σ : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ₁) (htip : α q ∈ H) (hσ : (σ : ℝ≥0∞) ≤ ζ₂)
    (hβσ : β σ = α q) (hdisj : ∀ t < σ, β t ∉ α '' Icc 0 q) {s : ℝ≥0} (hsq : s < q) (hsH : α s ∈ H)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q ∪ β '' Icc 0 σ)] (α s)) :
    ∃ y : ℝ, 0 < y ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x₁)) U (𝓝 (y : ℂ)) := by
  set e := transR (-x₁) with he
  have heap : ∀ z, e z = z - x₁ := fun z => by rw [he, transR_apply]; push_cast; ring
  have hp₁' : IsPathGood (fun t => e (α t)) ζ₁ 0 := by
    refine ⟨fun a ha b hb hab => hp₁.1 ha hb (e.injective hab), W, hWc, hW0, ?_⟩
    simpa [heap] using hg
  have hp₂' : IsPathGood (fun t => e (β t)) ζ₂ (x₂ - x₁) := by
    obtain ⟨hi, w, hw, hw0, hg₂⟩ := hp₂
    refine ⟨fun a ha b hb hab => hi ha hb (e.injective hab), w, hw, hw0, ?_⟩
    have e₁ : (fun t => e (β t) - ((x₂ - x₁ : ℝ) : ℂ)) = fun t => β t - x₂ := by
      funext t; rw [heap]; push_cast; ring
    rw [e₁]; exact hg₂
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hsq
  have hch := isChart (η := fun t => e (α t)) (by simpa [heap] using hg) hWc hW0
    (fun a ha b hb hab => by
      simp only [heap] at hab
      exact hp₁.1 ha hb (sub_left_injective hab)) hq hq0
  have himA : (fun t => e (α t)) '' Icc 0 q = e '' (α '' Icc 0 q) := by rw [image_image]
  have himB : (fun t => e (β t)) '' Icc 0 σ = e '' (β '' Icc 0 σ) := by rw [image_image]
  have hU' : ((U.map e : Ultrafilter ℂ) : Filter ℂ) ≤
      𝓝[H \ fillH ((fun t => e (α t)) '' Icc 0 q ∪ (fun t => e (β t)) '' Icc 0 σ)] (e (α s)) := by
    rw [Ultrafilter.coe_map, himA, himB, ← image_union, fillH_image_homeomorph e (transR_mem_H _) ?_,
      ← image_H_diff_homeomorph e (transR_mem_H _), ← e.isEmbedding.map_nhdsWithin_eq]
    · exact map_mono hU
    · intro S
      constructor
      · intro h
        have := (isometry_add_right (x₁ : ℂ)).lipschitzWith.isBounded_image h
        rwa [← image_comp, show ((fun z => z + (x₁ : ℂ)) ∘ e) = id from funext fun z => by
          simp [heap], image_id] at this
      · exact (isometry_add_right _).lipschitzWith.isBounded_image
  have hH : ∀ z, e z ∈ H ↔ z ∈ H := transR_mem_H _
  obtain ⟨y, hy, hlim⟩ := exists_pos_tendsto hp₁' hp₂' (by linarith) hch hq.le ((hH _).2 htip) hσ
    (by simp only [hβσ]) (fun t ht hm => hdisj t ht (by
      obtain ⟨u, hu, hue⟩ := hm
      exact ⟨u, hu, e.injective hue⟩)) hsq ((hH _).2 hsH) _ hU'
  refine ⟨y, hy, ?_⟩
  rw [Ultrafilter.coe_map] at hlim
  have := hlim.comp tendsto_map
  refine this.congr fun z => ?_
  simp only [Function.comp_apply, heap]

/-- **The left side of the second trace in its physical chart** (the reflection of `exists_pos_tendsto_phys`): for
`β` from `x₂ < x₁` stopped at `q` with interior tip `β(q) = α(σ)`, along every approach to the non-tip point
`β(s) ∈ ℍ` from the joint unbounded domain, `f_q(· − x₂)` has a negative limit. -/
theorem exists_neg_tendsto_phys {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} (hp₁ : IsPathGood α ζ₁ x₁)
    (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁) {W : ℝ≥0 → ℝ}
    (hg : IsGeneratingTrace W ζ₂ (fun t => β t - x₂)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ₂})
    (hW0 : W 0 = 0) {q σ : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ₂) (htip : β q ∈ H) (hσ : (σ : ℝ≥0∞) ≤ ζ₁)
    (hασ : α σ = β q) (hdisj : ∀ t < σ, α t ∉ β '' Icc 0 q) {s : ℝ≥0} (hsq : s < q) (hsH : β s ∈ H)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (β '' Icc 0 q ∪ α '' Icc 0 σ)] (β s)) :
    ∃ y : ℝ, y < 0 ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x₂)) U (𝓝 (y : ℂ)) := by
  set R := LP.reflectHomeo with hR
  have hRap : ∀ z, R z = LP.reflectC z := fun z => rfl
  have hRH : ∀ z, R z ∈ H ↔ z ∈ H := fun z => LP.reflectC_mem_H_iff
  have hg' : IsGeneratingTrace (-W) ζ₂ (fun t => LP.reflectC (β t) - ((-x₂ : ℝ) : ℂ)) := by
    have h := LP.isGeneratingTrace_reflect hg
    have e₁ : (fun t => LP.reflectC (β t - x₂)) = fun t => LP.reflectC (β t) - ((-x₂ : ℝ) : ℂ) := by
      funext t; rw [LP.reflectC_sub, LP.reflectC_ofReal]
    rwa [e₁] at h
  have himA : (fun t => LP.reflectC (β t)) '' Icc 0 q = R '' (β '' Icc 0 q) := by rw [image_image]; rfl
  have himB : (fun t => LP.reflectC (α t)) '' Icc 0 σ = R '' (α '' Icc 0 σ) := by rw [image_image]; rfl
  have hU' : ((U.map R : Ultrafilter ℂ) : Filter ℂ) ≤ 𝓝[H \ fillH ((fun t => LP.reflectC (β t)) '' Icc 0 q ∪
      (fun t => LP.reflectC (α t)) '' Icc 0 σ)] (LP.reflectC (β s)) := by
    rw [Ultrafilter.coe_map, himA, himB, ← image_union, fillH_image_homeomorph R hRH ?_,
      ← image_H_diff_homeomorph R hRH, ← hRap, ← R.isEmbedding.map_nhdsWithin_eq]
    · exact map_mono hU
    · intro S; exact LP.isBounded_reflectC_image_iff
  obtain ⟨y, hy, hlim⟩ := exists_pos_tendsto_phys hp₂.reflect hp₁.reflect (by linarith) hg' hWc.neg
    (by simp [hW0]) hq (LP.reflectC_mem_H_iff.2 htip) hσ (by simp only [hασ])
    (fun t ht hm => hdisj t ht (by
      obtain ⟨u, hu, hue⟩ := hm
      exact ⟨u, hu, LP.reflectC_injective hue⟩)) hsq (LP.reflectC_mem_H_iff.2 hsH) _ hU'
  refine ⟨-y, by linarith, ?_⟩
  rw [Ultrafilter.coe_map] at hlim
  have h1 := (LP.continuous_reflectC.tendsto _).comp (hlim.comp tendsto_map)
  rw [LP.reflectC_ofReal] at h1
  refine h1.congr fun z => ?_
  simp only [Function.comp_apply, hRap]
  have e₂ : LP.reflectC z - ((-x₂ : ℝ) : ℂ) = LP.reflectC (z - x₂) := by
    rw [LP.reflectC_sub, LP.reflectC_ofReal]
  have e₃ : (fun r : ℝ => (-W) r.toNNReal) = -(fun r : ℝ => W r.toNNReal) := rfl
  rw [e₂, e₃, LP.fwdMap_neg _ (NNReal.coe_nonneg q), LP.reflectC_reflectC]

end ReverseArc

end Sec7

end InteractingSLE

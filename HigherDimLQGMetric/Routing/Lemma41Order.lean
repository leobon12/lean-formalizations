import HigherDimLQGMetric.Routing.Lemma41Star

/-! An injective path contains an injective subarc in one of its two natural orders. -/

set_option autoImplicit false

noncomputable section
open Set Topology
namespace HigherDimLQGMetric

theorem lemma41_arc_time_lift {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X}
    (P : Path x y) (hPi : Function.Injective P)
    (σ : ℝ → X) (hσc : ContinuousOn σ (Icc 0 1))
    (hσrange : ∀ r ∈ Icc (0 : ℝ) 1, σ r ∈ Set.range P) :
    ∃ f : Icc (0 : ℝ) 1 → unitInterval, Continuous f ∧ ∀ r, P (f r) = σ r := by
  let g : unitInterval → Set.range P := fun r => ⟨P r, ⟨r, rfl⟩⟩
  have hgi : Function.Injective g := fun _ _ h => hPi (congrArg Subtype.val h)
  have hgs : Function.Surjective g := by
    rintro ⟨z, ⟨r, hr⟩⟩
    exact ⟨r, Subtype.ext hr⟩
  let e : unitInterval ≃ Set.range P := Equiv.ofBijective g ⟨hgi, hgs⟩
  have hgc : Continuous g := P.continuous.subtype_mk _
  let H : unitInterval ≃ₜ Set.range P := Continuous.homeoOfEquivCompactToT2 (f := e) hgc
  let gσ : Icc (0 : ℝ) 1 → Set.range P := fun r => ⟨σ r, hσrange r r.property⟩
  have hgσc : Continuous gσ := (continuousOn_iff_continuous_domRestrict.mp hσc).subtype_mk _
  refine ⟨H.symm ∘ gσ, H.symm.continuous.comp hgσc, ?_⟩
  intro r
  change (H (H.symm (gσ r))).val = σ r
  simpa only [gσ] using congrArg Subtype.val (H.apply_symm_apply (gσ r))

theorem lemma41_arc_order {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X}
    (P : Path x y) (hPi : Function.Injective P)
    (σ : ℝ → X) (hσc : ContinuousOn σ (Icc 0 1))
    (hσi : InjOn σ (Icc 0 1))
    (hσrange : ∀ r ∈ Icc (0 : ℝ) 1, σ r ∈ Set.range P) :
    ∃ f : Icc (0 : ℝ) 1 → unitInterval, Continuous f ∧
      (StrictMono f ∨ StrictAnti f) ∧ ∀ r, P (f r) = σ r := by
  obtain ⟨f, hfc, hPf⟩ := lemma41_arc_time_lift P hPi σ hσc hσrange
  let F : ℝ → ℝ := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then f ⟨r, hr⟩ else 0
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp hfc using 1
    ext r
    change F r = (f r).val
    simp only [F, dite_eq_left r.property]
  have hFi : InjOn F (Icc (0 : ℝ) 1) := by
    intro a ha b hb hab
    have hfEq : f ⟨a, ha⟩ = f ⟨b, hb⟩ := by
      apply Subtype.ext
      simpa only [F, dite_eq_left ha, dite_eq_left hb] using hab
    exact hσi ha hb (by rw [← hPf ⟨a, ha⟩, ← hPf ⟨b, hb⟩, hfEq])
  have hmon := hFc.strictMonoOn_of_injOn_Icc' (by norm_num : (0 : ℝ) ≤ 1) hFi
  refine ⟨f, hfc, ?_, hPf⟩
  rcases hmon with hm | ha
  · left
    intro a b hab
    have h := hm a.property b.property hab
    simpa only [F, dite_eq_left a.property, dite_eq_left b.property, Subtype.coe_lt_coe] using h
  · right
    intro a b hab
    have h := ha a.property b.property hab
    simpa only [F, dite_eq_left a.property, dite_eq_left b.property, Subtype.coe_lt_coe] using h

/-- Every point of an arc contained in an injective curve has a continuous, monotone time
coordinate on that curve. -/
theorem lemma41_arc_order_on_interval {X : Type*} [TopologicalSpace X] [T2Space X]
    {ℓ : ℝ} (Q : ℝ → X) (hQc : ContinuousOn Q (Icc 0 ℓ))
    (hQi : InjOn Q (Icc 0 ℓ)) (σ : ℝ → X)
    (hσc : ContinuousOn σ (Icc 0 1)) (hσi : InjOn σ (Icc 0 1))
    (hσrange : σ '' Icc (0 : ℝ) 1 ⊆ Q '' Icc 0 ℓ) :
    ∃ f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) ℓ,
      Continuous f ∧ (StrictMono f ∨ StrictAnti f) ∧
        ∀ r, Q (f r) = σ r := by
  let g : Icc (0 : ℝ) ℓ → X := fun r => Q r
  have hgc : Continuous g := continuousOn_iff_continuous_domRestrict.mp hQc
  have hgi : Function.Injective g := fun a b h => Subtype.ext (hQi a.property b.property h)
  let j : Icc (0 : ℝ) ℓ → Set.range g := fun r => ⟨g r, ⟨r, rfl⟩⟩
  have hji : Function.Injective j := fun _ _ h => hgi (congrArg Subtype.val h)
  have hjs : Function.Surjective j := by
    rintro ⟨z, ⟨r, hr⟩⟩
    exact ⟨r, Subtype.ext hr⟩
  let e : Icc (0 : ℝ) ℓ ≃ Set.range g := Equiv.ofBijective j ⟨hji, hjs⟩
  have hjc : Continuous j := hgc.subtype_mk _
  let H : Icc (0 : ℝ) ℓ ≃ₜ Set.range g :=
    Continuous.homeoOfEquivCompactToT2 (f := e) hjc
  let gσ : Icc (0 : ℝ) 1 → Set.range g := fun r => by
    refine ⟨σ r, ?_⟩
    obtain ⟨u, hu, heq⟩ := hσrange ⟨r, r.property, rfl⟩
    exact ⟨⟨u, hu⟩, heq⟩
  have hgσc : Continuous gσ :=
    (continuousOn_iff_continuous_domRestrict.mp hσc).subtype_mk _
  let f := H.symm ∘ gσ
  have hfc : Continuous f := H.symm.continuous.comp hgσc
  have hQf : ∀ r, Q (f r) = σ r := by
    intro r
    change (H (H.symm (gσ r))).val = σ r
    simpa only [gσ] using congrArg Subtype.val (H.apply_symm_apply (gσ r))
  let F : ℝ → ℝ := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then f ⟨r, hr⟩ else 0
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp hfc using 1
    ext r
    change F r = (f r).val
    simp only [F, dite_eq_left r.property]
  have hFi : InjOn F (Icc (0 : ℝ) 1) := by
    intro a ha b hb hab
    have hfEq : f ⟨a, ha⟩ = f ⟨b, hb⟩ := by
      apply Subtype.ext
      simpa only [F, dite_eq_left ha, dite_eq_left hb] using hab
    exact hσi ha hb (by rw [← hQf ⟨a, ha⟩, ← hQf ⟨b, hb⟩, hfEq])
  have hmon := hFc.strictMonoOn_of_injOn_Icc' (by norm_num : (0 : ℝ) ≤ 1) hFi
  refine ⟨f, hfc, ?_, hQf⟩
  rcases hmon with hm | ha
  · left
    intro a b hab
    have h := hm a.property b.property hab
    simpa only [F, dite_eq_left a.property, dite_eq_left b.property, Subtype.coe_lt_coe] using h
  · right
    intro a b hab
    have h := ha a.property b.property hab
    simpa only [F, dite_eq_left a.property, dite_eq_left b.property, Subtype.coe_lt_coe] using h

end HigherDimLQGMetric

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Aux. lemma 54: extending a stopped coupling by one disintegration of a fixed reference

Packet PROVE-SEC7-A2 (specification §7.1, Aux. lemma 54 and its proof, p. 246).

"Disintegrate the fixed reference law once, obtaining a regular conditional law of its entire future
driving history given `(Ĥ_S, Ĥ_S)`. Use that kernel at `(H_S, H_S)` to sample the new future. … This is a
single regular conditional probability on standard Borel spaces. There is no choice of a separate
coupling for every possible random current force configuration."

The probabilistic core (`aux54_exists_extension`): let `Rr` (the recorded stopped history and the mapped
active field) and `Fr` (the future, standard Borel) be defined on a reference probability space, and let
`R` be defined on another probability space with the same law as `Rr`. With `κ₀ = law(Fr | Rr)` the
extension `P ⊗ κ₀(R(·))` on `Ω × C`
* keeps the original space: its first marginal is `P` (the whole initial field and every germ are
  preserved);
* reproduces the reference: `(R, future)` has the joint law of `(Rr, Fr)`;
* samples only from `R` (`map_prodMk_compProd_comap`): for every further observable `G` of the original
  space, `(G, R, future)` has law `law(G, R) ⊗ κ₀(R)`, i.e. the future is conditionally independent of
  `G` given `R` ("The new future kernel does not read the old germ").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace InteractingSLE

namespace Sec7

/-- Pushing `P ⊗ κ(S(·))` forward by `S × id` gives `law(S) ⊗ κ`. -/
theorem map_prodMk_compProd_comap {Ω α C : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]
    [MeasurableSpace C] {P : Measure Ω} [IsFiniteMeasure P] {S : Ω → α} (hS : Measurable S)
    (κ : Kernel α C) [IsMarkovKernel κ] :
    (P ⊗ₘ κ.comap S hS).map (fun p => (S p.1, p.2)) = (P.map S) ⊗ₘ κ := by
  have hm : Measurable fun p : Ω × C => (S p.1, p.2) := (hS.comp measurable_fst).prodMk measurable_snd
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    have hpre : (fun p : Ω × C => (S p.1, p.2)) ⁻¹' (s ×ˢ t) = (S ⁻¹' s) ×ˢ t := by ext; simp
    rw [Measure.map_apply hm (hs.prod ht), hpre, Measure.compProd_apply_prod (hS hs) ht,
      Measure.compProd_apply_prod hs ht, setLIntegral_map hs (κ.measurable_coe ht) hS]
    rfl
  · rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ, Measure.compProd_apply_univ,
      Measure.compProd_apply_univ, Measure.map_apply hS MeasurableSet.univ, preimage_univ]

/-- **Aux. lemma 54, probabilistic core** (p. 246): extension of a coupling by one regular conditional
law of a fixed reference. `κ₀ = law(Fr | Rr)` is a Markov kernel (one disintegration of the reference);
the extended measure `P ⊗ κ₀(R(·))` on `Ω × C` has first marginal `P`, and `(R, future)` has the
reference joint law `law(Rr, Fr)`. -/
theorem aux54_exists_extension {α C : Type*} [MeasurableSpace α] [MeasurableSpace C]
    [StandardBorelSpace C] [Nonempty C]
    {Ωr : Type*} {mΩr : MeasurableSpace Ωr} {Pr : Measure Ωr} [IsProbabilityMeasure Pr]
    {Rr : Ωr → α} {Fr : Ωr → C} (hRr : Measurable Rr) (hFr : Measurable Fr)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {R : Ω → α} (hR : Measurable R) (hlaw : P.map R = Pr.map Rr) :
    ∃ κ₀ : Kernel α C, IsMarkovKernel κ₀ ∧
      (P ⊗ₘ κ₀.comap R hR).map Prod.fst = P ∧
      (P ⊗ₘ κ₀.comap R hR).map (fun p => (R p.1, p.2)) = Pr.map (fun ω => (Rr ω, Fr ω)) := by
  refine ⟨condDistrib Fr Rr Pr, inferInstance, ?_, ?_⟩
  · exact Measure.fst_compProd _ _
  · rw [map_prodMk_compProd_comap hR, hlaw,
      compProd_map_condDistrib hRr.aemeasurable hFr.aemeasurable]

/-- **The extension samples only from the record** (Aux. lemma 54, p. 246: "The new future kernel does not
read the old germ"). For every observable `G` of the original space, `(G, R, future)` has law
`law(G, R) ⊗ κ₀(R)`: conditionally on `(G, R)`, the future has law `κ₀(R)`. -/
theorem map_compProd_comap_eq_of_obs {Ω α β C : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace C] {P : Measure Ω} [IsFiniteMeasure P] {R : Ω → α}
    (hR : Measurable R) (κ₀ : Kernel α C) [IsMarkovKernel κ₀] {G : Ω → β} (hG : Measurable G) :
    (P ⊗ₘ κ₀.comap R hR).map (fun p => ((G p.1, R p.1), p.2)) =
      (P.map fun ω => (G ω, R ω)) ⊗ₘ κ₀.comap Prod.snd measurable_snd := by
  have h : κ₀.comap R hR = (κ₀.comap Prod.snd measurable_snd).comap (fun ω => (G ω, R ω))
      (hG.prodMk hR) := rfl
  rw [h]
  exact map_prodMk_compProd_comap (S := fun ω => (G ω, R ω)) (hG.prodMk hR) _

end Sec7

end InteractingSLE

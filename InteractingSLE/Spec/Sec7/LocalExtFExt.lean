/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtFHist
import InteractingSLE.Spec.Sec7.TwoForceMainExtend

/-!
# Aux. lemma 54: the extension by one disintegration, with the record read from the reference

Packet PROVE-LOCEXT-F. The proof of Aux. lemma 54 (specification p. 246) samples the future of the stopped coupling from
one regular conditional law of a fixed reference given its record ("Disintegrate the fixed reference law once, obtaining
a regular conditional law of its entire future driving history given `(Ĥ_S, Ĥ_S)`. Use that kernel at `(H_S, H_S)` to
sample the new future"). When the reference is encoded by a random element `F̂` of a standard Borel space and its record
is a measurable function `π(F̂)` of the encoding, the extension `E = Q ⊗ κ₀(R(·))`, `κ₀ = law(F̂ | π(F̂))`, has
(`exists_recordExtension`):

* first marginal `Q` (the whole original space is preserved);
* second marginal the law of the reference encoding;
* **the record of the sample is the record of the original point**, `E`-almost surely (`π(p.2) = R(p.1)`): the
  sampled reference agrees with the stopped coupling on everything the record contains;
* for every observable `G` of the original space, `(G, R, sample)` has the law `law(G, R) ⊗ κ₀(R)` ("The new future
  kernel does not read the old germ").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace InteractingSLE

namespace LocalExt

open Sec7

/-- **Aux. lemma 54, the extension by one disintegration of an encoded reference whose record is read from its
encoding.** -/
theorem exists_recordExtension {α C : Type*} [MeasurableSpace α] [MeasurableEq α] [MeasurableSpace C]
    [StandardBorelSpace C] [Nonempty C] {Ωr : Type*} {mΩr : MeasurableSpace Ωr} {Pr : Measure Ωr}
    [IsProbabilityMeasure Pr] {Fr : Ωr → C} (hFr : Measurable Fr) {π : C → α} (hπ : Measurable π)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Ω → α}
    (hR : Measurable R) (hlaw : Q.map R = Pr.map fun ω => π (Fr ω)) :
    ∃ κ₀ : Kernel α C, IsMarkovKernel κ₀ ∧
      (Q ⊗ₘ κ₀.comap R hR).map Prod.fst = Q ∧
      (Q ⊗ₘ κ₀.comap R hR).map Prod.snd = Pr.map Fr ∧
      (∀ᵐ p ∂(Q ⊗ₘ κ₀.comap R hR), π p.2 = R p.1) ∧
      ∀ {β : Type*} [MeasurableSpace β] {G : Ω → β}, Measurable G →
        (Q ⊗ₘ κ₀.comap R hR).map (fun p => ((G p.1, R p.1), p.2)) =
          (Q.map fun ω => (G ω, R ω)) ⊗ₘ κ₀.comap Prod.snd measurable_snd := by
  obtain ⟨κ₀, hκ₀, hfst, hpair⟩ := aux54_exists_extension (Rr := fun ω => π (Fr ω)) (hπ.comp hFr) hFr hR hlaw
  have hRs : Measurable fun p : Ω × C => (R p.1, p.2) := (hR.comp measurable_fst).prodMk measurable_snd
  have hpr : Measurable fun ω => (π (Fr ω), Fr ω) := (hπ.comp hFr).prodMk hFr
  refine ⟨κ₀, hκ₀, hfst, ?_, ?_, fun hG => map_compProd_comap_eq_of_obs hR κ₀ hG⟩
  · have e : (Prod.snd : Ω × C → C) = Prod.snd ∘ fun p : Ω × C => (R p.1, p.2) := rfl
    rw [e, ← Measure.map_map measurable_snd hRs, hpair, Measure.map_map measurable_snd hpr]
    rfl
  · have hD : MeasurableSet {q : α × C | π q.2 = q.1} := measurableSet_eq_fun (hπ.comp measurable_snd) measurable_fst
    have h1 : ∀ᵐ q ∂((Q ⊗ₘ κ₀.comap R hR).map fun p => (R p.1, p.2)), π q.2 = q.1 := by
      rw [hpair, ae_map_iff (p := fun q : α × C => π q.2 = q.1) hpr.aemeasurable hD]
      exact Eventually.of_forall fun ω => rfl
    exact (ae_map_iff (p := fun q : α × C => π q.2 = q.1) hRs.aemeasurable hD).1 h1

end LocalExt

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Ref
import InteractingSLE.Spec.Restart.StoppedCont

/-!
# Aux. lemma 54 for general words, part 4: the record law and the extension

Packet PROVE-AUX54. Specification p. 246: "The pair `(𝓗_S, H_S)` has exactly the same joint law in the stopped coupling
and in the fixed full reference coupling … Disintegrate the fixed reference law once, obtaining a regular conditional
law of its entire future driving history given `(𝓗_S, H_S)`. Use that kernel at `(𝓗_S, H_S)` to sample the new future."

* **`map_recOfA_eq_reference`** (the record law): for a coupling through a Galmarino stop `V = R(history)` that is
  regular at the stop, and a full coupling of the word stopped at `V₀ = R(its history) ∧ ζ₀`, the records (history
  killed at the stop, field off the recorded hull) have the same law: (U) (`stoppedHistLawStatement_of_continuation`
  with the landed continuation) and the two kernels at the stop (`hasSetKernel_stoppedCoupling`,
  `hasSetKernel_reference`);
* `IsRecExt`: a **record extension** — a measure on `Ω × Ω₀` with marginals `P`, `P₀`, on which the histories agree and
  the fields off the hull agree test function by test function, of the form `P ⊗ κ₀(record)`;
* **`exists_isRecExt`**: the record extension exists (`Sec7.aux54_exists_extension`, one disintegration);
* `IsRecExt.ae_state_eq`: on a record extension the driving states agree before the stop.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF

variable {nL nR : ℕ}

/-- The record space: a history and the field off its hull. -/
abbrev RecSpace (nL nR : ℕ) : Type := HistorySpace nL nR × (TestOn upperHalfPlaneOpens → ℝ)

/-! ### The record law -/

/-- **Aux. lemma 54's record law** (p. 246): a coupling through a Galmarino stop, regular at the stop, and a full
coupling of the word stopped at its rule stop have the same law of records. -/
theorem map_recOfA_eq_reference {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R)
    (hRg : IsHistGalmarino R) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    (hV : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) (hreg : IsRegularStop ρL ρR P W VL VR V)
    {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hC₀ : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀) :
    P.map (fun ω => recOfA (recHull ρL ρR xL xR) (h ω) (killedHistory W VL VR V ω)) =
      P₀.map (fun ω₀ => recOfA (recHull ρL ρR xL xR) (h₀ ω₀)
        (killedHistory W₀ VL₀ VR₀ (ruleStop R W₀ VL₀ VR₀ ζ₀) ω₀)) := by
  have hU := stoppedHistLawStatement_of_continuation hκ (StoppedCont.stoppedContinuationStatement hκ)
    xL xR ρL ρR hF R hRm hRg P 𝓕 W VL VR B V h hSC hV P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hC₀.1
  have hk₁ := hasSetKernel_stoppedCoupling hSC hreg
  have hk₂ := hasSetKernel_reference hκ hC₀ hRm hRg
  obtain ⟨-, -, hh, -, hX, -⟩ := hSC
  have hY₁ : Measurable (killedHistory W VL VR V) := measurable_killedHistory hX
  have hX₀ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC₀.1
  have hY₂ : Measurable (killedHistory W₀ VL₀ VR₀ (ruleStop R W₀ VL₀ VR₀ ζ₀)) :=
    measurable_killedHistory (isMeasurableKilledDriving_of_le hX₀
      ((hRm.comp (measurable_killedHistory hX₀)).min (measurable_lifetime hX₀)) (ruleStop_le R))
  exact map_recOfA_eq_of_hasSetKernel (isMeasHull_recHull ρL ρR xL xR) hY₁ hY₂ hh hC₀.2.1
    (measurable_recK κ ρL ρR xL xR) hk₁ hk₂ hU

/-! ### Record extensions -/

section RecExt

variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]

/-- **A record extension** (Aux. lemma 54: "Use that kernel at `(𝓗_S, H_S)` to sample the new future"): a measure `E`
on `Ω × Ω₀` with marginals `P` and `P₀`, on which the recorded histories agree and the fields off the recorded hull
agree test function by test function, and which samples the second factor from the first only through the record. -/
def IsRecExt (P : Measure Ω) (P₀ : Measure Ω₀) (A : HistorySpace nL nR → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) (X : Ω → HistorySpace nL nR) (h₀ : Ω₀ → DistOn upperHalfPlaneOpens)
    (X₀ : Ω₀ → HistorySpace nL nR) (E : Measure (Ω × Ω₀)) : Prop :=
  E.map Prod.fst = P ∧ E.map Prod.snd = P₀ ∧ (∀ᵐ p ∂E, X p.1 = X₀ p.2) ∧
    (∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E, fieldRecA A (h p.1) (X p.1) ψ = fieldRecA A (h₀ p.2) (X₀ p.2) ψ) ∧
    ∃ (hm : Measurable fun ω => recOfA A (h ω) (X ω)) (κ₀ : Kernel (RecSpace nL nR) Ω₀), IsMarkovKernel κ₀ ∧
      E = P ⊗ₘ κ₀.comap (fun ω => recOfA A (h ω) (X ω)) hm

/-- **The record extension exists** (one disintegration of the reference, `Sec7.aux54_exists_extension`). -/
theorem exists_isRecExt [StandardBorelSpace Ω₀] {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {A : HistorySpace nL nR → Set ℂ} (hA : IsMeasHull A)
    {h : Ω → DistOn upperHalfPlaneOpens} {X : Ω → HistorySpace nL nR} (hh : Measurable h) (hX : Measurable X)
    {h₀ : Ω₀ → DistOn upperHalfPlaneOpens} {X₀ : Ω₀ → HistorySpace nL nR} (hh₀ : Measurable h₀)
    (hX₀ : Measurable X₀)
    (hlaw : P.map (fun ω => recOfA A (h ω) (X ω)) = P₀.map (fun ω₀ => recOfA A (h₀ ω₀) (X₀ ω₀))) :
    ∃ E : Measure (Ω × Ω₀), IsProbabilityMeasure E ∧ IsRecExt P P₀ A h X h₀ X₀ E := by
  have : Nonempty Ω₀ := nonempty_of_isProbabilityMeasure P₀
  have hrm : Measurable fun ω => recOfA A (h ω) (X ω) := (measurable_recOfA hA).comp (hh.prodMk hX)
  have hr₀m : Measurable fun ω₀ => recOfA A (h₀ ω₀) (X₀ ω₀) := (measurable_recOfA hA).comp (hh₀.prodMk hX₀)
  obtain ⟨κ₀, hκ₀, hfst, hpair⟩ := Sec7.aux54_exists_extension (Fr := id) hr₀m measurable_id hrm hlaw
  set E : Measure (Ω × Ω₀) := P ⊗ₘ κ₀.comap (fun ω => recOfA A (h ω) (X ω)) hrm with hE
  have hpm : Measurable fun p : Ω × Ω₀ => (recOfA A (h p.1) (X p.1), p.2) :=
    (hrm.comp measurable_fst).prodMk measurable_snd
  have hsnd : E.map Prod.snd = P₀ := by
    have e : (Prod.snd : Ω × Ω₀ → Ω₀) = Prod.snd ∘ fun p : Ω × Ω₀ => (recOfA A (h p.1) (X p.1), p.2) := rfl
    rw [e, ← Measure.map_map measurable_snd hpm, hpair, Measure.map_map measurable_snd (hr₀m.prodMk measurable_id)]
    exact Measure.map_id
  -- an almost sure property of the pair `(record, ω₀)` under the reference law transfers to `E`
  have htr : ∀ {D : Set (RecSpace nL nR × Ω₀)}, MeasurableSet D →
      (∀ ω₀, (recOfA A (h₀ ω₀) (X₀ ω₀), ω₀) ∈ D) → ∀ᵐ p ∂E, (recOfA A (h p.1) (X p.1), p.2) ∈ D := by
    intro D hD hall
    have h1 : ∀ᵐ q ∂(P₀.map fun ω => (recOfA A (h₀ ω) (X₀ ω), id ω)), q ∈ D :=
      (ae_map_iff (hr₀m.prodMk measurable_id).aemeasurable hD).2 (Eventually.of_forall hall)
    rw [← hpair] at h1
    exact (ae_map_iff hpm.aemeasurable hD).1 h1
  have hkh : ∀ᵐ p ∂E, X p.1 = X₀ p.2 :=
    htr (D := {q | q.1.1 = X₀ q.2}) (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
      (hX₀.comp measurable_snd)) fun ω₀ => rfl
  have hfr : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E,
      fieldRecA A (h p.1) (X p.1) ψ = fieldRecA A (h₀ p.2) (X₀ p.2) ψ := fun ψ =>
    htr (D := {q | q.1.2 ψ = fieldRecA A (h₀ q.2) (X₀ q.2) ψ})
      (measurableSet_eq_fun ((measurable_pi_apply ψ).comp (measurable_snd.comp measurable_fst))
        ((measurable_fieldRecA_apply hA ψ).comp ((hh₀.comp measurable_snd).prodMk (hX₀.comp measurable_snd))))
      fun ω₀ => rfl
  exact ⟨E, inferInstance, hfst, hsnd, hkh, hfr, hrm, κ₀, hκ₀, rfl⟩

end RecExt

end Aux54

end Restart

end InteractingSLE

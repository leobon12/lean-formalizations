/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstGluedPieces

/-! # Seed collars measured by the retained history

The collar selection uses only the recorded inverse chart and counterflow
boundary. In particular its events factor through the history without
requiring the future contact time to be history measurable.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GCont
open Aux61GInst Aux61FibData Aux61Restart
open WangWu (negInv)

/-- A continuous path starting outside a closed obstacle has positive first
contact time. This includes the case of no contact. -/
theorem hitTime_pos_of_notMem {X : Type*} {ρ : X → ℝ≥0 → ℂ}
    {C : X → Set ℂ} {x : X} (hc : Continuous (ρ x)) (hC : IsClosed (C x))
    (hstart : ρ x 0 ∉ C x) : 0 < hitTime ρ C x := by
  by_contra hn
  obtain ⟨u, hu, hmem⟩ := (hitTime_le_iff hc hC 0).1 (le_of_not_gt hn)
  have hu0 : u = 0 := by
    apply le_antisymm _ (zero_le : (0 : ℝ≥0) ≤ u)
    exact ENNReal.coe_le_coe.1 hu
  exact hstart (hu0 ▸ hmem)

/-- Countable collar pieces are actual preimages of measurable history
events, with exact coverage. No standard Borel assumption is needed. -/
theorem exists_history_seedPieces {X β : Type*} [mβ : MeasurableSpace β]
    (Z : X → β) {E : Set X} (hE : MeasurableSet[mβ.comap Z] E)
    {F : X → ℝ → ℂ} {C : X → Set ℂ}
    (hFm : ∀ a, Measurable[mβ.comap Z] (E.indicator fun x => F x a))
    (hFc : ∀ x ∈ E, Continuous (F x))
    (hCm : ∀ z, Measurable[mβ.comap Z] (E.indicator fun x => infDist z (C x)))
    (hCc : ∀ x ∈ E, IsClosed (C x)) (hCne : ∀ x ∈ E, (C x).Nonempty)
    (hgap : ∀ x ∈ E, ∃ δ > 0, ∀ a : ℝ, |a| < δ → F x a ∉ C x) :
    ∃ B : ℕ × ℕ → Set β, (∀ p, MeasurableSet (B p)) ∧
      E = ⋃ p, Z ⁻¹' B p ∧ (∀ p, Z ⁻¹' B p ⊆ E) ∧
      ∀ p x, Z x ∈ B p → ∀ a : ℝ, |a| ≤ collarRadius p.1 → F x a ∉ C x := by
  obtain ⟨S, hSm, hcov, hsub, hfree⟩ :=
    @exists_measurable_seedPieces X (mβ.comap Z) E hE F C hFm hFc hCm hCc hCne hgap
  choose B hBm hBS using fun p => MeasurableSpace.measurableSet_comap.1 (hSm p)
  refine ⟨B, hBm, ?_, ?_, ?_⟩
  · simpa only [hBS] using hcov
  · intro p
    rw [hBS p]
    exact hsub p
  · intro p x hx
    exact hfree p x ((hBS p) ▸ hx)

/-- The pointwise history inputs for the actual bounded inverse and recorded
counterflow boundary are measurable in the retained sigma algebra. -/
theorem measurable_glued_seed_data {X : Type*} [mX : MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {ℋ : MeasurableSpace X}
    (hE : MeasurableSet[ℋ] E) (hc : @IsMeasChart X ℋ c)
    {W : X → ℝ → ℝ} {β η : X → ℝ → ℂ} {s r : ℝ} (hs0 : 0 ≤ s)
    (hβ : ∀ x ∈ E, IsLoewnerTrace (W x) (β x))
    (hβm : ∀ t, Measurable[ℋ] (fun x => β x t))
    (hη : ∀ x ∈ E, ContinuousOn (η x) (Icc 0 r))
    (hηH : ∀ x ∈ E, MapsTo (η x) (Icc 0 r) Hbar) {b : X → ℂ}
    (hb : ∀ x ∈ E, b x ∈ retainedDomain (negInv '' QuantumZipper.fwdHull (W x) s) (η x) r)
    (hdom : ∀ x ∈ E, ((c x).dom : Set ℂ) =
      restartComponent (negInv '' QuantumZipper.fwdHull (W x) s) (η x) r (b x)) :
    (∀ a : ℝ, Measurable[ℋ] (E.indicator fun x => boundedInverse (c x) (a : ℂ))) ∧
      ∀ z : ℂ, Measurable[ℋ] (E.indicator fun x =>
        infDist z (oldModelBoundary (counterflowRecord (β x) s))) := by
  classical
  have hconf : ∀ x ∈ E, (c x).IsConformal := @IsRestartSpec.conf X mX E c ρ T hs
  have hF : ∀ x ∈ E, EqOn (boundedInverse (c x))
      (QuantumZipper.CA.cayley ∘ (c x).2.1) H ∧ ContinuousOn (boundedInverse (c x)) Hbar := by
    intro x hx
    have hh := boundedInverse_spec_of_traces (hβ x hx) hs0 (hη x hx) (hηH x hx)
      (hb x hx) (hconf x hx) (hdom x hx)
    exact ⟨hh.1, hh.2.1⟩
  refine ⟨fun a => @measurable_boundedInverse_real X ℋ E hE c hc hconf hF a, fun z => ?_⟩
  letI : MeasurableSpace X := ℋ
  have hd : Measurable (fun x : E => infDist z (oldModelBoundary (counterflowRecord (β x.1) s))) :=
    measurable_infDist_oldModelBoundary (β := fun x : E => β x.1) (s := s)
      (fun x => (hβ x x.2).2.1.mono Icc_subset_Ici_self)
      (fun t => (hβm t).comp measurable_subtype_coe) z
  have hzero : Measurable (fun _ : (Eᶜ : Set X) => (0 : ℝ)) := measurable_const
  convert Measurable.dite hd hzero hE using 1
  funext x
  by_cases hx : x ∈ E <;> simp [hx]

end InteractingSLE.Sec5.Aux61GCont

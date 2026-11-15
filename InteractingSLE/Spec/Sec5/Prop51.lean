/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Mono

/-!
# Proposition 5.1: the passage from a dense set of counterflow times to the whole counterflow

Packet PROVE-SEC5-D. The proof of Proposition 5.1 (specification p. 135) fixes an `η'`-stopping time `τ'` and shows
that `η'(τ')` lies to the right of `η_θ`; the whole statement then follows from a countable dense set of times and the
continuity of `η'` (the same final step as in Proposition 4.9, p. 120: "The result now follows by taking a countable
dense collection of stopping times `τ'` (e.g., the positive rationals) and invoking the almost sure continuity of
`η'`"). This file proves that final step on the carriers of `Spec/Sec5/Carrier.lean`:

* `disjoint_stripCounterflowRange_of_dense` (pathwise): if `S` (a strict side of the flow-line range) is open, the
  trace `γ` is continuous before its lifetime and avoids `−1` (the strip end `+∞`, where `M_q⁻¹` is singular), and the
  points `M_q⁻¹(γ(r))` at the times `r` of a dense set `D` avoid `S`, then the whole counterflow range avoids `S`;
* `ae_disjoint_stripCounterflowRange_of_countable`, `ae_liesRightOf_liesLeftOf_of_countable` (almost sure, `D`
  countable): the statement at each deterministic
  time of `D` implies the statement for the whole counterflow (and likewise for `LiesLeftOf`).

The per-time statement is the substance of the proof of Proposition 5.1 (Aux. lemma 22 for the conditional field after
mapping out `K'_{τ'}`, Lemma 5.4, and the planar no-wrap argument; see the handoff `PROVE-SEC5-D.md`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec5

open Sec4 (stripCounterflowChart)

/-- `M_q⁻¹` is continuous away from `−1`. -/
theorem continuousAt_stripCounterflowChart_inv (q : ℝ) {z : ℂ} (hz : z ≠ -1) :
    ContinuousAt (fun z : ℂ => (stripCounterflowChart q).2.1 z) z := by
  have hz1 : z + 1 ≠ 0 := fun h => hz (eq_neg_of_add_eq_zero_left h)
  simp only [Sec4.stripCounterflowChart_inv]
  exact continuousAt_const.mul ((continuousAt_id.add continuousAt_const).inv₀ hz1)

/-- **The final step of Proposition 5.1, pathwise.** Let `S` be open (in the application, the strict left or right side
of the flow-line range), the counterflow trace `γ` (chart `M_q`) be continuous before its lifetime `ζ'` and avoid `−1`
there, and let `D ⊆ ℝ≥0` be dense. If `M_q⁻¹(γ(r)) ∉ S` at every `r ∈ D` before `ζ'`, then the whole counterflow range
`M_q⁻¹(γ([0, ζ')))` is disjoint from `S`. -/
theorem disjoint_stripCounterflowRange_of_dense {q : ℝ} {γ : ℝ≥0 → ℂ} {ζ' : ℝ≥0∞}
    {S : Set ℂ} (hS : IsOpen S) (hγ : ContinuousOn γ {t | (t : ℝ≥0∞) < ζ'})
    (hne : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' → γ t ≠ -1) {D : Set ℝ≥0} (hD : Dense D)
    (hpt : ∀ r ∈ D, (r : ℝ≥0∞) < ζ' → (stripCounterflowChart q).2.1 (γ r) ∉ S) :
    Disjoint (stripCounterflowRange q γ ζ') S := by
  rw [Set.disjoint_left]
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ hmem
  have hO : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ'} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ContinuousAt (fun s => (stripCounterflowChart q).2.1 (γ s)) t :=
    (continuousAt_stripCounterflowChart_inv q (hne t ht)).comp (hγ.continuousAt (hO.mem_nhds ht))
  have hU : {s | (stripCounterflowChart q).2.1 (γ s) ∈ S} ∩ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ'} ∈ 𝓝 t :=
    inter_mem (hcont.preimage_mem_nhds (hS.mem_nhds hmem)) (hO.mem_nhds ht)
  obtain ⟨U, hUsub, hUo, htU⟩ := mem_nhds_iff.1 hU
  obtain ⟨r, hrD, hrU⟩ := hD.exists_mem_open hUo ⟨t, htU⟩
  exact hpt r hrD (hUsub hrU).2 (hUsub hrU).1

/-- **The final step of Proposition 5.1, almost surely** (a countable dense set `D` of deterministic counterflow
times). If almost surely the strict side `S ω` (the left side of the flow line in the application) is open and the
trace is continuous and avoids `−1` before its lifetime, and at each `r ∈ D` almost surely `M_q⁻¹(γ(r)) ∉ S` before
the lifetime, then almost surely the whole counterflow range is disjoint from `S`. -/
theorem ae_disjoint_stripCounterflowRange_of_countable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {q : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {ζ' : Ω → ℝ≥0∞} {S : Ω → Set ℂ} {D : Set ℝ≥0} (hDc : D.Countable) (hD : Dense D)
    (hreg : ∀ᵐ ω ∂P, IsOpen (S ω) ∧ ContinuousOn (γ ω) {t | (t : ℝ≥0∞) < ζ' ω} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω → γ ω t ≠ -1)
    (hpt : ∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω → (stripCounterflowChart q).2.1 (γ ω r) ∉ S ω) :
    ∀ᵐ ω ∂P, Disjoint (stripCounterflowRange q (γ ω) (ζ' ω)) (S ω) := by
  have : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ r : D, ((r : ℝ≥0) : ℝ≥0∞) < ζ' ω →
      (stripCounterflowChart q).2.1 (γ ω r) ∉ S ω := ae_all_iff.2 fun r => hpt r r.2
  filter_upwards [hreg, hall] with ω ⟨hS, hγ, hne⟩ hω
  exact disjoint_stripCounterflowRange_of_dense hS hγ hne hD fun r hr hrζ => hω ⟨r, hr⟩ hrζ

/-- The two conclusions of Proposition 5.1 from their statements at the times of a countable dense set: `LiesRightOf`
(`S = stripLeftSide`) and `LiesLeftOf` (`S = stripRightSide`), for a closed flow-line range. -/
theorem ae_liesRightOf_liesLeftOf_of_countable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {q : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {ζ' : Ω → ℝ≥0∞} {A : Ω → Set ℂ} {D : Set ℝ≥0} (hDc : D.Countable) (hD : Dense D)
    (hreg : ∀ᵐ ω ∂P, IsClosed (A ω) ∧ ContinuousOn (γ ω) {t | (t : ℝ≥0∞) < ζ' ω} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω → γ ω t ≠ -1) :
    ((∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω → (stripCounterflowChart q).2.1 (γ ω r) ∉ stripLeftSide (A ω)) →
        ∀ᵐ ω ∂P, LiesRightOf (stripCounterflowRange q (γ ω) (ζ' ω)) (A ω)) ∧
      ((∀ r ∈ D, ∀ᵐ ω ∂P, (r : ℝ≥0∞) < ζ' ω →
          (stripCounterflowChart q).2.1 (γ ω r) ∉ stripRightSide (A ω)) →
        ∀ᵐ ω ∂P, LiesLeftOf (stripCounterflowRange q (γ ω) (ζ' ω)) (A ω)) := by
  refine ⟨fun hpt => ?_, fun hpt => ?_⟩
  · refine ae_disjoint_stripCounterflowRange_of_countable hDc hD ?_ hpt
    filter_upwards [hreg] with ω ⟨hA, hγ, hne⟩ using ⟨isOpen_stripLeftSide hA, hγ, hne⟩
  · refine ae_disjoint_stripCounterflowRange_of_countable hDc hD ?_ hpt
    filter_upwards [hreg] with ω ⟨hA, hγ, hne⟩ using ⟨isOpen_stripRightSide hA, hγ, hne⟩

end Sec5

end InteractingSLE

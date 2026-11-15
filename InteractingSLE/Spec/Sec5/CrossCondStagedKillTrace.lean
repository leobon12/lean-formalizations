/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodesFar
import InteractingSLE.Spec.Sec7.ContinuityProbCollision

/-!
# Proposition 5.9's killed stage law: what its comparison premise demands

Packet PROVE-STAGED8. PROVE-PROP59-NODES states the per-stage law of Proposition 5.9 in the killed comparison form
`Prop59Nodes.IsStageLawFar` (ruling R75): its premise `CompPremiseFar` quantifies over every integrated evolution
**with an almost surely existing generating trace through its whole lifetime**, sampled with the lifetime killed at
the first far contact (`farLife`).

The piece itself is a flow-line image killed at its first contact with the revealed counterflow; it carries a trace
only up to that contact. This file records, in Lean, what the comparison form then demands of a proof:

* `NoTracedEvolution κ ρL ρR y₀`: no integrated evolution from the start `y₀` (on any probability space in `Type`) has
  an almost surely existing generating trace through its lifetime;
* **`IsStageLawFar.measure_noTrace_eq_zero`**: if `IsStageLawFar` holds, then for every measurable set `N` of starts
  from which no traced evolution exists, `P(R ∩ y⁻¹ N) = 0` (as soon as this event is a past event). So a proof of
  `IsStageLawFar` must exhibit, from almost every realized start, an integrated evolution **with a trace through its
  whole lifetime** — for `κ ∈ (2, 4)` that lifetime continues past the far contact (the collapsed heading-side group has
  weight `κ − 4 > −2`, not a continuation threshold), so these are traces of `SLE_κ(ρ)` after a boundary collision
  (Theorem 1.3-type input, Aux. lemmas 99–113), which ruling R48 keeps out of Theorem 1.2's inputs;
* the **trace-up-to-the-kill form** `CompPremiseFarK` / `IsStageLawFarK` (premise over evolutions whose trace exists
  up to their killed lifetime `farLife` only), with `CompPremiseFarK.compPremiseFar` and
  `IsStageLawFar.isStageLawFarK`: the killed law of the piece in the form that needs no post-contact trace.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedKill

open Prop59Stage Prop59Nodes

/-! ### Starts without traced evolutions -/

section NoTrace

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **No traced evolution from `y₀`**: no integrated `SLE_κ(ρ)` evolution from the start `y₀` (on a probability space
in `Type`) has an almost surely existing generating trace through its lifetime. -/
def NoTracedEvolution (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (y₀ : Start nL nR) : Prop :=
  ∀ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
    IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
    ¬ ∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω') (ζ' ω') η

/-- **The premise holds with `p = 1` for the event "the start is not in `N`"** when no start of `N` has a traced
evolution: from a start in `N` the premise is vacuous, from a start outside `N` the event is sure. -/
theorem compPremiseFar_noTrace {N : Set (Start nL nR)} (hN : ∀ y₀ ∈ N, NoTracedEvolution κ ρL ρR y₀)
    (iL : Fin nL) (iR : Fin nR) : CompPremiseFar κ ρL ρR iL iR univ (Nᶜ ×ˢ univ) 1 := by
  intro y₀ _ Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  by_cases hy : y₀ ∈ N
  · exact absurd htr (hN y₀ hy Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE)
  · have e : {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
        (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω'))) ∈ Nᶜ ×ˢ univ} =
        univ := by
      ext ω'
      simp only [mem_ofPred_eq, mem_prod, mem_compl_iff, mem_univ, and_true, iff_true]
      exact hy
    rw [e, measure_univ]

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R : Set Ω}
  {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The killed comparison form demands traced evolutions from the realized starts.** If a stage obeys
`IsStageLawFar`, then for every measurable set `N` of starts from which no integrated evolution has a trace through
its lifetime, the stage event meets `y⁻¹ N` only in a null set (provided `R ∩ y⁻¹ N` is a past event, e.g. when `y` is
past-measurable). -/
theorem IsStageLawFar.measure_noTrace_eq_zero
    (hL : IsStageLawFar κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ) {N : Set (Start nL nR)} (hNm : MeasurableSet N)
    (hN : ∀ y₀ ∈ N, NoTracedEvolution κ ρL ρR y₀) (hA : MeasurableSet[𝓠] (R ∩ y ⁻¹' N)) :
    P (R ∩ y ⁻¹' N) = 0 := by
  have h := hL.2 (Nᶜ ×ˢ univ) (hNm.compl.prod MeasurableSet.univ) 1 (compPremiseFar_noTrace hN iL iR)
    (R ∩ y ⁻¹' N) hA inter_subset_left
  have e : R ∩ y ⁻¹' N ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈
      Nᶜ ×ˢ univ} = ∅ := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_prod, mem_compl_iff, mem_univ, and_true,
      mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun h => h.2
  rw [e, measure_empty, one_mul] at h
  exact le_antisymm h zero_le

/-- **No traced evolution at all**: if no start has a traced evolution, a stage obeying `IsStageLawFar` with a
past-measurable start is reached only on a null set. -/
theorem IsStageLawFar.measure_eq_zero_of_noTrace
    (hL : IsStageLawFar κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ) (hN : ∀ y₀, NoTracedEvolution κ ρL ρR y₀)
    (hR : MeasurableSet[𝓠] R) : P R = 0 := by
  have h := IsStageLawFar.measure_noTrace_eq_zero hL MeasurableSet.univ (fun y₀ _ => hN y₀)
    (by rw [preimage_univ, inter_univ]; exact hR)
  rwa [preimage_univ, inter_univ] at h

end NoTrace

/-! ### The premise over evolutions traced up to the kill -/

section TraceK

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR}

/-- **The killed premise over evolutions traced up to the kill**: as `CompPremiseFar`, but every integrated
evolution whose trace exists (almost surely) **up to its killed lifetime `farLife`** must satisfy the bound. Since a
trace through the lifetime is a trace up to `farLife ≤ ζ`, this premise is stronger than `CompPremiseFar`
(`CompPremiseFarK.compPremiseFar`). -/
def CompPremiseFarK (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR)
    (D : Set (Start nL nR)) (S : Set (Start nL nR × Samp nL nR)) (p : ℝ≥0∞) : Prop :=
  ∀ y₀ ∈ D, ∀ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
    IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
    (∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω')
      (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')) η) →
    p ≤ P' {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
      (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω'))) ∈ S}

/-- A premise over evolutions traced up to the kill is a premise over evolutions traced through their lifetime. -/
theorem CompPremiseFarK.compPremiseFar {D : Set (Start nL nR)} {S : Set (Start nL nR × Samp nL nR)} {p : ℝ≥0∞}
    (h : CompPremiseFarK κ ρL ρR iL iR D S p) : CompPremiseFar κ ρL ρR iL iR D S p := by
  intro y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  refine h y₀ hy Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE ?_
  filter_upwards [htr] with ω' hω'
  obtain ⟨η, hη⟩ := hω'
  exact ⟨η, hη.mono_horizon farLife_le⟩

/-- **The killed stage law in the trace-up-to-the-kill form**: clause 1 of `IsStageLawFar`, and the comparison clause
for every premise over evolutions traced up to their killed lifetime. It needs no trace of any evolution after its
first far contact. -/
def IsStageLawFarK (κ : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝓠 : MeasurableSpace Ω)
    (R : Set Ω) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR)
    (y : Ω → Start nL nR) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  (∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧ StrictMono (y ω).2.2 ∧
    Sec2.IsSLEPathUpTo κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω)
      (B · ω) (ζ ω)) ∧
  ∀ S : Set (Start nL nR × Samp nL nR), MeasurableSet S → ∀ p : ℝ≥0∞, CompPremiseFarK κ ρL ρR iL iR univ S p →
    ∀ A : Set Ω, MeasurableSet[𝓠] A → A ⊆ R →
      p * P A ≤ P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S})

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R : Set Ω}
  {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- `IsStageLawFar` implies the trace-up-to-the-kill form. -/
theorem IsStageLawFar.isStageLawFarK (hL : IsStageLawFar κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ) :
    IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ :=
  ⟨hL.1, fun S hS p hp A hA hAR => hL.2 S hS p hp.compPremiseFar A hA hAR⟩

/-- In the trace-up-to-the-kill form, a past event of the stage event is never charged more than its measure: the
lower bound of a premise holding with `p` is at most `1` on every non-null event. -/
theorem IsStageLawFarK.le_measure (hL : IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ)
    {S : Set (Start nL nR × Samp nL nR)} (hS : MeasurableSet S) {p : ℝ≥0∞}
    (hp : CompPremiseFarK κ ρL ρR iL iR univ S p) {A : Set Ω} (hA : MeasurableSet[𝓠] A) (hAR : A ⊆ R) :
    p * P A ≤ P A :=
  (hL.2 S hS p hp A hA hAR).trans (measure_mono inter_subset_left)

end TraceK

end InteractingSLE.Sec5.CrossCond.StagedKill

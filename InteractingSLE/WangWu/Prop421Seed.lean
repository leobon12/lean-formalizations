/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop419
import InteractingSLE.WangWu.PrefixLocalSides
import InteractingSLE.Spec.Sec2.TwoSeedPath

/-!
# Lemma 4.21 on the seed-line space: one centred field for all heights, and each seed line local for it

Packet PROVE-WW-B20. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.txt`, Lemma 4.21 (L1745–L1752: "Two seed
lines of different heights share no nontrivial subarc almost surely. […] The local-set union boundary lemma then forces
the union conditional mean to converge both to `−λ − u₁` and to `−λ − u₂`"). The landed Lemma 4.21
(`ae_interior_contact_eq_empty_inter`, PROVE-WW-B5/B8) is stated for two curves that are local sets of **one**
zero-boundary field. On the seed-line space of `Prop419.lean` the line of height `u` is a level line of `h + u`, whose
centred field is `(h + u) − (u₀ + u)`; this file shows that it is the same field `h − u₀` for every height, so
that every
seed line is a local set of that one field:

* `integral_add_const_mul_test`, **`centredField_flowField_eq`**: `centredField (h + c) (u₀ + c) = centredField h u₀`;
* **`isLocalSet_seedLine_centred`**: on the seed-line space, `arcRange γ_u ∩ ℍ` is a local set of `h − u₀` for
every height.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedField

theorem continuousOn_of_isBoundedHarmonicExtension {g : ℝ → ℝ} {S : Set ℝ} {u₀ : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u₀) : ContinuousOn u₀ H := fun z hz =>
  (hu.1 z hz).1.continuousAt.continuousWithinAt

/-- `∫ (u₀ + c) φ = ∫ u₀ φ + c ∫ φ` for a continuous `u₀` on `ℍ` and a test function `φ`. -/
theorem integral_add_const_mul_test {u₀ : ℂ → ℝ} (hc : ContinuousOn u₀ H) (c : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, (u₀ z + c) * φ z = (∫ z, u₀ z * φ z) + c * ∫ z, φ z := by
  have h1 : Integrable (fun z => u₀ z * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H) hc φ φ.tsupport_subset
  have h2 : Integrable (fun z => c * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H) continuousOn_const φ φ.tsupport_subset
  have e : (fun z => (u₀ z + c) * φ z) = fun z => u₀ z * φ z + c * φ z := funext fun z => by ring
  rw [e, integral_add h1 h2, integral_const_mul]

/-- **One centred field for all heights**: `(h + c) − (u₀ + c) = h − u₀` as distributions on `ℍ`. -/
theorem centredField_flowField_eq {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) {u₀ : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u₀ H) (c : ℝ) :
    WholeField.centredField (fun ω => Exist.flowField 0 c (h ω)) (fun z => u₀ z + c) =
      WholeField.centredField h u₀ := by
  have hu' : InnerProductSpace.HarmonicOnNhd (fun z => u₀ z + c) H := fun z hz =>
    (hu z hz).add (InnerProductSpace.harmonicAt_const _)
  have hc : ContinuousOn u₀ H := fun z hz => (hu z hz).1.continuousAt.continuousWithinAt
  funext ω
  ext φ
  rw [WholeField.centredField_apply _ hu', WholeField.centredField_apply _ hu, Exist.flowField_apply,
    integral_add_const_mul_test hc c φ]
  have hφ : Chart.pushTest (Exist.isConformal_shiftChart 0) φ = φ := by
    ext z
    rw [Exist.pushTest_shiftChart_apply, Complex.ofReal_zero, sub_zero]
  rw [hφ]
  ring

/-- **Each seed line is a local set of the common centred field** (the input of Lemma 4.21 on the seed-line space). On a
space carrying a field `h` with the two-seed data of `(ρL; ρR)` (bounded harmonic extension `u₀`) and an optional hull
coupling of the nonnegative word `(ρL − c/λ; ρR + c/λ)` with the field `h + c`, the range of its seed line, intersected
with `ℍ`, is a local set of `h − u₀`. -/
theorem isLocalSet_seedLine_centred {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {rL rR c : ℝ} (hL : 0 ≤ rL - c / wwLambda) (hR : 0 ≤ rR + c / wwLambda)
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - c / wwLambda)
      (fun _ => rR + c / wwLambda) P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 c (h ω)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL)
      (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀) :
    IsLocalSet (fun ω => arcRange (seedLine ζ W ω) ∩ H) (WholeField.centredField h u₀) P := by
  have hF := isFullLevelLineCoupling_twoSeed hL hR hC
  have hseed := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1
  have htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
    filter_upwards [hseed] with ω hω
    obtain ⟨hζ, ⟨η, hη, -⟩, -⟩ := hω
    exact ⟨η, hζ ▸ hη⟩
  have hthr : ¬ ForceWord.ThresholdCondition (fun _ : Fin 1 => rL - c / wwLambda) (fun _ : Fin 1 => rR + c / wwLambda)
      0 LP.twoSeedXL LP.twoSeedXR :=
    Sec2.TwoSeed.not_thresholdCondition_fin_one (fun _ => by linarith) (fun _ => by linarith) 0 _ _
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hseed.mono fun ω hω => hω.1
  have hγ : ∀ᵐ ω ∂P, IsLoewnerTrace (Ito.rpath (W · ω)) (seedLine ζ W ω) ∧ IsProperArc (seedLine ζ W ω) :=
    hseed.mono fun ω hω => ⟨hω.2.2.1, hω.2.2.2.1⟩
  have hu' := Sec5.GlueCond.isBoundedHarmonicExtension_add_const hu₀ c
  have hdata : (fun x => forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
      LP.twoSeedXR x + c) = forceBoundaryData 4 (fun _ : Fin 1 => rL - c / wwLambda)
        (fun _ : Fin 1 => rR + c / wwLambda) LP.twoSeedXL LP.twoSeedXR :=
    funext fun x => forceBoundaryData_twoSeed_four_add rL rR c x
  rw [hdata] at hu'
  have hloc := hF.isLocalSet_line htr hthr hζ hγ hu'
  rwa [centredField_flowField_eq h hu₀.1 c] at hloc

end InteractingSLE.WangWu.SeedField

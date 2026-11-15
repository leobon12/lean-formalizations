/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterRoot

/-!
# Proposition 5.9 at depth `ℓ`: DEPTH's deterministic wiring hypotheses for the shifted root field

Packet PROVE-STAGED-S3. DEPTH's `ae_stage_meanIdent`/`ae_stage_charIdent` take, besides the probabilistic setting,
two deterministic hypotheses relating the coupling field `h` (with its mean `𝔥₀`) to the staged field `h_s` (with its
mean `𝔥_s`): `hcs : centredField h_s 𝔥_s = centredField h 𝔥₀` and `hu₀s : 𝔥₀ = 𝔥_s + θ₀χ`. For PROVE-PROP59-PIECES'
root instance (`h = rootField = flowField 0 ((π/2)χ) qField`, `h_s = qField`, `θ₀ = π/2`) both hold with
`𝔥₀ = 𝔥_s + (π/2)χ`, and this `𝔥₀` is a bounded harmonic extension of the root flow word's data:

* **`centredField_flowField_zero`** (`hcs` for any shift `flowField 0 a`), `centredField_rootField`;
* `isBoundedHarmonicExtension_congr_H`, **`isBoundedHarmonicExtension_flowWord_add`** (`hu₀` for
  `𝔥₀ = 𝔥_s + θχ` at any angle `θ`, from the seed identity of the flow word).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS3

section Wire

/-- A bounded harmonic extension only depends on its values in `ℍ`. -/
theorem isBoundedHarmonicExtension_congr_H {g : ℝ → ℝ} {S : Set ℝ} {u v : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (h : EqOn u v H) : IsBoundedHarmonicExtension g S v := by
  obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hu
  have hev : ∀ z ∈ H, u =ᶠ[𝓝 z] v := fun z hz =>
    Filter.eventuallyEq_of_mem (QuantumZipper.isOpen_H.mem_nhds hz) h
  refine ⟨fun z hz => (InnerProductSpace.harmonicAt_congr_nhds (hev z hz)).1 (hharm z hz),
    ⟨C, fun z hz => h hz ▸ hC z hz⟩, fun x hx => ?_⟩
  exact (hlim x hx).congr' (eventuallyEq_nhdsWithin_of_eqOn h)

/-- **`hu₀` for the shifted mean**: if `𝔥_s` is a bounded harmonic extension of piecewise constant data `b` with jumps
`J`, then `𝔥_s + θχ` is a bounded harmonic extension of the data of the flow-line word from `0` at angle `θ`. -/
theorem isBoundedHarmonicExtension_flowWord_add {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ) {us : ℂ → ℝ} (hus : IsBoundedHarmonicExtension b J us) :
    IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0))
      (fun z => us z + θ * chiC κ) := by
  obtain ⟨u, hu⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b J 0 θ)
    (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0)
  have heq := Exist.eqOn_flowLine_harmonicExtension hκ hb 0 θ hus hu
  refine isBoundedHarmonicExtension_congr_H hu fun z hz => ?_
  rw [heq hz]
  simp only [Complex.ofReal_zero, add_zero]

/-- **`hcs` for a constant shift**: the centred field of `flowField 0 a ∘ f` with the mean `𝔥_s + a` is the centred
field of `f` with the mean `𝔥_s`. -/
theorem centredField_flowField_zero {Ω : Type*} (f : Ω → DistOn upperHalfPlaneOpens) {us : ℂ → ℝ}
    (hus : InnerProductSpace.HarmonicOnNhd us H) (a : ℝ) (ω : Ω) :
    WholeField.centredField (fun ω => Exist.flowField 0 a (f ω)) (fun z => us z + a) ω =
      WholeField.centredField f us ω := by
  have hus' : InnerProductSpace.HarmonicOnNhd (fun z => us z + a) H := fun z hz =>
    (hus z hz).add (InnerProductSpace.harmonicAt_const _)
  ext φ
  rw [WholeField.centredField_apply _ hus' ω φ, WholeField.centredField_apply _ hus ω φ, Exist.flowField_apply,
    GlueCond.pushTest_shiftChart_zero]
  have hc : ContinuousOn us H := fun z hz => (hus z hz).1.continuousAt.continuousWithinAt
  have hi1 : Integrable (fun z => us z * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H) hc φ φ.tsupport_subset
  have hi2 : Integrable (fun z => a * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H) continuousOn_const φ φ.tsupport_subset
  have e : (fun z => (us z + a) * φ z) = fun z => us z * φ z + a * φ z := funext fun z => by ring
  rw [e, integral_add hi1 hi2, integral_const_mul]
  ring

/-- **`hcs` for PROVE-PROP59-PIECES' root instance**: the root coupling field `rootField = qField + (π/2)χ` with the
mean `𝔥_s + (π/2)χ` has the centred field of `qField` with the mean `𝔥_s`. -/
theorem centredField_rootField {κ x₀ : ℝ} {Ω : Type} (h : Ω → DistOn upperHalfPlaneOpens) {us : ℂ → ℝ}
    (hus : InnerProductSpace.HarmonicOnNhd us H) (ω : Ω) :
    WholeField.centredField (StagedRepLater.rootField (κ := κ) (x₀ := x₀) h) (fun z => us z + π / 2 * chiC κ) ω =
      WholeField.centredField (Prop59Pieces.qField x₀ κ h) us ω :=
  centredField_flowField_zero (Prop59Pieces.qField x₀ κ h) hus _ ω

end Wire

end InteractingSLE.Sec5.CrossCond.StagedS3

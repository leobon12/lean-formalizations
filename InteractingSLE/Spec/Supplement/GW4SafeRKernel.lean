/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRUnion

/-!
# GW4: Gaussian kernels of the global marked union

At every deterministic original time the union of the two walks and the
counterflow prefix has the marked Gaussian field kernel. Its mean here is the
actual local-set mean, rather than an asserted finite-word formula. The kernel
keeps both walk records and the counterflow record.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField WalkLaw Sec5.GlueCond Sec5.Cond44Ref

section Shift

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The marked local-set Gaussian kernel with a deterministic harmonic initial
mean restored. This specializes the zero-boundary kernel of `RelSafeS`. -/
theorem ae_condExp_cexp_boundary_marked {h : Ω → DistOn upperHalfPlaneOpens}
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B)
    (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) (hℋ : ℋ ≤ mΩ)
    (hloc : IsHistoryAvoidanceLocal ℋ B (centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean B (centredField h u₀) P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
      germSigma B (centredField h u₀) ⊔ ℋ] ω =
      Complex.exp (Complex.I * ((g ω + smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov (H \ B ω) φ φ : ℝ) : ℂ)) := by
  have h1 := Supp8.RelSafeS.ae_condExp_cexp_marked hh0 hBm hBc hℋ hloc hg φ
  have hc : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hsplit : (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) =
      Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) •
        fun ω => Complex.exp (Complex.I * (centredField h u₀ ω φ : ℂ)) := by
    funext ω
    rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, centredField_apply h hu₀ ω φ]
    congr 1
    push_cast
    ring
  have h2 : P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) |
      germSigma B (centredField h u₀) ⊔ ℋ] =ᵐ[P]
      Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) •
        P[fun ω => Complex.exp (Complex.I * (centredField h u₀ ω φ : ℂ)) |
          germSigma B (centredField h u₀) ⊔ ℋ] := by
    rw [hsplit]
    exact condExp_smul _ _ _
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω2, Pi.smul_apply, smul_eq_mul, hω1, add_apply, smoothDist_apply hc,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have he : (∫ z, φ z * u₀ z) = ∫ z, u₀ z * φ z := by
    congr 1
    funext z
    exact mul_comm _ _
  rw [he]
  push_cast
  ring

end Shift

/-- The global Gaussian kernel of the actual walks and the counterflow prefix.
The local-set means are supplied by the local-set theorem; no finite-word mean
identification, conditional restart, or independence after disintegration is used. -/
theorem exists_walkCfUnion_kernel
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b J P h spec (E spec))
    (hreg : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b J P spec (E spec))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀) :
    ∃ (B : ℝ≥0 → Ω → Set ℂ) (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens),
      (∀ t, walkCfMarks κ b J E W ζ t ≤ mΩ) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧
      (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
      (∀ t, ∀ᵐ ω ∂P, B t ω = relClosureH
        (walkUnionSet κ b J E ω ∪ cfHullQ t (cfHistory W ζ ω))) ∧
      (∀ t, IsHistoryAvoidanceLocal (walkCfMarks κ b J E W ζ t)
        (B t) (centredField h u₀) P) ∧
      (∀ t, IsLocalSetMean (B t) (centredField h u₀) P (g t)) ∧
      ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          germSigma (B t) (centredField h u₀) ⊔ walkCfMarks κ b J E W ζ t] ω =
        Complex.exp (Complex.I * ((g t ω + smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (H \ B t ω) φ φ : ℝ) : ℂ)) := by
  obtain ⟨B, hℋ, hBm, hBc, hBeq, hloc⟩ :=
    exists_walkCfUnion h12p h13 hκ hκ4 hb hh hcf hζ hE hreg hu₀
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hl : ∀ t, IsLocalSet (B t) (centredField h u₀) P := fun t =>
    ((isLocalSet_tfae hh0 (hBm t) (Eventually.of_forall (hBc t))).out 4 1).2
      (hloc t).isAvoidanceLocal
  choose g hg using fun t => IsLocalSet.exists_isLocalSetMean hh0 (hBm t) (hl t)
  exact ⟨B, g, hℋ, hBm, hBc, hBeq, hloc, hg, fun t =>
    ae_condExp_cexp_boundary_marked hu₀.1 hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hg t)⟩

end InteractingSLE.Theorem14.GW4Fix

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightFibres
import InteractingSLE.Spec.Sec5.Aux61GlueKCover

/-!
# The fibre kernel from the chart union law, PC1 and glued projection independence

PROVE-WIRE-PARTA. Kernel measurability and raw conditional member identities
are consequences of the landed GlueK reductions. The new data record contains
only objects; its mathematical and measurability requirements are named below.
-/

set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Dawn
open Sec5 Sec5.Aux61Fib Sec5.Aux61FibK Sec5.Aux61GlueK
open Restart.DomainMarkov (RatIdx dyT safeEv ballsOpen)
open LocalExt (cfVal)

/-- The fixed words, conditioning sigma-algebras and candidate harmonic means. -/
structure FibreKernelData {X : Type u} [MeasurableSpace X] (D : Night.FibreRecords X) where
  kappa : D.ι → ℝ
  boundary : D.ι → ℝ → ℝ
  jumps : D.ι → Finset ℝ
  sigma : D.ι → ℕ → ℕ → MeasurableSpace X
  mean : D.ι → ℕ → ℕ → X → ℂ → ℝ

/-- Fixed reference words and joint measurability of the correction and cutoff. -/
def FibreDataMeas {X : Type u} [MeasurableSpace X] (D : Night.FibreRecords X)
    (K : FibreKernelData D) : Prop :=
  (∀ i z, (D.data i z).κ = K.kappa i ∧ (D.data i z).bR = K.boundary i ∧
    (D.data i z).JR = K.jumps i) ∧
  (∀ i, Measurable fun p : D.β i × ℂ => (D.data i p.1).q p.2) ∧
  (∀ i, Measurable fun p : D.β i × ℂ => (D.cutoff i p.1).f p.2) ∧
  ∀ i, Measurable fun p : D.β i × ℂ => QuantumZipper.K3.greenDensity (D.cutoff i p.1).f p.2

/-- Conditioning contains the history and stopped raw code and lies in the ambient space. -/
def FibreSigma {X : Type u} [mX : MeasurableSpace X] (D : Night.FibreRecords X)
    (K : FibreKernelData D) : Prop :=
  (∀ i n k, K.sigma i n k ≤ mX) ∧
  (∀ i n k, (D.mβ i).comap (D.Z i) ≤ K.sigma i n k) ∧
  ∀ i n k, (codeSigma.{u} n k).comap (fun x => ULift.up.{u} (D.Y i x)) ≤ K.sigma i n k

/-- The union characteristic functional in the chart, before PC1 identifies its mean. -/
def FibreChart {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : Night.FibreRecords X)
    (K : FibreKernelData D) : Prop :=
  ∀ i (n k : ℕ) (p : RatIdx), ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → ULift.up.{u} (D.Y i x) ∈ ratAvoid n k p →
    μ[fun x' => Complex.exp (Complex.I * (fibField (ULift.up.{u} (D.Y i x')) (ratψ p) : ℂ)) |
      K.sigma i n k] x =
      cfVal (∫ z, K.mean i n k x z * ratψ p z)
        (loewnerGreenEnergy (Ito.rpath (fibW · (ULift.up.{u} (D.Y i x)))) (dyT n k : ℝ≥0) (ratψ p))

/-- PC1 for the actual candidate mean in the chart. -/
def FibrePC1 {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : Night.FibreRecords X)
    (K : FibreKernelData D) : Prop :=
  ∀ i (n k : ℕ), ∀ᵐ x ∂μ, D.Z i x ∈ D.B i →
    ((dyT n k : ℝ≥0) : ℝ≥0∞) < fibU (ULift.up.{u} (D.Y i x)) →
      Aux61Win.IsPC1 (D.data i (D.Z i x)).κ
        (canonExt (D.data i (D.Z i x)) (ULift.up.{u} (D.Y i x)) (dyT n k))
        (Ito.rpath (fibW · (ULift.up.{u} (D.Y i x)))) (dyT n k)
        (D.data i (D.Z i x)).q (D.data i (D.Z i x)).O₀ (K.mean i n k x)

/-- Projection independence on the glued history/code rectangles. -/
def FibreLocal {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : Night.FibreRecords X) : Prop :=
  ∀ i (r s : ℚ≥0), r < s → ∀ F : Finset (ℚ × ℚ × ℚ), Coupling.ballsK F ⊆ H →
    ∀ (T : Finset (ℚ × ℚ × ℚ)) (B' : Set (D.β i)), MeasurableSet B' → B' ⊆ D.B i →
      Coupling.IsProjIndepMeasure (ballsOpen F)
        ((μ.restrict (D.Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (D.Y i x)) ⁻¹'
          (ratPi fibW fibU (r : ℝ≥0) T ∩ safeEv fibW fibU F (s : ℝ≥0)))).map
            fun x => fibField (ULift.up.{u} (D.Y i x)))

/-- The old kernel-measurability hypothesis is proved from the data facts. -/
theorem fibreMeas_of_data {X : Type u} [MeasurableSpace X] (D : Night.FibreRecords X)
    (K : FibreKernelData D) (hm : FibreDataMeas D K) : Night.FibreMeas D := by
  obtain ⟨hw, hq, hf, hs⟩ := hm
  exact fun i n k p => measurable_ratAvoid_ratKer (D.data i) (D.cutoff i)
    (K.kappa i) (K.boundary i) (K.jumps i) (hw i) (hq i) (hf i) (hs i) n k p

/-- The raw rectangle kernel integrals follow from the union chart law and PC1. -/
theorem fibreIntegral_of_chart {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} (D : Night.FibreRecords X) (K : FibreKernelData D)
    (hg : Night.FibreGeometry μ E D) (hm : FibreDataMeas D K) (hs : FibreSigma D K)
    (hc : FibreChart μ D K) (hp : FibrePC1 μ D K) : Night.FibreIntegral μ D := by
  obtain ⟨hZ, hY, hB, hL, hLv, hRef, hG, hGgood, hYG, hcover, hE, hcut⟩ := hg
  have hgood : ∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → PathGood (D.data i (D.Z i x)) (D.Y i x) :=
    fun i => (hYG i).mono fun x hx hxB => hGgood i _ _ hxB (hx hxB)
  exact fun i => hint_of_chartKernel (hZ i) (hY i) (hB i) (D.data i) (D.cutoff i) (D.neighbourhood i)
    (hcut i) (hgood i) (fibreMeas_of_data D K hm i)
    (K.sigma i) (hs.1 i) (hs.2.1 i) (hs.2.2 i) (K.mean i) (hc i) (hp i)

/-- Raw fibre member identities follow from glued projection independence. -/
theorem fibreMembers_of_local {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} (D : Night.FibreRecords X) (hg : Night.FibreGeometry μ E D)
    (hm : Night.FibreMeas D) (hi : Night.FibreIntegral μ D) (hl : FibreLocal μ D) :
    Night.FibreMembers μ D := by
  obtain ⟨hZ, hY, hB, hL, hLv, hRef, hG, hGgood, hYG, hcover, hE, hcut⟩ := hg
  exact fun i => ae_fibMembersRaw_of_glued (hZ i) (hY i) (hB i) (D.data i)
    (ae_pathGood_condDistrib (hZ i) (hY i) (hB i) (D.data i) (D.G i) (hG i) (hGgood i) (hYG i))
    (ae_fibKernelRaw_of_glued (hZ i) (hY i) (hB i) (D.data i) (D.cutoff i) (D.neighbourhood i)
      (hcut i) (D.G i) (hG i) (hGgood i) (hYG i) (hm i) (hi i)) (hl i)

end InteractingSLE.Wire.Dawn

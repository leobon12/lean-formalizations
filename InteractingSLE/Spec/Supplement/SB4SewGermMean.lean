/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewLawK2
import InteractingSLE.Spec.Sec6.Prop61BGlobal
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# Identifying the retained germ mean from its surviving-word boundary limits

This is the mean-identification argument used by the landed image union law:
locality supplies a harmonic local-set mean; Proposition 6.1 and Aux. 28 identify
it on each component from prime-end limits outside finitely many exceptions.
The input below records those boundary limits and the actual surviving word.
It does not assume the conditional-mean identity being proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)

universe u

namespace InteractingSLE.Theorem14.SB.SewGerm

open LocalSets

/-- On every component, the physical candidate is the harmonic extension of
the surviving real word with the inherited argument lift. The local-set mean
has its boundary values at all prime ends except finitely many marked fibers.
Constructing these data for arbitrary SB4 histories is a separate obligation. -/
def HasSurvivingWordBoundary (A : Set ℂ) (u₀ v w : ℂ → ℝ) (χ : ℝ)
    (b : ℝ → ℝ) (jumps : Finset ℝ) : Prop :=
  ∀ z₀ ∈ H \ A, ∃ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
    IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ A) z₀) ∧
    IsConformalBijection φc (connectedComponentIn (H \ A) z₀) H ∧
    IsBoundedHarmonicExtension b jumps G ∧
    ContinuousOn L (connectedComponentIn (H \ A) z₀) ∧
    (∀ z ∈ connectedComponentIn (H \ A) z₀,
      deriv φc z = ‖deriv φc z‖ * Complex.exp (L z * Complex.I)) ∧
    E.Finite ∧
    EqOn v (fun z => G (φc z) - χ * L z) (connectedComponentIn (H \ A) z₀) ∧
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
        (𝓝[ball 0 1] q) (𝓝 0)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- Prime-end uniqueness identifies the physical mean on the entire complement,
including unbounded components. No boundedness of the local-set mean is assumed:
the landed Gaussian growth theorem supplies the growth needed by Aux. 28. -/
theorem ae_eqOn_physicalMean_of_boundary
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g)
    {v : Ω → ℂ → ℝ} {b : Ω → ℝ → ℝ} {jumps : Ω → Finset ℝ} (χ : ℝ)
    {D : Set Ω}
    (hbd : ∀ᵐ ω ∂P, ω ∈ D → ∀ w : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        g ω φ = ∫ z, w z * φ z) →
      HasSurvivingWordBoundary (A ω) u₀ (v ω) w χ (b ω) (jumps ω)) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ w : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        g ω φ = ∫ z, w z * φ z) →
      EqOn (fun z => w z + u₀ z) (v ω) (H \ A ω) := by
  have huniq := Sec6.ae_eqOn_component_of_tendsto_global hh0 hAm hloc hg hu₀ hu₀b χ
  filter_upwards [huniq, hbd] with ω hω hbω hωD w hw hrep z hz
  obtain ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, hlim⟩ :=
    hbω hωD w hw hrep z hz
  have he := hω z hz w hw hrep f φc G L E hf hφc hG.1 hG.2.1 hL hd hE hlim
  exact (he z (mem_connectedComponentIn hz)).trans (hv (mem_connectedComponentIn hz)).symm

/-- The joint retained germ mean is the physical surviving-word mean once its
prime-end boundary data have been established. In particular the conclusion is
`SewLaw.HasActiveGermMean`, not a hypothesis of this theorem. -/
theorem hasActiveGermMean_of_boundary
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ)
    (A : ℝ≥0 → Ω → Set ℂ) (hAm : ∀ q, Measurable[mΩ, hittingSigma] (A q))
    (hAc : ∀ q, ∀ᵐ ω ∂P, A q ω ⊆ H ∧ IsOpen (H \ A q ω))
    (hloc : ∀ q, WholeField.IsHistoryAvoidanceLocal
      (𝓜 q) (A q) (WholeField.centredField h u₀) P)
    (F : Set Ω) (ζ : Ω → ℝ≥0∞) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (v : ℝ≥0 → Ω → ℂ → ℝ) (b : ℝ≥0 → Ω → ℝ → ℝ)
    (jumps : ℝ≥0 → Ω → Finset ℝ) (χ : ℝ)
    (hM : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      (q : ℝ≥0∞) < ζ ω → tsupport φ ⊆ H \ A q ω → M q ω φ = ∫ z, v q ω z * φ z)
    (hbd : ∀ q (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (A q) (WholeField.centredField h u₀) P g →
      ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∀ w : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd w (H \ A q ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A q ω →
          g ω φ = ∫ z, w z * φ z) →
        HasSurvivingWordBoundary (A q ω) u₀ (v q ω) w χ (b q ω) (jumps q ω)) :
    SewLaw.HasActiveGermMean P 𝓜 A h u₀ F ζ M := by
  intro q φ
  have hl : IsLocalSet (A q) (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae hh0 (hAm q) (hAc q)).out 1 4).1 (hloc q).isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hAm q) hl
  have hce := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup
    hh0 (hAm q) hl (h𝓜 q) (hloc q) hg φ
  have heq := ae_eqOn_physicalMean_of_boundary (D := {ω | ω ∈ F ∧ (q : ℝ≥0∞) < ζ ω})
    hh0 hu₀ hu₀b (hAm q) hl hg χ
    ((hbd q g hg).mono fun ω hω hD => hω hD.1 hD.2)
  filter_upwards [hce, hg.2.1, heq, hM q φ] with ω hcω hgω heω hMω hF hq hφ
  obtain ⟨w, hw, hrep⟩ := hgω
  have hid := heω ⟨hF, hq⟩ w hw hrep
  have hwi : Integrable fun z => w z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hw z hz).1.continuousAt.continuousWithinAt) φ hφ
  have hui : Integrable fun z => u₀ z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt) φ φ.tsupport_subset
  have hint : (∫ z, v q ω z * φ z) = (∫ z, w z * φ z) + (∫ z, u₀ z * φ z) := by
    rw [← integral_add hwi hui]
    apply integral_congr_ae
    refine Eventually.of_forall fun z => ?_
    by_cases hz : φ z = 0
    · simp only [hz, mul_zero, add_zero]
    · change v q ω z * φ z = w z * φ z + u₀ z * φ z
      rw [← hid (hφ (subset_tsupport _ hz))]
      ring
  rw [← hcω, hrep φ hφ, hMω hF hq hφ, hint]
  ring

end InteractingSLE.Theorem14.SB.SewGerm

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactGerm
import InteractingSLE.Spec.Sec7.Aux119Heights

/-!
# Deterministic shifts of local-set means

PROVE-SIDE-COLLAR2. A deterministic distribution changes neither the
neighborhood germ sigma-algebras nor their intersection. Adding a harmonic
distribution therefore adds precisely that distribution to a local mean.
These statements do not assume that the ambient field is a GFF.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.SideC12

open LocalSets

/-- A deterministic shift preserves every neighborhood germ sigma-algebra. -/
theorem germSigmaAt_add_dist_eq {Ω : Type*} (A : Ω → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) (T : DistOn upperHalfPlaneOpens) (δ : ℝ) :
    germSigmaAt A (fun ω => h ω + T) δ = germSigmaAt A h δ := by
  have hle : ∀ (f : Ω → DistOn upperHalfPlaneOpens) (S : DistOn upperHalfPlaneOpens),
      germSigmaAt A (fun ω => f ω + S) δ ≤ germSigmaAt A f δ := by
    intro f S
    refine sup_le le_sup_left (MeasurableSpace.generateFrom_le ?_)
    rintro E ⟨φ, B, hB, rfl⟩
    have he : {ω | tsupport φ ⊆ germNbhd δ (A ω)} ∩ (fun ω => (f ω + S) φ) ⁻¹' B =
        {ω | tsupport φ ⊆ germNbhd δ (A ω)} ∩
          (fun ω => f ω φ) ⁻¹' ((fun x : ℝ => x + S φ) ⁻¹' B) := rfl
    rw [he]
    exact (le_sup_right : MeasurableSpace.generateFrom _ ≤ germSigmaAt A f δ) _
      (MeasurableSpace.measurableSet_generateFrom
      ⟨φ, _, (measurable_id.add_const _) hB, rfl⟩)
  refine le_antisymm (hle h T) ?_
  have hback := hle (fun ω => h ω + T) (-T)
  simpa only [add_neg_cancel_right] using hback

/-- A deterministic shift preserves the full germ sigma-algebra. -/
theorem germSigma_add_dist_eq {Ω : Type*} (A : Ω → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) (T : DistOn upperHalfPlaneOpens) :
    germSigma A (fun ω => h ω + T) = germSigma A h := by
  unfold germSigma
  simp_rw [germSigmaAt_add_dist_eq]

/-- The actual local mean shifts by the same deterministic harmonic
distribution as its ambient field; the residual conditional law is unchanged. -/
theorem localSetMean_add_dist {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Set ℂ} (hAo : ∀ ω, IsOpen (H \ A ω))
    {h g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g)
    {T : DistOn upperHalfPlaneOpens} (hT : IsHarmonicDistOn T H) :
    IsLocalSetMean A (fun ω => h ω + T) P (fun ω => g ω + T) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [germSigma_add_dist_eq]
    exact (Coupling.measurable_add_distOnConst T).comp hg.1
  · filter_upwards [hg.2.1] with ω hω
    exact Coupling.IsHarmonicDistOn.add' (hAo ω) hω
      (LocalSets.IsHarmonicDistOn.mono hT sdiff_subset)
  · rw [germSigma_add_dist_eq]
    simpa only [add_sub_add_right_eq_sub] using hg.2.2

/-- The harmonic representative of a mean shifted by a smooth harmonic
function is the original representative plus that function, throughout the
open domain. This is a pointwise identity, not just equality in pairings. -/
theorem harmRep_add_smoothDist {T : DistOn upperHalfPlaneOpens} {U : Set ℂ}
    (hUo : IsOpen U) (hUH : U ⊆ H) (hT : IsHarmonicDistOn T U)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) :
    EqOn (Aux119Heights.harmRep
      (T + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u) U)
      (fun z => Aux119Heights.harmRep T U z + u z) U := by
  have hS := WholeField.isHarmonicDistOn_smoothDist hu
  have hTS := Coupling.IsHarmonicDistOn.add' hUo hT
    (LocalSets.IsHarmonicDistOn.mono hS hUH)
  obtain ⟨hV, hrepV⟩ := Aux119Heights.harmRep_spec hT
  obtain ⟨hVS, hrepVS⟩ := Aux119Heights.harmRep_spec hTS
  refine Sec6.eqOn_of_integral_mul_eq hUo hUH hVS (hV.add (hu.mono hUH)) ?_
  intro φ hφ
  have hiV := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
    (fun z hz => (hV z hz).1.continuousAt.continuousWithinAt) φ hφ
  have hiu := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
    (fun z hz => (hu z (hUH hz)).1.continuousAt.continuousWithinAt) φ hφ
  rw [← hrepVS φ hφ, add_apply, hrepV φ hφ,
    SupercriticalConformalCovariance.GM24.smoothDist_apply hu.continuousOn]
  simp_rw [add_mul]
  rw [integral_add hiV hiu]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)

end InteractingSLE.Sec7.SideC12

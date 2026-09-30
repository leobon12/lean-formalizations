import QuantumZipper.Proofs.Thm18.G3ZcChain
import QuantumZipper.Proofs.Thm18.G3Za7

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: the smoothed local coupling with both far clauses

`exists_pullSetupFar2`: ZOOM-A's `G3Za.exists_pullSetupFar` (local conformal coupling with the
harmonic part smoothed and the far gauge clause) together with the general far clause of
`G3Cv.pullCouplingHarm_of_process` (`FarPair`: increments of `W` carried away from the pull-back
region are a.s. `Ξ`-coordinates, the domain Markov property). Both come from one Hilbert
realization (`gs_process_hilbert`), so they hold for the same `W, X', Ξ`. Own assembly of
G3ZcFar/G3ZcChain and G3Za6.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology RealInnerProductSpace

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

theorem exists_pullSetupFar2 (hD : PullData Φ b r₀ ρ r₁ m M) (hr₁0 : 0 < r₁) {r' : ℝ}
    (hr' : 0 < r') (hr'r : r' < r₁) :
    ∃ (W X' : (ℕ → ℝ) → FieldSample) (Ξ : (ℕ → ℝ) → (PXiIdx Φ b ρ r₁ → ℝ))
      (g : (ℕ → ℝ) → ℂ → ℝ),
      IsFreeGFFModConstH W stdP ∧ IsFreeGFFModConstH X' stdP ∧ Measurable Ξ ∧
      Indep (MeasurableSpace.comap Ξ inferInstance) (freeIncrSigma X') stdP ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (closedBall (b : ℂ) r')) ∧
      (∀ z, Measurable[MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X' b ρ]
        fun ω => g ω z) ∧
      (∀ μ μ' : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH μ' → μ Set.univ = μ' Set.univ →
        μ (closedBall (b : ℂ) r')ᶜ = 0 → μ' (closedBall (b : ℂ) r')ᶜ = 0 →
        ∀ᵐ ω ∂stdP, W ω (μ.map Φ) - W ω (μ'.map Φ) =
          X' ω μ - X' ω μ' + ((∫ z, g ω z ∂μ) - ∫ z, g ω z ∂μ'))
      ∧ (∀ μ : LocIdx b r₁, ∀ S : Measure ℂ, IsAdmissibleH S → μ.1 Set.univ = S Set.univ →
        (∀ᵐ y ∂S, ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y) →
        ∃ D : (ℕ → ℝ) → ℝ, Measurable[MeasurableSpace.comap Ξ inferInstance] D ∧
          ∀ᵐ ω ∂stdP, W ω (μ.1.map Φ) - W ω S = X' ω μ.1 - X' ω (bal b ρ μ.1) + D ω)
      ∧ (∀ α α' : Measure ℂ, FarPair Φ b ρ α α' →
        ∃ u : PXiIdx Φ b ρ r₁, ∀ᵐ ω ∂stdP, W ω α - W ω α' = Ξ ω u) := by
  obtain ⟨J, hJ1, hJ2⟩ := exists_pullIsometry hD
  obtain ⟨Z, hZm, hZ⟩ := gs_process_hilbert (PIdx Φ b ρ r₁) (pVec J)
  obtain ⟨g, hW, hX, hΞ, hind, hfarP, hgc, hgh, hgm, hid⟩ :=
    pullCouplingHarm_of_process hD hr₁0 hJ1 hJ2 hZm hZ
  obtain ⟨g', hgh', hgm', hid'⟩ := pullSetup_of hD hr₁0 hr' hr'r hgc hgh hgm hid
  refine ⟨realWP Z, realXP Z, realXi Z, g', hW, hX, hΞ, hind, hgh', hgm', hid', ?_, hfarP⟩
  intro μ S hS hm hSy
  obtain ⟨u, hu⟩ := G3Za.ae_realWP_far hD hJ1 hZ μ hS hm hSy
  exact ⟨fun ω => realXi Z ω u, (measurable_pi_apply u).comp (comap_measurable (realXi Z)), hu⟩

end G3Cv
end QuantumZipper

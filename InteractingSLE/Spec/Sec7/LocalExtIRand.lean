/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtILoc
import InteractingSLE.Spec.Coupling.MartMeans2Chart

/-!
# The coupling clause at a random test function

Packet PROVE-LOCEXT-I. At a restart the test functions of the source construction depend on the current force
positions, hence on `ω` (`𝓖_0`-measurably). This file evaluates the coupling clause `MartMeans.IsCouplingCharFun`
(word-agnostic; at a restart it is `isCouplingCharFun_restart_cond`) at a **random** test function measurable for the
stopped σ-algebra:

* **`isCouplingCharFun_condExp_cexp_random`**: for a `𝓖_τ`-measurable random test function `φ`, almost surely on
  `{supp φ ∩ K_τ = ∅}`, `E[e^{i h(φ)} | 𝓖_τ] = exp(i (𝔥_τ, φ ω) − ½ E_τ(φ ω))` (`clauseKernel` at `φ ω`).

The proof is PROVE-CPL-MART2's route with the identity chart: the clause at fixed test functions on the random open set
`ℍ ∖ K_τ`, the local Gaussian laws `exists_gaussLocalLaw`, and the disintegration `condExp_cexp_apply_ae_eq_of_local`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov fwdHull)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace LocalExt

open Coupling Coupling.MartMeans2 Ito

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The coupling clause at a random test function.** If `(h, W, V, ζ)` satisfies the coupling clause for `𝓖`, the
driver starts at `0` and is continuous before `ζ` almost surely, `τ < ζ` is a stopping time and `φ` a random test
function measurable for `𝓖_τ`, then almost surely on `{supp φ(ω) ∩ K_τ(ω) = ∅}`,
`E[e^{i h(φ)} | 𝓖_τ](ω) = exp(i ∫ 𝔥_τ φ(ω) − ½ E_τ(φ(ω)))`. -/
theorem isCouplingCharFun_condExp_cexp_random [IsProbabilityMeasure P]
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) (hh : Measurable h)
    (hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (hlt : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    {φ : Ω → TestOn upperHalfPlaneOpens} (hφ : ∀ z, Measurable[hτ.measurableSpace] fun ω => φ ω z) :
    ∀ᵐ ω ∂P, Disjoint (tsupport (φ ω)) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' (φ ω') : ℂ)) | hτ.measurableSpace] ω =
        clauseKernel κ W (u ω) (φ ω) ((τ ω).untopD 0) ω := by
  have h𝒢 : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  -- the random remaining domains
  set O : Ω → Opens ℂ := fun ω => ⟨interior (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)),
    isOpen_interior⟩ with hOdef
  have hOH : ∀ ω, (O ω : Set ℂ) ⊆ H := fun ω => interior_subset.trans sdiff_subset
  have hgood : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hpath, hlt] with ω h1 h2
    refine ⟨h1.1, h1.2, ?_⟩
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h2)
    rw [← hs] at h2 ⊢
    rw [WithTop.untopD_coe]
    exact h2
  have hOeq : ∀ ω, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω →
      (O ω : Set ℂ) = H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := fun ω hω =>
    (isOpen_H_diff_fwdHull_rpath (w := fun t => W t ω) hω.2.1 hω.2.2).interior_eq
  have hmc : ∀ ω, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω →
      ContinuousOn (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω)) (O ω : Set ℂ) :=
    fun ω hω => by
      have hr := continuousOn_rpath (u := fun t => W t ω) hω.2.1 hω.2.2
      refine (continuousOn_couplingMean κ hr (hu ω).1).mono fun z hz => ?_
      rw [hOeq ω hω] at hz
      exact mem_hullDom hr hz.1 hz.2
  -- the conditional characteristic functional at the random test function
  have hRT := condExp_cexp_apply_ae_eq_of_local (P := P) h𝒢 hh (fun ω => (O ω).isOpen) hOH
    (Ψ := fun ω ψ => Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
      ((τ ω).untopD 0 : ℝ≥0) (u ω) z * ψ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov (O ω : Set ℂ) ψ ψ : ℝ) : ℂ)))
    (by
      filter_upwards [hgood] with ω hω R hR
      have hRH : R ≤ upperHalfPlaneOpens := fun x hx => hOH ω (hR hx)
      obtain ⟨μ, hμP, hμ⟩ := exists_gaussLocalLaw (U := O ω) (hOH ω) (R := R) hR
        (((hmc ω hω).mono hR).locallyIntegrableOn R.isOpen.measurableSet)
      refine ⟨μ, hμP, fun ψ => ?_⟩
      rw [hμ ψ, GFF.coe_testIncl hRH ψ])
    (fun ψ => by
      filter_upwards [hcf τ hτ hlt u hu ψ, hgood] with ω h1 hω hsupp
      have hdisj : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := by
        rw [hOeq ω hω] at hsupp
        exact Set.disjoint_left.2 fun z hz hK => (hsupp hz).2 hK
      rw [h1 hdisj, hOeq ω hω, WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => W t ω)
        hω.2.1 hω.1 hω.2.2 ψ hdisj])
    hφ
  filter_upwards [hRT, hgood] with ω hω hgω hdisj
  have hφO : tsupport (φ ω) ⊆ (O ω : Set ℂ) := by
    rw [hOeq ω hgω]
    exact fun z hz => ⟨(φ ω).tsupport_subset hz, fun hK => Set.disjoint_left.1 hdisj hz hK⟩
  rw [hω hφO, clauseKernel, hOeq ω hgω, WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => W t ω)
    hgω.2.1 hgω.1 hgω.2.2 (φ ω) hdisj]

end LocalExt

end InteractingSLE

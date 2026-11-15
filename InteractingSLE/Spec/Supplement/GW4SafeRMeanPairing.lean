/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanPhase

/-!
# GW4: from a phase-word representative to the canonical tested mean

The analytic input is an actual harmonic representative of the local-set mean
with the finite-word boundary description. Bounded harmonic uniqueness removes
the choice of extension; compact support and integrability justify every
distributional pairing. At time zero the coincident seeds remove the phase
without imposing an arbitrary normalization on its value there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PhaseSel Restart.DomainMarkov

/-- Uniqueness identifies a phase-word extension with the canonical extension
when the phase is zero or the exposed seed interval is empty. -/
theorem eqOn_bheProc_of_phase_zero_or_seed_eq {Ω : Type*} {k : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {R : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ω : Ω} {q : ℝ≥0} {d : ℝ} {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => VL i q ω - R q ω)
        (fun j => VR j q ω - R q ω) d)
      (forceJumpSet (fun i => VL i q ω - R q ω) (fun j => VR j q ω - R q ω)) G)
    (hd : d = 0 ∨ VL 0 q ω = VR 0 q ω) :
    EqOn G (bheProc k ρL ρR R VL VR ω q) H := by
  have heq : phaseData k ρL ρR (fun i => VL i q ω - R q ω)
      (fun j => VR j q ω - R q ω) d =
      forceBoundaryData k ρL ρR (fun i => VL i q ω - R q ω)
        (fun j => VR j q ω - R q ω) := by
    funext x
    rcases hd with hd | hs
    · simp only [phaseData, hd, zero_mul, add_zero]
    · simp only [phaseData, hs, Ioo_self, indicator_empty, mul_zero, add_zero]
  rw [heq] at hG
  exact Impl.eqOn_of_isBoundedHarmonicExtension
    (((Set.finite_range _).union (Set.finite_range _)).insert 0)
    (isBoundedHarmonicExtension_bheProc ω q) hG

/-- The actual harmonic representative and the canonical finite-word
extension give the same distributional pairing on every safe test. -/
theorem pairing_eq_couplingMean_of_phase {Ω : Type*} {k : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {R : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ω : Ω} {q : ℝ≥0} {d : ℝ}
    {B : Set ℂ} {g : DistOn upperHalfPlaneOpens} {w u₀ G : ℂ → ℝ}
    (hR : Continuous fun s : ℝ => R s.toNNReal ω)
    (hshape : H \ B = H \ fwdHull (fun s : ℝ => R s.toNNReal ω) q)
    (hw : InnerProductSpace.HarmonicOnNhd w (H \ B))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hrep : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ B →
      g ψ = ∫ z, w z * ψ z)
    (hmean : EqOn (fun z => w z + u₀ z)
      (couplingMean k (fun s : ℝ => R s.toNNReal ω) q G) (H \ B))
    (hG : IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => VL i q ω - R q ω)
        (fun j => VR j q ω - R q ω) d)
      (forceJumpSet (fun i => VL i q ω - R q ω) (fun j => VR j q ω - R q ω)) G)
    (hd : d = 0 ∨ VL 0 q ω = VR 0 q ω)
    {ψ : TestOn upperHalfPlaneOpens}
    (hψ : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => R s.toNNReal ω) q)) :
    (g + smoothDist upperHalfPlaneOpens u₀) ψ =
      ∫ z, couplingMean k (fun s : ℝ => R s.toNNReal ω) q
        (bheProc k ρL ρR R VL VR ω q) z * ψ z := by
  have hψB : tsupport ψ ⊆ H \ B := by
    rw [hshape]
    exact fun z hz => ⟨Coupling.tsupport_subset_H ψ hz, Set.disjoint_left.1 hψ hz⟩
  have hwc : ContinuousOn w (H \ B) :=
    fun z hz => (hw z hz).1.continuousAt.continuousWithinAt
  have hu₀c : ContinuousOn u₀ H :=
    fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hi₁ := WholeField.integrable_mul_testOn hwc ψ hψB
  have hi₂ := WholeField.integrable_mul_testOn hu₀c ψ (hψB.trans sdiff_subset)
  rw [add_apply, hrep ψ hψB, Coupling.smoothDist_apply_eq hu₀c ψ,
    ← integral_add hi₁ hi₂]
  have hGG := eqOn_bheProc_of_phase_zero_or_seed_eq hG hd
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport ψ
  · have hzB := hψB hz
    have hzO : z ∈ H \ fwdHull (fun s : ℝ => R s.toNNReal ω) q := hshape ▸ hzB
    have hfH := QuantumZipper.FwdHolo.mapsTo_fwdMap hR q.coe_nonneg hzO
    have hm : w z + u₀ z = couplingMean k (fun s : ℝ => R s.toNNReal ω) q G z :=
      hmean hzB
    rw [← add_mul, hm]
    simp only [couplingMean, hGG hfH]
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero, add_zero]

end InteractingSLE.Theorem14.GW4Fix

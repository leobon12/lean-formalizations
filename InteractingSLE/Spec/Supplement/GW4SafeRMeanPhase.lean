/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanShared
import InteractingSLE.Spec.Sec7.PhaseSelAdaptMain

/-!
# GW4: zero phase on an exhaustion by protected stopping times

Aux. 122 is applied with the actual geometric force coordinates. All their
deterministic and adaptedness hypotheses are discharged by the landed Loewner
geometry. The source's seed bounds `(-2, k/2-4]` imply its strict upper bounds.
Only the phase-word martingales and their continuity on the protected caps
remain mathematical inputs. No measurability of the phase is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull swallowTime)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar Sec7 Sec7.PhaseSel Sec7.PocketTraversal

/-- Phase selection for GW4's geometric force word on countably many protected
caps. The lifetime may be zero and need not itself be a stopping time. -/
theorem ae_phase_eq_zero_geom_caps {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    {k : ℝ} (hk : 4 < k) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hrL : -2 < ρL 0) (hrLu : ρL 0 ≤ k / 2 - 4)
    (hrR : -2 < ρR 0) (hrRu : ρR 0 ≤ k / 2 - 4)
    {R : ℝ≥0 → Ω → ℝ} (hR0 : ∀ ω, R 0 ω = 0)
    (hRc : ∀ ω, Continuous (R · ω)) (hRa : StronglyAdapted 𝓕 R)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hxL0 : ∀ ω, xL ω 0 = 0) (hxR0 : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0)
    (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    {V : Ω → ℝ≥0∞} {d : ℝ≥0 → Ω → ℝ} {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0))
    (hcover : ∀ᵐ ω ∂ν, ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω → ∃ n, q ≤ σ n ω)
    (hd : ∀ n (q : ℝ≥0) ω, 0 < q → q ≤ σ n ω → ∃ j : ℤ, d q ω = j * phaseStep k)
    (hmart : ∀ n (U : Ω → ℝ≥0 → ℂ → ℝ), (∀ ω q, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => geomLW R xL i q ω - R q ω)
          (fun j => geomRW R xR j q ω - R q ω) (d q ω))
        (forceJumpSet (fun i => geomLW R xL i q ω - R q ω)
          (fun j => geomRW R xR j q ω - R q ω)) (U ω q)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 ν
        (fun ω => min (swallowTime (wpath R ω) z : WithTop ℝ≥0) (σ n ω))
        (fun q ω => couplingMean k (wpath R ω) q (U ω q) z))
    (hcont : ∀ n (U : Ω → ℝ≥0 → ℂ → ℝ), (∀ ω q, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => geomLW R xL i q ω - R q ω)
          (fun j => geomRW R xR j q ω - R q ω) (d q ω))
        (forceJumpSet (fun i => geomLW R xL i q ω - R q ω)
          (fun j => geomRW R xR j q ω - R q ω)) (U ω q)) →
      ∀ ω (z : ℂ) (T : ℝ), 0 ≤ T → (T.toNNReal : WithTop ℝ≥0) ≤ σ n ω →
        z ∈ H \ fwdHull (wpath R ω) T →
        ContinuousOn (fun q : ℝ => couplingMean k (wpath R ω) q (U ω q.toNNReal) z)
          (Icc 0 T)) :
    ∀ᵐ ω ∂ν, ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V ω → d q ω = 0 := by
  have hLu : ρL 0 < 2 * (k / 2 - 2) - 2 := by linarith only [hk, hrLu]
  have hRu : ρR 0 < 2 * (k / 2 - 2) - 2 := by linarith only [hk, hrRu]
  have hstep : ∀ n, ∀ᵐ ω ∂ν, ∀ q : ℝ≥0, 0 < q →
      (q : WithTop ℝ≥0) ≤ σ n ω → d q ω = 0 := by
    intro n
    refine PhaseSelAdapt.ae_phase_eq_zero_adapt hk hrL hLu hrR hRu
      (VL := geomLW R xL) (VR := geomRW R xR)
      (fun ω => ?_) (fun ω => ?_) (fun ω i => ?_) (fun ω j => ?_)
      hR0 hRc hRa (stronglyAdapted_geomLW hRa hRc hxLm)
      (stronglyAdapted_geomRW hRa hRc hxRm)
      (fun ω q i => geomLW_le hRc xL ω q i) (fun ω q j => le_geomRW hRc xR ω q j)
      (isForcePath_geomLW hRc xL) (isForcePath_geomRW hRc xR)
      (antitone_geomLW hRc xL) (monotone_geomRW hRc xR)
      (fun ω q => antitone_index_geomLW hRc (hxLi ω) q)
      (fun ω q => monotone_index_geomRW hRc (hxRi ω) q)
      (fun ω i j s t hst => geomLW_merge hRc xL ω i j s t hst)
      (fun ω i j s t hst => geomRW_merge hRc xR ω i j s t hst)
      (fun ω q hq i j => geom_sep hRc xL xR ω q hq i j)
      (hσ n) (fun q ω hq hqσ => hd n q ω hq (WithTop.coe_le_coe.1 hqσ))
      (hmart n) (hcont n)
    · rw [geomLW_zero hRc hR0 (le_of_eq (hxL0 ω)), hxL0 ω]
    · rw [geomRW_zero hRc hR0 (le_of_eq (hxR0 ω).symm), hxR0 ω]
    · rw [geomLW_zero hRc hR0 (hxLd ω i).le]
      exact hxLd ω i
    · rw [geomRW_zero hRc hR0 (hxRd ω j).le]
      exact hxRd ω j
  filter_upwards [ae_all_iff.2 hstep, hcover] with ω hzero hcov q hq hqV
  obtain ⟨n, hn⟩ := hcov q hqV
  exact hzero n q hq (WithTop.coe_le_coe.2 hn)

end InteractingSLE.Theorem14.GW4Fix

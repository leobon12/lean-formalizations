/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVField

/-! # The landed tilted kernel and the generating trace for a regularized clock -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H)
open Sec7.PocketTraversal
variable {S : Type u} [MeasurableSpace S] {D : CMIVSetting S} (C : CMIVClock D)

/-- A strictly announcing sequence makes its clock positive almost surely. -/
theorem CMIVClock.ae_pos : ∀ᵐ ω ∂D.Q₀, 0 < C.e ω :=
  (C.announcing.2.2.1 0).mono fun _ h => lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ _) h

include C in
/-- A positive clock forces the seed into the buffer and hence into the chart buffer. -/
theorem CMIVClock.seed_mem : (D.y : ℂ) ∈ D.N := by
  let _ := D.Q₀_prob
  obtain ⟨ω, hpos, he, hg⟩ := ((CMIVClock.ae_pos C).and ((C.ae_exit).and D.trace)).exists
  have hzero : D.Γ ω 0 = D.y := sub_eq_zero.1 hg.1
  have hyV : (D.y : ℂ) ∈ D.V := by
    by_contra hnot
    have hex := RLC.exitTime_eq_zero (V := D.V) (γ := D.Γ ω) (D.U ω) (by rwa [hzero])
    exact hpos.ne' (he.trans hex)
  exact D.closureV_subset (subset_closure hyV)

/-- The per-stop Cameron–Martin theorem gives the reference kernel for this clock. -/
theorem CMIVClock.isCouplingCharFun : Coupling.MartMeans.IsCouplingCharFun
    D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ)
    D.tilt D.driving C.W (geomLW C.W fun _ => flowLineXL D.bR D.JR D.y)
    (geomRW C.W fun _ => flowLineXR D.bR D.JR D.y) C.e D.chartField := by
  classical
  let _ := D.Q₀_prob
  let _ := D.tilt_prob
  intro τ hτ hτe uR huR φ
  have hτe₀ := D.tilt_equivalent.2.ae_le hτe
  have hτU : ∀ᵐ ω ∂D.Q₀, (τ ω : ℝ≥0∞) < D.U ω := by
    filter_upwards [hτe₀, C.ae_exit] with ω hω he
    rw [he] at hω
    exact hω.trans_le (min_le_left _ _)
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData D.κ (flowLineRhoL D.κ D.bR D.JR D.y D.θ)
        (flowLineRhoR D.κ D.bR D.JR D.y D.θ)
        (fun i => geomL (Ito.rpath (C.W · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
          (flowLineXL D.bR D.JR D.y i))
        (fun j => geomR (Ito.rpath (C.W · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
          (flowLineXR D.bR D.JR D.y j)))
      (forceJumpSet
        (fun i => geomL (Ito.rpath (C.W · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
          (flowLineXL D.bR D.JR D.y i))
        (fun j => geomR (Ito.rpath (C.W · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
          (flowLineXR D.bR D.JR D.y j))) (uR ω) := by
    intro ω
    have hr : Bessel.realPath C.W ω = Ito.rpath (C.W · ω) := rfl
    have hl : Bessel.realPath (fun t ω => -C.W t ω) ω =
        (fun s => -Ito.rpath (C.W · ω) s) := rfl
    simpa only [geomLW, geomRW, geomL, geomR, hr, hl, Ito.rpath,
      Real.toNNReal_coe] using huR ω
  exact ae_condExp_shift_eq_ref D.κ_pos D.b_pc D.bR_pc D.O_open D.boundary_eq
    (by simpa using D.N_real D.y C.seed_mem (by simp)) D.θ D.q_extension D.N_open D.N_real
    D.cutoff_eq D.cutoff_harmonic C.seed_mem D.s_bound D.s_limit D.Λ_measurable D.pairing_limit
    D.k_pos D.tilt_prob D.translate D.coupling D.killed hτ hτU (C.pathData τ hτ hτe₀) hu φ

/-- Countably many announced stopping-time identities give agreement before the clock. -/
theorem CMIVClock.ae_agree_before : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0,
    (t : ℝ≥0∞) < C.e ω → C.W t ω = D.W₀ t ω := by
  have hp := fun n => C.pathData (fun ω => (C.announce n ω : WithTop ℝ≥0))
    (C.announcing.1 n) (C.announcing.2.2.1 n)
  filter_upwards [ae_all_iff.2 hp, C.announcing.2.2.2] with ω hω hcover t ht
  obtain ⟨n, hn⟩ := hcover t ht
  obtain ⟨t₂, ht₂, hag⟩ := (hω n).2.2.1
  have h := hag t ⟨t.coe_nonneg, (NNReal.coe_le_coe.2 hn).trans ht₂.le⟩
  simpa only [Ito.rpath, Real.toNNReal_coe] using h

/-- Restrict the original trace and change only its agreeing driver. -/
theorem CMIVClock.ae_generatingTrace : ∀ᵐ ω ∂D.Q₀,
    IsGeneratingTrace (C.W · ω) (C.e ω) (fun t => D.Γ ω t - D.y) := by
  filter_upwards [D.trace, C.ae_exit, C.ae_agree_before] with ω hg he hag
  have hle : C.e ω ≤ D.U ω := he ▸ min_le_left _ _
  exact StoppedK2.isGeneratingTrace_congr (fun t ht => (hag t ht).symm)
    (LP.isGeneratingTrace_mono hg hle)

end InteractingSLE.Restart.FlowStopIdentCMI
